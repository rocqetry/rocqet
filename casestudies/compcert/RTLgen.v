From NFPOP Require Import Loader.

From NFPOP Require Import Coqlib.
From NFPOP Require Import Errors.
From NFPOP Require Import Values.
From NFPOP Require Import AST.
From NFPOP Require Import Integers. 
From NFPOP Require Import Floats.
From NFPOP Require Import Memory.
From NFPOP Require Import Globalenvs.
From NFPOP Require Import Smallstep.
From NFPOP Require Import Events.
From NFPOP Require Import Maps.
From NFPOP Require Import Linking.
Require Import NFPOP.CompCert.lib.Ctypes.
From NFPOP Require Import Cop.
From NFPOP Require Import Mon.
Require Import FSets.
Require Import FSetAVL.
Require Import Orders.
Require Import Mergesort.
Require Import Ordered.
Require Import Coq.ZArith.ZArith.
From NFPOP Require Import Prelude.
From NFPOP Require Import Op.

Local Open Scope string_scope.
Local Open Scope list_scope.
Open Scope asm.

Trait Base.



Family Cfam.

FInductive expr : Type :=
| Evar : ident -> expr. (* reading a temporary variable *)

FDefinition label := ident.
FInductive stmt : Type :=
| Sskip: stmt
| Sassign : ident -> expr -> stmt
| Sseq: stmt -> stmt -> stmt                    
| Sreturn: option expr -> stmt
| Slabel: label -> stmt -> stmt
| Sgoto: label -> stmt.
       
FOpaque Definition function : Type := cheat.
FOpaque Definition function_body : function -> stmt := cheat.
FOpaque Definition function_locals : function -> list ident := cheat.
FOpaque Definition function_params : function -> list ident := cheat.       
FOpaque Definition function_sig : function -> signature := cheat.
       
FDefinition fundef := AST.fundef function.
FDefinition program := AST.program fundef unit.

FDefinition funsig := fun (fd: fundef) => 
  match fd with
  | AST.Internal f => function_sig f
  | AST.External ef => ef_sig ef
  end.

FEnd Cfam.

Family CminorSel extends Cfam.
FInductive expr : Type :=
| Econdition : condexpr -> expr -> expr -> expr
| Eop : operation -> exprlist -> expr
| Elet : expr -> expr -> expr
| Eletvar : nat -> expr
with exprlist : Type :=
| Enil: exprlist
| Econs: expr -> exprlist -> exprlist
with condexpr : Type :=
| CEcond : condition -> exprlist -> condexpr
| CEcondition : condexpr -> condexpr -> condexpr -> condexpr
| CElet: expr -> condexpr -> condexpr.
       
FInductive stmt : Type := Sifthenelse: condexpr -> stmt -> stmt -> stmt.

MetaData fn.
Record fn : Type := mkfunction {
   fn_sig: signature;
   fn_params: list ident;
   fn_vars: list ident;
   fn_stackspace: Z;
   fn_body: self__CminorSel.stmt
}.
FEnd fn.

FOverride Definition function := fn.
FOverride Definition function_body := self__CminorSel.fn_body.
FOverride Definition function_locals := self__CminorSel.fn_vars.
FOverride Definition function_params := self__CminorSel.fn_params.
FOverride Definition function_sig := self__CminorSel.fn_sig.

FEnd CminorSel.

Family RTL.
FDefinition node := positive.

From NFPOP Require Import Registers.
      
FInductive instruction: Type :=
| Inop: node -> instruction
| Iop: operation -> list reg -> reg -> node -> instruction          
| Icond: condition -> list reg -> node -> node -> instruction
| Ireturn: option reg -> instruction.

FDefinition code: Type := PTree.t instruction.

MetaData function.
Record function: Type := mkfunction {
  fn_sig: signature;
  fn_params: list reg;
  fn_stacksize: Z;
  fn_code: self__RTL.code;
  fn_entrypoint: self__RTL.node
}.
FEnd function.

FDefinition fundef := AST.fundef function.

FDefinition program := AST.program fundef unit.

FDefinition funsig := fun (fd: fundef) => 
  match fd with
  | AST.Internal f => self__RTL.fn_sig f
  | AST.External ef => ef_sig ef
  end.

FEnd RTL.

From NFPOP Require Import RTLmonad.

(* CminorSel -> RTL *)
Family RTLgen.
Family S extends CminorSel. FEnd S.
Family T extends RTL. FEnd T.

FDefinition res := fun (A : Type) => res A T.instruction.
FDefinition mon := fun (A : Type) => mon A T.instruction.
FDefinition state := state T.instruction.

FLemma init_state_wf:
  forall pc, Plt pc 1%positive \/ (PTree.empty T.instruction)!pc = None.
FProofLemma. intros; right; apply PTree.gempty. Qed. CloseFLemma.

FDefinition init_state : state :=
  mkstate T.instruction 1%positive 1%positive (PTree.empty T.instruction) init_state_wf.

FLemma add_instr_wf:
  forall s i pc,
  let n := s.(st_nextnode T.instruction) in
  Plt pc (Pos.succ n) \/ (PTree.set n i s.(st_code T.instruction))!pc = None.
FProofLemma. apply cheat. Qed. CloseFLemma.

FLemma add_instr_incr:
  forall s i,
  let n := s.(st_nextnode T.instruction) in
  state_incr T.instruction s (mkstate T.instruction s.(st_nextreg T.instruction)
                (Pos.succ n)
                (PTree.set n i s.(st_code T.instruction))
                (add_instr_wf s i)).
FProofLemma. apply cheat. Qed. CloseFLemma.

FDefinition add_instr : T.instruction -> mon T.node := fun (i: T.instruction) =>
  fun s =>
    let n := s.(st_nextnode T.instruction) in
    OK n
       (mkstate T.instruction s.(st_nextreg T.instruction) (Pos.succ n) (PTree.set n i s.(st_code T.instruction))
                (add_instr_wf s i))
       (add_instr_incr s i).

FLemma reserve_instr_wf:
  forall s pc,
    Plt pc (Pos.succ s.(st_nextnode T.instruction)) \/ s.(st_code T.instruction)!pc = None.
FProofLemma. apply cheat. Qed. CloseFLemma.

FLemma reserve_instr_incr:
  forall s,
  let n := s.(st_nextnode T.instruction) in
  state_incr T.instruction s (mkstate T.instruction s.(st_nextreg T.instruction)
                (Pos.succ n)
                s.(st_code T.instruction)
                    (reserve_instr_wf s)).
FProofLemma. apply cheat. Qed. CloseFLemma.

FDefinition reserve_instr : mon T.node :=
  fun (s: state) =>
  let n := s.(st_nextnode T.instruction) in
  OK n
     (mkstate T.instruction s.(st_nextreg T.instruction) (Pos.succ n) s.(st_code T.instruction) (reserve_instr_wf s))
     (reserve_instr_incr s).

FLemma update_instr_wf:
  forall s n i,
  Plt n s.(st_nextnode T.instruction) ->
  forall pc,
    Plt pc s.(st_nextnode T.instruction) \/ (PTree.set n i s.(st_code T.instruction))!pc = None.
FProofLemma. apply cheat. Qed. CloseFLemma.

FLemma update_instr_incr:
  forall s n i (LT: Plt n s.(st_nextnode T.instruction)),
  s.(st_code T.instruction)!n = None ->
  state_incr T.instruction s
             (mkstate T.instruction s.(st_nextreg T.instruction) s.(st_nextnode T.instruction) (PTree.set n i s.(st_code T.instruction))
                     (update_instr_wf s n i LT)).
FProofLemma. apply cheat. Qed. CloseFLemma.

FLemma check_empty_node:
  forall (s: state) (n: T.node), { s.(st_code T.instruction)!n = None } + { True }.
FProofLemma.  intros. case (s.(st_code self__RTLgen.T.instruction)!n); intros. right; auto. left; auto. Qed. CloseFLemma.

FDefinition update_instr : T.node -> T.instruction -> mon unit := fun (n: T.node) (i: T.instruction) => 
  fun s =>
    match plt n s.(st_nextnode T.instruction), check_empty_node s n with
    | left L, left EMPTY =>
        OK tt
           (mkstate T.instruction s.(st_nextreg T.instruction) s.(st_nextnode T.instruction) (PTree.set n i s.(st_code T.instruction))
                    (update_instr_wf s n i L))
           (update_instr_incr s n i L EMPTY)
    | _, _ =>
        Error (Errors.msg "RTLgen.update_instr")
    end.

FLemma new_reg_incr:
  forall s,
  state_incr T.instruction s (mkstate T.instruction (Pos.succ s.(st_nextreg T.instruction))
                        s.(st_nextnode T.instruction) s.(st_code T.instruction) s.(st_wf T.instruction)).
FProofLemma. constructor; simpl. apply Ple_refl. apply Ple_succ. auto. Qed. CloseFLemma.

FDefinition new_reg : mon reg :=
  fun s =>
    OK s.(st_nextreg T.instruction)
       (mkstate T.instruction (Pos.succ s.(st_nextreg T.instruction)) s.(st_nextnode T.instruction) s.(st_code T.instruction) s.(st_wf T.instruction))
       (new_reg_incr s).

FDefinition init_mapping : mapping :=
  mkmapping (PTree.empty reg) nil.

FDefinition add_var : mapping -> ident -> mon (reg * mapping) := fun map name => 
  do r <- new_reg;
     ret (r, mkmapping (PTree.set name r map.(map_vars))
                       map.(map_letvars)).

MetaData add_vars.
Fixpoint add_vars (map: mapping) (names: list ident)
                  {struct names} : self__RTLgen.mon (list reg * mapping) :=
  match names with
  | nil => ret (nil, map)
  | n1 :: nl =>
      do (rl, map1) <- add_vars map nl;
      do (r1, map2) <- self__RTLgen.add_var map1 n1;
      ret (r1 :: rl, map2)
  end.
FEnd add_vars.

FDefinition find_var : mapping -> ident -> mon reg := fun (map: mapping) (name: ident) =>
  match PTree.get name map.(map_vars) with
  | None => error (Errors.MSG "RTLgen: unbound variable " :: Errors.CTX name :: nil)
  | Some r => ret r
  end.

FDefinition add_letvar : mapping -> reg -> mapping := fun (map: mapping) (r: reg) =>
  mkmapping map.(map_vars) (r :: map.(map_letvars)).

FDefinition find_letvar : mapping -> nat -> mon reg := fun (map: mapping) (idx: nat) =>
  match List.nth_error map.(map_letvars) idx with
  | None => error (Errors.msg "RTLgen: unbound let variable")
  | Some r => ret r
  end.

FDefinition add_move : reg -> reg -> T.node -> mon T.node := fun (rs rd: reg) (nd: T.node) => 
  if Reg.eq rs rd
  then ret nd
  else add_instr (T.Iop Op.Omove (rs::nil) rd nd).

FRecursion alloc_reg about S.expr motive (fun (_ : S.expr) => mapping -> mon reg) by _rect.
Case Evar id := (fun map => find_var map id).
Case Eletvar n := (fun map => find_letvar map n).
Case Eop := (fun op args => fun map => new_reg).
Case Econdition c a0 a1 := (fun map => new_reg).
Case Elet a b := (fun map => new_reg).
FEnd alloc_reg.

FRecursion alloc_regs about S.exprlist motive (fun (_ : S.exprlist) => mapping -> mon (list reg)) by _rect.
Case Enil := (fun map => ret nil).
Case Econs a bl :=
(fun map =>
  do r <- alloc_reg a map;
  do rl <- alloc_regs bl map;
  ret (r :: rl)).
FEnd alloc_regs.

FRecursion transl_expr about S.expr motive (fun (_ : S.expr) => mapping -> reg -> T.node -> mon T.node)
  with transl_exprlist about S.exprlist motive (fun (_ : S.exprlist) => mapping -> list reg -> T.node -> mon T.node)
  with transl_condexpr about S.condexpr motive (fun (_ : S.condexpr) => mapping  -> T.node -> T.node -> mon T.node) by _rect.
Case Evar v := (fun map rd nd => do r <- find_var map v; add_move r rd nd).
Case Elet b c :=
(fun map rd nd => 
   do r <- new_reg;
   do nc <- transl_expr c (add_letvar map r) rd nd;
   transl_expr b map r nc).
Case Eop op al :=
(fun map rd nd => 
    do rl <- alloc_regs al map;
    do no <- add_instr (T.Iop op rl rd nd);
    transl_exprlist al map rl no).
Case Econdition a b c :=
(fun map rd nd => 
  do nfalse <- transl_expr c map rd nd;
  do ntrue <- transl_expr b map rd nd;
  transl_condexpr a map ntrue nfalse).
Case Eletvar n := (fun map rd nd => do r <- find_letvar map n; add_move r rd nd).

(* exprlist *)
Case Enil := (fun map rl nd => match rl with nil => ret nd | _ => error (Errors.msg "RTLgen.transl_exprlist") end).
Case Econs b bs :=
(fun map rl nd => 
   match rl with 
   | r :: rs =>  
       do no <- transl_exprlist bs map rs nd; 
       transl_expr b map r no
   | _ => error (Errors.msg "RTLgen.transl_exprlist") end).

(* condexpr *)
Case CEcond c al :=
(fun map ntrue nfalse => 
   do rl <- alloc_regs al map;
   do nt <- add_instr (T.Icond c rl ntrue nfalse);
   transl_exprlist al map rl nt).
Case CEcondition a b c :=
(fun map ntrue nfalse => 
   do nc <- transl_condexpr c map ntrue nfalse;
   do nb <- transl_condexpr b map ntrue nfalse;
   transl_condexpr a map nb nc).
Case CElet b c :=
(fun map ntrue nfalse => 
   do r <- new_reg;
   do nc <- transl_condexpr c (add_letvar map r) ntrue nfalse;
   transl_expr b map r nc).
FEnd transl_expr with transl_exprlist with transl_condexpr.
        
FDefinition labelmap : Type := PTree.t T.node.
        
FRecursion transl_stmt about S.stmt motive (fun (_ : S.stmt) => mapping -> T.node -> list T.node -> labelmap -> T.node -> option reg -> mon T.node) by _rect.
Case Sskip := (fun map nd nexits ngoto nret rret => ret nd).
Case Sassign v b :=
(fun map nd nexits ngoto nret rret => 
   do r <- find_var map v;
   transl_expr b map r nd). 
Case Sseq s1 s2 :=
(fun map nd nexits ngoto nret rret =>  
   do ns <- transl_stmt s2 map nd nexits ngoto nret rret;
   transl_stmt s1 map ns nexits ngoto nret rret).
Case Sifthenelse c strue sfalse :=
(fun map nd nexits ngoto nret rret => 
   (* Don't use "more likely" heuristic *)
   do ntrue <- transl_stmt strue map nd nexits ngoto nret rret;
   do nfalse <- transl_stmt sfalse map nd nexits ngoto nret rret;
   transl_condexpr c map ntrue nfalse).
Case Sreturn opt_a :=
(fun map nd nexits ngoto nret rret => 
  match opt_a, rret with
  | None, _ => ret nret
  | Some a, Some r => transl_expr a map r nret
  | _, _ => error (Errors.msg "RTLgen: type mismatch on return")
  end).
Case Slabel lbl s' :=
(fun map nd nexits ngoto nret rret => 
  do ns <- transl_stmt s' map nd nexits ngoto nret rret;
  match ngoto!lbl with
  | None => error (Errors.msg "RTLgen: unbound label")
  | Some n =>
      do xx <-
        (handle_error (update_instr n (T.Inop ns))
                      (error (Errors.MSG "Multiply-defined label " ::
                              Errors.CTX lbl :: nil)));
      ret ns
  end).
Case Sgoto lbl :=
(fun map nd nexits ngoto nret rret => 
  match ngoto!lbl with
  | None => error (Errors.MSG "Undefined defined label " ::
                  Errors.CTX lbl :: nil)
  | Some n => ret n
  end).
FEnd transl_stmt.

FDefinition alloc_label : S.label -> labelmap -> mon labelmap :=
  fun (lbl: S.label) (map: labelmap) =>
  do n <- reserve_instr;
  ret (PTree.set lbl n map).   

FRecursion reserve_labels about S.stmt
  motive (fun (_ : S.stmt) => labelmap -> mon labelmap) by _rect.
Case Sseq s1 s2 := (fun lm => do lm' <- reserve_labels s2 lm; reserve_labels s1 lm').
Case Sifthenelse e s1 s2 := (fun lm => do lm' <- reserve_labels s2 lm; reserve_labels s1 lm').
Case Slabel lbl s1 := (fun lm => do lm' <- reserve_labels s1 lm; alloc_label lbl lm').
Case Sskip := (fun lm => ret lm).
Case Sassign i e := (fun lm => ret lm).
Case Sreturn a := (fun lm => ret lm).
Case Sgoto lbl := (fun lm => ret lm).
FEnd reserve_labels.

FDefinition ret_reg : signature -> reg -> option reg :=
  fun (sig: signature) (rd: reg) =>
  if rettype_eq sig.(AST.sig_res) AST.Tvoid then None else Some rd.

FDefinition transl_fun : S.function -> mon (T.node * list reg) :=
  fun (f: S.function) => 
  do ngoto <- reserve_labels (S.fn_body f) (PTree.empty T.node);
  do (rparams, map1) <- add_vars init_mapping (S.fn_params f);
  do (rvars, map2) <- add_vars map1 (S.fn_vars f);
  do rret <- new_reg;
  let orret := ret_reg (S.fn_sig f) rret in
  do nret <- add_instr (T.Ireturn orret);
  do nentry <- transl_stmt (S.fn_body f) map2 nret nil ngoto nret orret;
  ret (nentry, rparams).

FDefinition transl_function : S.function -> Errors.res T.function := 
    fun (f: S.function) => 
  match transl_fun f init_state with
  | Error msg => Errors.Error msg
  | OK (nentry, rparams) s i =>
      Errors.OK (T.mkfunction
                   (S.fn_sig f)
                   rparams
                   (S.fn_stackspace f)
                   s.(st_code T.instruction)
                   nentry)
  end.

FDefinition transl_fundef := transf_partial_fundef transl_function.

FDefinition transl_program : S.program -> Errors.res T.program := 
  fun (p: S.program) =>
     transform_partial_program transl_fundef p.                 
FEnd RTLgen.

FEnd Base.

Trait Comp_Loops extends Base.

Family CminorSel.
FInductive stmt : Type :=
| Sblock: stmt -> stmt
| Sexit: nat -> stmt
| Sloop: stmt -> stmt.
FEnd CminorSel.

Trait RTL_jumptable extends RTL.
FInductive instruction: Type :=
| Ijumptable: reg -> list node -> instruction.  
FEnd RTL_jumptable.

Family RTL extends RTL_jumptable.
FEnd RTL.

From NFPOP Require Import RTLmonad.

Trait RTLgen_Sloop extends RTLgen.

Inherit labelmap.

FDefinition transl_exit : list T.node -> nat -> mon T.node := fun nexits n =>
  match nth_error nexits n with
  | None => error (Errors.msg "RTLgen: wrong exit")
  | Some ne => ret ne
  end.

FRecursion transl_stmt.
Case Sloop sbody :=
(fun map nd nexits ngoto nret rret =>
  do n1 <- reserve_instr;
  do n2 <- transl_stmt sbody map n1 nexits ngoto nret rret;
  do xx <- update_instr n1 (T.Inop n2);
  add_instr (T.Inop n2)).
Case Sblock sbody :=
(fun map nd nexits ngoto nret rret =>
   transl_stmt sbody map nd (nd :: nexits) ngoto nret rret).
Case Sexit n := (fun map nd nexits ngoto nret rret => transl_exit nexits n).
FEnd transl_stmt.

FRecursion reserve_labels.
Case Sloop s1 := (fun lm => reserve_labels s1 lm).
Case Sblock s1 := (fun lm => reserve_labels s1 lm).
Case Sexit n := (fun lm => ret lm).
FEnd reserve_labels.

FEnd RTLgen_Sloop.

Family RTLgen extends RTLgen_Sloop.
FEnd RTLgen.

FEnd Comp_Loops.

Trait Comp_Builtin extends Base.

Family CminorSel.
FInductive stmt : Type :=
| Sbuiltin : builtin_res ident -> external_function -> list (builtin_arg expr) -> stmt.
FEnd CminorSel.

Family RTL.
FInductive instruction: Type :=
| Ibuiltin: external_function -> list (builtin_arg reg) -> builtin_res reg -> node -> instruction.
FEnd RTL.

Family RTLgen.
Family S extends CminorSel. FEnd S.
Family T extends RTL. FEnd T.

FDefinition exprlist_of_expr_list : list S.expr -> S.exprlist := fun l =>
  List.fold_right S.Econs S.Enil l.

MetaData params_of_builtin_arg.
Fixpoint params_of_builtin_arg (A: Type) (a: builtin_arg A) : list A :=
  match a with
  | BA x => x :: nil
  | BA_splitlong hi lo => params_of_builtin_arg A hi ++ params_of_builtin_arg A lo
  | BA_addptr a1 a2 => params_of_builtin_arg A a1 ++ params_of_builtin_arg A a2
  | _ => nil
  end.
FEnd params_of_builtin_arg.

FDefinition params_of_builtin_args := fun (A: Type) (al: list (builtin_arg A)) =>
  List.fold_right (fun a l => params_of_builtin_arg A a ++ l) nil al.

MetaData convert_builtin_arg.
Fixpoint convert_builtin_arg {A: Type} (a: builtin_arg self__RTLgen.S.expr) (rl: list A) : builtin_arg A * list A :=
  match a with
  | BA a =>
      match rl with
      | r :: rs => (BA r, rs)
      | nil => (BA_int Int.zero, nil)(* never happens *)
      end
  | BA_int n => (BA_int n, rl)
  | BA_long n => (BA_long n, rl)
  | BA_float n => (BA_float n, rl)
  | BA_single n => (BA_single n, rl)
  | BA_loadstack chunk ofs => (BA_loadstack chunk ofs, rl)
  | BA_addrstack ofs => (BA_addrstack ofs, rl)
  | BA_loadglobal chunk id ofs => (BA_loadglobal chunk id ofs, rl)
  | BA_addrglobal id ofs => (BA_addrglobal id ofs, rl)
  | BA_splitlong hi lo =>
      let (hi', rl1) := convert_builtin_arg hi rl in
      let (lo', rl2) := convert_builtin_arg lo rl1 in
      (BA_splitlong hi' lo', rl2)
  | BA_addptr a1 a2 =>
      let (a1', rl1) := convert_builtin_arg a1 rl in
      let (a2', rl2) := convert_builtin_arg a2 rl1 in
      (BA_addptr a1' a2', rl2)
  end.
FEnd convert_builtin_arg.

MetaData convert_builtin_args.
Fixpoint convert_builtin_args {A: Type} (al: list (builtin_arg self__RTLgen.S.expr)) (rl: list A) : list (builtin_arg A) :=
  match al with
  | nil => nil
  | a1 :: al =>
      let (a1', rl1) := self__RTLgen.convert_builtin_arg a1 rl in
      a1' :: convert_builtin_args al rl1
  end.
FEnd convert_builtin_args.

From NFPOP Require Import RTLmonad.
Inherit labelmap.

FDefinition convert_builtin_res : mapping -> rettype -> builtin_res ident -> self__RTLgen.mon (builtin_res reg)
 := fun map ty r =>                                                                                            
  match r with
  | BR id => do r <- find_var map id; ret (BR r)
  | BR_none => if rettype_eq ty AST.Tvoid then ret BR_none else (do r <- new_reg; ret (BR r))
  | _ => error (Errors.msg "RTLgen: bad builtin_res")
  end.

FRecursion transl_stmt.
Case Sbuiltin r ef args :=
(fun map nd nexits ngoto nret rret =>  
   let al := exprlist_of_expr_list (params_of_builtin_args S.expr args) in
   do rargs <- alloc_regs al map;
   let args' := convert_builtin_args args rargs in
   do res' <- convert_builtin_res map (sig_res (ef_sig ef)) r;
   do n1 <- add_instr (T.Ibuiltin ef args' res' nd);
   transl_exprlist al map rargs n1).
FEnd transl_stmt.

FRecursion reserve_labels.
Case _ := (fun lm => ret lm).
FEnd reserve_labels.

FEnd RTLgen.

FEnd Comp_Builtin.

Trait Comp_Heap extends Base, Comp_Builtin.

Family CminorSel.
(*CminorSel *)
FInductive expr : Type :=
| Eload : memory_chunk -> addressing -> exprlist -> expr.

FInductive stmt : Type :=                                                        
| Sstore : memory_chunk -> addressing -> exprlist -> expr -> stmt.

FEnd CminorSel.

Family RTL.
FInductive instruction: Type :=
| Iload: memory_chunk -> addressing -> list reg -> reg -> node -> instruction
| Istore: memory_chunk -> addressing -> list reg -> reg -> node -> instruction.
FEnd RTL.

Family RTLgen.
Family S extends CminorSel. FEnd S.
Family T extends RTL. FEnd T.

FRecursion alloc_reg.
Case Eload chunkn addr al := (fun map => new_reg).
FEnd alloc_reg.

From NFPOP Require Import RTLmonad.
FRecursion transl_expr
  with transl_exprlist
  with transl_condexpr.
Case Eload chunk addr al := 
  (fun map rd nd =>
     do rl <- alloc_regs al map;
     do no <- add_instr (T.Iload chunk addr rl rd nd);
     transl_exprlist al map rl no).
FEnd transl_expr with transl_exprlist with transl_condexpr.

FRecursion transl_stmt.
Case Sstore chunk addr al b :=
 (fun map nd nexits ngoto nret rret =>
  do rl <- alloc_regs al map;
  do r <- alloc_reg b map;
  do no <- add_instr (T.Istore chunk addr rl r nd);
  do ns <- transl_expr b map r no;
  transl_exprlist al map rl ns).
FEnd transl_stmt.

FRecursion reserve_labels.
Case _ := (fun lm => ret lm).
FEnd reserve_labels.

FEnd RTLgen.

FEnd Comp_Heap.

Trait Comp_Field extends Base, Comp_Heap.

FEnd Comp_Field.

Trait Comp_Call extends Base, Comp_Builtin.

Family CminorSel.
FInductive stmt : Type :=
| Scall : option ident -> signature -> expr + ident -> exprlist -> stmt
| Stailcall: signature -> expr + ident -> exprlist -> stmt.                                                           
FEnd CminorSel.

Family RTL.
FInductive instruction: Type :=
| Icall: signature -> reg + ident -> list reg -> reg -> node -> instruction
| Itailcall: signature -> reg + ident -> list reg -> instruction.

FEnd RTL.

Family RTLgen.
Family S extends CminorSel. FEnd S.
Family T extends RTL. FEnd T.

Inherit alloc_regs.
From NFPOP Require Import RTLmonad.

FDefinition alloc_optreg : mapping -> option ident -> mon reg := fun map dest =>
  match dest with
  | Some id => find_var map id
  | None => new_reg
  end.

FRecursion transl_stmt.
Case Scall optid sig expr_ident cl :=
 (fun map nd nexits ngoto nret rret =>
    match expr_ident with
     | inl b => 
        do rf <- alloc_reg b map;
        do rargs <- alloc_regs cl map;
        do r <- alloc_optreg map optid;
        do n1 <- add_instr (T.Icall sig (inl _ rf) rargs r nd);
        do n2 <- transl_exprlist cl map rargs n1;
        transl_expr b map rf n2
    | (inr id) =>
        do rargs <- alloc_regs cl map;
        do r <- alloc_optreg map optid;
        do n1 <- add_instr (T.Icall sig (inr _ id) rargs r nd);
        transl_exprlist cl map rargs n1
     end).
Case Stailcall sig expr_ident cl :=
(fun map nd nexits ngoto nret rret =>
     match expr_ident with 
     | inl b =>
         do rf <- alloc_reg b map;
         do rargs <- alloc_regs cl map;
         do n1 <- add_instr (T.Itailcall sig (inl _ rf) rargs);
         do n2 <- transl_exprlist cl map rargs n1;
         transl_expr b map rf n2
     | (inr id) =>
         do rargs <- alloc_regs cl map;
         do n1 <- add_instr (T.Itailcall sig (inr _ id) rargs);
         transl_exprlist cl map rargs n1
     end).         
FEnd transl_stmt.

FRecursion reserve_labels.
Case _ := (fun lm => ret lm).
FEnd reserve_labels.

FEnd RTLgen.

FEnd Comp_Call.

(* small extension *)
Trait Comp_Switch extends Comp_Loops.

Trait CminorSel_Switch extends CminorSel.

Inherit expr.

MetaData exitexpr.
Inductive exitexpr : Type :=
  | XEexit: nat -> exitexpr
  | XEjumptable: self__CminorSel_Switch.expr -> list nat -> exitexpr
  | XEcondition: self__CminorSel_Switch.condexpr -> exitexpr -> exitexpr -> exitexpr
  | XElet: self__CminorSel_Switch.expr -> exitexpr -> exitexpr.
FEnd exitexpr.

FInductive stmt : Type := 
| Sswitch: exitexpr -> stmt.
FEnd CminorSel_Switch.

Family CminorSel extends CminorSel_Switch.
FEnd CminorSel.

Trait RTLgen_Switch extends RTLgen.

Inherit labelmap.

From NFPOP Require Import RTLmonad.

Inherit transl_exit.

MetaData transl_jumptable.
Fixpoint transl_jumptable (nexits: list self__RTLgen_Switch.T.node) (tbl: list nat) : self__RTLgen_Switch.mon (list self__RTLgen_Switch.T.node) :=
  match tbl with
  | nil => ret nil
  | t1 :: tl =>
      do n1 <- self__RTLgen_Switch.transl_exit nexits t1;
      do nl <- transl_jumptable nexits tl;
      ret (n1 :: nl)
  end.
FEnd transl_jumptable.

MetaData transl_exitexpr.
Fixpoint transl_exitexpr (map: mapping) (a: self__RTLgen_Switch.S.exitexpr) (nexits: list self__RTLgen_Switch.T.node)
                         {struct a} : self__RTLgen_Switch.mon self__RTLgen_Switch.T.node :=
  match a with
  | self__RTLgen_Switch.S.XEexit n =>
      self__RTLgen_Switch.transl_exit nexits n
  | self__RTLgen_Switch.S.XEjumptable a tbl =>
      do r <- self__RTLgen_Switch.alloc_reg a map;
      do tbl' <- self__RTLgen_Switch.transl_jumptable nexits tbl;
      do n1 <- self__RTLgen_Switch.add_instr (self__RTLgen_Switch.T.Ijumptable r tbl');
         self__RTLgen_Switch.transl_expr a map r n1
  | self__RTLgen_Switch.S.XEcondition a b c =>
      do nc <- transl_exitexpr map c nexits;
      do nb <- transl_exitexpr map b nexits;
         self__RTLgen_Switch.transl_condexpr a map nb nc
  | self__RTLgen_Switch.S.XElet a b =>
      do r <- self__RTLgen_Switch.new_reg;
      do n1 <- transl_exitexpr (self__RTLgen_Switch.add_letvar map r) b nexits;
         self__RTLgen_Switch.transl_expr a map r n1
  end.
FEnd transl_exitexpr.

FRecursion transl_stmt.
Case Sswitch a := (fun map nd nexits ngoto nret rret => transl_exitexpr map a nexits).
FEnd transl_stmt.

FRecursion reserve_labels.
Case Sswitch a := (fun lm => ret lm).
FEnd reserve_labels.
FEnd RTLgen_Switch.

Family RTLgen extends RTLgen_Switch.
FEnd RTLgen.

FEnd Comp_Switch.

Family Comp extends 
  Base,
  Comp_Switch,
  Comp_Loops,
  Comp_Heap, 
  Comp_Field, 
  Comp_Call,
  (* Comp_Float,*)
  Comp_Builtin. 

Family RTLgen.
Final Family S := CminorSel.
Final Family T := RTL.
FEnd RTLgen.

FEnd Comp.

Require Extraction.
Cd "extraction".
Separate Extraction X.C.
Extraction Library X.

Require Extraction.
Extraction Language OCaml.
Extraction "compcert.ml" Base.SimplExpr.transl_function.
