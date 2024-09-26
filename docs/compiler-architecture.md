
## Overview

Our compiler is a modification of CompCert to enable 
a modular and extensible design. We also want to ensure 
we avoid code duplication by reusing similar code in 
within the compiler.

## Vanilla CompCert 

C -> Clight -> Csharpminor -> Cminor -> CminorSel -> RTL -> LTL -> Linear -> Mach -> RISC-V

## Enabling sharing within CompCert

{C, Clight} -> {Csharpminor, Cminor, CminorSel} -> RTL -> LTL -> {Linear, Mach} -> {RISC-V}


### Base compiler
```
family Base { 
	family Cfrontend { }	
	family C extends Cfrontend { } 
	family Clight extends Cfrontend { }
	
	family Cminorvariant {
		Abstract function : Type.
		
		family Sem { 						
			Abstract function_env : Type.			
			Abstract empty_function_env : env.
			
			Inductive state: Type :=
               | State:(* Execution within a function *)
                   forall (f: function)(* currently executing function *)
                          (s: stmt)(* statement under consideration *)
                          (k: cont)(* its continuation -- what to do next *)
                          (sp: function_env)(* current stack pointer *)
                          (e: env)(* current local environment *)
                          (m: mem),(* current memory state *)
                   state
			
			(* Free stack space *)
			Abstract free_function_env : mem -> function_env -> function -> option mem.
			(* Called after free *)
			Abstract update_env : function_env -> function_env.
			
			FInductive step: state -> trace -> state -> Prop :=
				| step_skip_call: forall f k sp e m m',
                    is_call_cont k ->
					free_function_env m sp f = Some m' ->
                    step (State f Sskip k  e m)
                      E0 (Returnstate Vundef k m')
	            | step_return_0: forall f k sp e m m',
                  free_function_env m sp f = Some m' ->
                  step (State f (Sreturn None) k (update_env sp) e m)
                    E0 (Returnstate Vundef (call_cont k) m')
                | step_return_1: forall f a k sp e m v m',
                    eval_expr (update_env sp) e m a v ->
                    free_function_env m sp f = Some m' ->
                    step (State f (Sreturn (Some a)) k (Vptr sp Ptrofs.zero) e m)
                      E0 (Returnstate v (call_cont k) m')
		}
	}
	family CminorTransl { 
		family Source extends Cminorvariant { } 
		family Target extends Cminiorvariant { }
		
		family Sim { 
			(* This will need some abstract things *)
			Indutive match_states : Source.state -> Target.state := ...
		}
	}
	
	family Csharpminor extends Cminorvariant {
	  FOverride Record function : Type := mkfunction {
          fn_sig: signature;
          fn_params: list ident;
          fn_vars: list (ident * Z);
          fn_temps: list ident;
          fn_body: stmt
      }.
		
		family Sem { 
			FOverride Definition function_env := PTree.t (block * Z).
		    FOverride Definition empty_env := PTree.empty (block * Z).
			
			FOverride Definition free_function_env (m : mem) (sp : function_env) (f : function) := 
			   Mem.free_list m (blocks_of_env e)
		    FOverride update_env e := e 
		}
	}
	family Cminor extends Cminorvariant { 
		FOverride Record function : Type := mkfunction {
         fn_sig: signature;
         fn_params: list ident;
         fn_vars: list ident;
         fn_stackspace: Z;
         fn_body: stmt
       }.

	   family Sem { 
           FOverride Definition function_env := val. (* stack pointer *)
		   FOverride Definition empty_env := Z.
		   
		   FOverride Definition free_function_env (m : mem) (sp : function_env) (f : function) := 
		     Mem.free m sp 0 f.(fn_stackspace).
		   FOverride update_env sp := (Vptr sp Ptrofs.zero).
	   }
	}
	family CminorSel extends Cminorvariant { 
		FOverride Record function : Type := mkfunction {
          fn_sig: signature;
          fn_params: list ident;
          fn_vars: list (ident * Z);
          fn_temps: list ident;
          fn_body: stmt
      }.
		
		family Sem { 
			FOverride Definition function_env := PTree.t (block * Z).
		    FOverride Definition empty_env := PTree.empty (block * Z).
			
			FOverride Definition free_function_env (m : mem) (sp : function_env) (f : function) := 
			   Mem.free_list m (blocks_of_env e)
		    FOverride update_env e := e 
		}
	}
	(* Csharpminor -> Cminor *)
	family Cminorgen extends CminorTransl { }
	family StackAllocate extends CminorTransl { }
	family SimplSwitch extends CminorTransl { }
	family ShiftExit extends CminorTransl { }
	
	(* Cminor -> CminorSel *)
	family Selection extends CminorTransl { }
	family SelSwitch extends CminorTransl { } 
	family SelBuiltin extends CminorTransl { }
	family SelBinary extends CminorTransl { }
	family SelUnary extends CminorTransl { }
	family SelLong extends CminorTransl { }
	family SplitLong extends CminorTransl { }
	family SelDiv extends CminorTransl { }
	
	
	family RTL { }
	family LTL { }
	
	family LinearLike {
	   Opaque FDefinition stackslot := ...
	   
       FInductive instruction: Type :=
         | Lgetstack: stackslot -> typ -> mreg -> instruction
         | Lsetstack: stackslot -> typ -> instruction
		 
	 
	   Family Sem { 
		   Opaque FDefinition locset := ...
		   
		   Inductive state: Type :=  
              | Callstate:
                  forall (stack: list stackframe)(* call stack *)
                         (f: block)(* pointer to function to call *)
                         (rs: locset) (* register state *)
                         (m: mem), (* memory state *)
                  state
		   
		   Inductive step: state -> trace -> state -> Prop :=
               | exec_Mgetstack:
                   forall s f sp ofs ty dst c rs m v,
                   load_stack m sp ty ofs = Some v ->
                   step (State s f sp (Mgetstack ofs ty dst :: c) rs m)
                     E0 (State s f sp c (rs#dst <- v) m)
               | exec_Msetstack:
                   forall s f sp src ofs ty c rs m m' rs',
                   store_stack m sp ty ofs (rs src) = Some m' ->
                   rs' = undef_regs (destroyed_by_setstack ty) rs ->
                   step (State s f sp (Msetstack src ofs ty :: c) rs m)
                     E0 (State s f sp c rs' m')
               | exec_Mgetparam:
                   forall s fb f sp ofs ty dst c rs m v rs',
                   Genv.find_funct_ptr ge fb = Some (Internal f) ->
                   load_stack m sp Tptr f.(fn_link_ofs) = Some (parent_sp s) ->
                   load_stack m (parent_sp s) ty ofs = Some v ->
                   rs' = (rs # temp_for_parent_frame <- Vundef # dst <- v) ->
                   step (State s fb sp (Mgetparam ofs ty dst :: c) rs m)
                     E0 (State s fb sp c rs' m)
	   }
	}
	family Linear extends LinearLike { } 
	family Mach extends LinearLike { }
	
	(* RISC-V *)
	family RISCV { 
	   family Base { 
	      (* 	Base Integer Instruction Set, 32-bit *)
	      family RV32I { }
	      (* Base Integer Instruction Set, 64-bit *)
	      family RV64I { }
	   }
	   
	   (* Extensions *)
	   family Ext { 
		   (* Standard Extension for Integer Multiplication and Division *)
           family M { } 
		   (* Standard Extension for Single-Precision Floating-Point *)
		   family F { } 
		   (* Standard Extension for Double-Precision Floating-Point *)
		   family D { } 
	   }
		   
	   family Asm extends Base.RV32I with Base.RV64I, Ext.M, Ext.F, Ext.M { }
	}	
	family Asm extends RISCV.Asm { }	
}
```

### Vector extension
```
family SIMD extends Base { 	
	family RISCV { 
		family Ext { 
			(* Standard Extension for Vector Operations *)
			family V { }
		}
		
		family Asm extends Ext.V { }
	}
}
```


## CompCert features made modular

### RISC-V modular design

## Nanopasses for CompCert

