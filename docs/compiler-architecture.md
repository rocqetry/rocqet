
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
	
	family Cminorvariant { } 	
	family Csharpminor extends Cminorvariant { } 
	family Cminor extends Cminorvariant { }
	family CminorSel extends Cminorvariant { }	
	
	family RTL { }
	family LTL { }
	
	family LinearLike { }
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

