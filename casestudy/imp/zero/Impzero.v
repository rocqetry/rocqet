family Impzero {
   family LTL { }

   family RTL { }

   family Linearcommon {
       family Semantics { }
   }

   family Linear extends Linearcommon {
          
   }

   family Mach extends Linearcommon {

   }

   family Processor {
      family Op { }      
   } 

   family Aarch64 extends Processor {
      family Op { }
   }
}


