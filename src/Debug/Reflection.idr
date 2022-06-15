module Debug.Reflection

import public Language.Reflection
import public Language.Reflection.Pretty
import public Language.Reflection.Syntax

%default total

-----------------------
--- Pretty-printing ---
-----------------------

export
Show TTImp where
  show expr = show $ assert_total {- WTF?? Why do I need it here? -} $ pretty {ann=Unit} expr
