module Debug.Reflection

import Language.Reflection
import Language.Reflection.Pretty

%default total

-----------------------
--- Pretty-printing ---
-----------------------

export
Show TTImp where
  show expr = show $ assert_total {- WTF?? Why do I need it here? -} $ pretty {ann=Unit} expr
