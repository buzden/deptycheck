module Debug.Reflection

import Language.Reflection
import Language.Reflection.Pretty
import Language.Reflection.Syntax

%default total

-----------------------
--- Pretty-printing ---
-----------------------

export
Show TTImp where
  show expr = show $ assert_total {- WTF?? Why do I need it here? -} $ pretty {ann=Unit} expr

export
Show Count where
  show M0 = "0"
  show M1 = "1"
  show MW = "+"

export
showVar : Count -> Maybe Name -> (type : TTImp) -> String
showVar count name type = "\{show count} \{maybe "_" show name} : \{show type}"

export
Show (Arg False) where
  show (MkArg count ExplicitArg       name type) = "(\{showVar count name type})"
  show (MkArg count ImplicitArg       name type) = "{\{showVar count name type}}"
  show (MkArg count AutoImplicit      name type) = "{auto \{showVar count name type}}"
  show (MkArg count (DefImplicit def) name type) = "{default \{show def} \{showVar count name type}}"
