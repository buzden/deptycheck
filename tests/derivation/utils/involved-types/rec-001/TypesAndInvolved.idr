module TypesAndInvolved

import Language.Reflection
import Language.Reflection.Syntax

%default total

public export
typesAndInvolved : List (Name, List Name)
typesAndInvolved =
  [ ("Nat", ["Nat"])
  , ("List", ["List"])
  , ("Vect", ["Vect", "Nat"])
  ]
