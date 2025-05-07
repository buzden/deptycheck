module TypesAndInvolved

import Language.Reflection.Compat

%default total

public export
typesAndInvolved : List (Name, Count, List Name)
typesAndInvolved =
  [ ("Nat", M0, ["Nat"])
  , ("List", M0, ["List"])
  , ("Vect", M0, ["Vect", "Nat"])
  , ("Vect", MW, ["Vect"])
  ]
