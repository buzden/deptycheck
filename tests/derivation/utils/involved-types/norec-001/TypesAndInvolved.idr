module TypesAndInvolved

import Language.Reflection
import Language.Reflection.Syntax

%default total

export
data X : Type -> Type -> Type where
  XX : Either a b -> X a b

public export
typesAndInvolved : List (Name, List Name)
typesAndInvolved =
  [ ("Bool", ["Prelude.Basics.Bool"])
  , ("Bool", ["Bool"])
  , ("X", ["Prelude.Types.Either", "TypesAndInvolved.X"])
  , ("X", ["X", "Either"])
  ]
