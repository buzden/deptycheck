module ConsApps

import Language.Reflection
import Language.Reflection.Syntax

%default total

infix 1 @@

(@@) : b -> a -> (a, b)
y @@ x = (x, y)

export
data X : Type -> Type -> Type where
  XX : Either a b -> X a b

public export
consApps : Elab $ List (List Name, TTImp)
consApps = pure
  [ `(a) @@ ["a"]
  , `(Nat) @@ []
  , `(Nat) @@ ["Nat"]
  , `(Vect n a) @@ ["n", "a"]
  , `(Either a a) @@ ["a"]
  , `(X a a) @@ ["a", "b"]
  ]
