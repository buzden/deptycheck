module ConsApps

import Language.Reflection
import Language.Reflection.Syntax

%default total

infix 1 @@

(@@) : b -> a -> (a, b)
y @@ x = (x, y)

public export
data X : Type -> Type -> Type where
  XX : Either a b -> X a b

public export
consApps : Elab $ List (List Name, TTImp)
consApps = pure
  [ `(Vect n Nat) @@ ["n", "a"]
  , `(Vect n Nat) @@ ["n"]
  , `(Vect n (Either a b)) @@ ["n", "a", "b"]
  , `(Vect (S n) (Either a b)) @@ ["n", "a", "b"]
  , `(Vect (S n) (Either a a)) @@ ["n", "a", "b"]
  , `(Vect (S $ S n) (Either a (X a a))) @@ ["n", "a", "b"]
  ]
