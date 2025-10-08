module ConsApps

import public Data.List.Views

import Language.Reflection.Compat
import Language.Reflection.Expr

%default total

rhsConsOf : Name -> Elab $ List (List Name, TTImp)
rhsConsOf n = getInfo' n <&> \tyInfo => tyInfo.cons <&> \con => (con.args <&> argName', con.type)

public export
data EqExp : (tyL : Type) -> (tyR : Type) -> tyL -> tyR -> Type where
  ReflExp : (x : a) -> EqExp a a x x

public export
consApps : Elab $ List (List Name, TTImp)
consApps = join <$> sequence
  [ rhsConsOf `{Nat}
  , rhsConsOf `{Vect}
  , rhsConsOf `{Data.List.Views.Split}
  , rhsConsOf `{Builtin.Equal}
  , rhsConsOf `{EqExp}
  ]
