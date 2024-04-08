module ConsApps

import public Data.Vect.Views.Extra

import Language.Reflection.Compat

%default total

rhsConsOf : Name -> Elab $ List (List Name, TTImp)
rhsConsOf n = getInfo' n <&> \tyInfo => tyInfo.cons <&> \con => (con.args <&> name, con.type)

public export
data EqExp : (tyL : Type) -> (tyR : Type) -> tyL -> tyR -> Type where
  ReflExp : (x : a) -> EqExp a a x x

public export
consApps : Elab $ List (List Name, TTImp)
consApps = join <$> sequence
  [ rhsConsOf `{Nat}
  , rhsConsOf `{Vect}
  , rhsConsOf `{Data.Vect.Views.Extra.Split}
  , rhsConsOf `{Builtin.Equal}
  , rhsConsOf `{EqExp}
  ]
