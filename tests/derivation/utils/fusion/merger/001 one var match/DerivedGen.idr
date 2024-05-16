module DerivedGen

import public Deriving.DepTyCheck.Util.Fusion
import public Deriving.DepTyCheck.Gen.Core

%default total

data X : Type -> Type where
    MkX : X n

data Y : Type -> Type where
    MkY : Y n

%language ElabReflection

decl : List Decl
decl = %runElab runFusion `{X} [`{n}] `{Y} [`{n}]

main : IO ()
main = putPretty $ getFusion decl
