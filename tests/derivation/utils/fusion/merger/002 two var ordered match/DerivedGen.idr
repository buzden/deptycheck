module DerivedGen

import public Deriving.DepTyCheck.Util.Fusion
import public Deriving.DepTyCheck.Gen.Core


%default total

data X : Type -> Type -> Type where
    MkX : X m n

data Y : Type -> Type -> Type where
    MkY : Y m n

%language ElabReflection


decl : List Decl
decl = %runElab runFusion `{X} [`{m}, `{n}] `{Y} [`{m}, `{n}]

main : IO ()
main = putPretty $ getFusion decl

