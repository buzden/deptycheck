module DerivedGen

import public Deriving.DepTyCheck.Util.Fusion
import public Deriving.DepTyCheck.Gen.Core


%default total

data X : Nat -> Type where
    MkX : X 1

data Y : Nat -> Type where
    MkY : Y 2

data Z : Type where
  MkZ : (m : Nat) -> X m -> Y m -> Z

%language ElabReflection

decl : Maybe FusionDecl
decl = %runElab runFusion `{X} [`{n}] `{Y} [`{n}]

main : IO ()
main = putPretty $ getGen decl
