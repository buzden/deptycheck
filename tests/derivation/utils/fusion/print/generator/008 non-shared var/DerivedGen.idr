module DerivedGen

import public Deriving.DepTyCheck.Util.Fusion
import public Deriving.DepTyCheck.Gen.Core


%default total

data X : Type -> Type -> Type where
    MkX : X m n

data Y : Type -> Type -> Type where
    MkY : Y m n

data Z : Type where
  MkZ : (k : Type) -> (m : Type) -> (n : Type) -> X k m -> Y m n -> Z

%language ElabReflection

decl : Maybe FusionDecl
decl = %runElab runFusion `{X} [`{k}, `{m}] `{Y} [`{m}, `{n}]

main : IO ()
main = putPretty $ getGen decl
