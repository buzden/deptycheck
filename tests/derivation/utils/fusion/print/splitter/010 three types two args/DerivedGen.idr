module DerivedGen

import public Deriving.DepTyCheck.Util.Fusion
import public Deriving.DepTyCheck.Gen.Core

%default total

data X : Type -> Type -> Type where
    MkX : X n m

data Y : Type -> Type -> Type where
    MkY : Y n m

data Z : Type -> Type -> Type where
    MkZ : Z n m

%language ElabReflection

decl : Maybe FusionDecl
decl = %runElab runFusionList [(`{X}, [`{n}, `{m}]), (`{Y}, [`{m}, `{k}]), (`{Z}, [`{k}, `{n}])]

main : IO ()
main = putPretty $ getSplit decl
