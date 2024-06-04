module DerivedGen

import public Deriving.DepTyCheck.Util.Fusion
import public Deriving.DepTyCheck.Gen.Core

%default total

data X : Type -> Type where
    MkX : X n

data Y : Type -> Type where
    MkY : Y n

data Z : Type -> Type where
    MkZ : Z n

%language ElabReflection

decl : Maybe FusionDecl
decl = %runElab runFusionList [(`{X}, [`{n}]), (`{Y}, [`{n}]), (`{Z}, [`{n}])]

main : IO ()
main = putPretty $ getFusion decl
