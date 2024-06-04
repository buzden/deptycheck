module DerivedGen

import public Deriving.DepTyCheck.Util.Fusion
import public Deriving.DepTyCheck.Gen.Core

%default total

data X : Type -> Type where
    MkX : X n

data Y : Type -> Type where
    MkY : Y n

data W : Type -> Type where
    MkW : W n


data Z : Type where
  MkZ : (m : Type) -> X m -> Y m -> W m -> Z

%language ElabReflection

decl : Maybe FusionDecl
decl = %runElab runFusionList [(`{X}, [`{n}]), (`{Y}, [`{n}]), (`{W}, [`{n}])]

main : IO ()
main = putPretty $ getGen decl
