module DerivedGen

import public Deriving.DepTyCheck.Util.Fusion
import public Deriving.DepTyCheck.Gen.Core

%default total

data X : Type -> Type -> Type where
    MkX : X n m

data Y : Type -> Type -> Type where
    MkY : Y n m

data W : Type -> Type -> Type where
    MkW : W n m

data Z : Type where
  MkZ : (k : Type) -> (m : Type) -> (n : Type) -> X k m -> Y m n -> W n k -> Z

%language ElabReflection

decl : Maybe FusionDecl
decl = %runElab runFusionList [(`{X}, [`{k}, `{m}]), (`{Y}, [`{m}, `{n}]), (`{W}, [`{n}, `{k}])]

main : IO ()
main = putPretty $ getGen decl `{genZ_ultimate} `{genXYW} `{MkZ}
