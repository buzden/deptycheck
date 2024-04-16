module DerivedGen

import public Deriving.DepTyCheck.Util.Fusion
import public Deriving.DepTyCheck.Gen.Core


%default total

data X : Nat -> Type where
    MkX : X 1
  
data Y : Nat -> Type where
    MkY : Y 2

%language ElabReflection

%runElab runFusion `{X} [`{n}] `{Y} [`{n}]
