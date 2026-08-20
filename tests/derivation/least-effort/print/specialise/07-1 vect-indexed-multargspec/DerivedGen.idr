module DerivedGen

import Deriving.DepTyCheck.Gen

import public Data.Fin
import Data.Fuel
import Data.String
import Data.Vect
import public Data.Vect.AtIndex

import Decidable.Equality

import Deriving.DepTyCheck.Gen

%language ElabReflection

%default total

%language ElabReflection

public export
Regs : Nat -> Type
Regs n = Vect n $ Maybe Bool

public export
RegIsType : Fin r -> Bool -> Regs r -> Type
RegIsType fn t rs = AtIndex fn rs (Just t)

public export
data SimpleExpr : Regs r -> Bool -> Type where
  Read    : (idx : Fin r) -> RegIsType idx t regs => SimpleExpr regs t

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (r : Nat) -> (t : Bool) -> Gen MaybeEmpty (a : Regs r ** SimpleExpr a t)
