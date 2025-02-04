module ValidateInput

import Deriving.DepTyCheck.Gen

%language ElabReflection

%default total

data X : Fin n -> Fin n -> Type where
  MkX : X {n=10} 5 6

n_is_fully_out : Fuel -> (a, b : _) -> Gen MaybeEmpty $ X a b
n_is_fully_out = deriveGen @{MainCoreDerivator @{LeastEffort}}

n_mentioned_in_wrong_place : Fuel -> (a, b : Fin n) -> Gen MaybeEmpty $ X a b
n_mentioned_in_wrong_place = deriveGen @{MainCoreDerivator @{LeastEffort}}
