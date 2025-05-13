module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

g : Fuel -> Gen MaybeEmpty Unit
g = deriveGen
