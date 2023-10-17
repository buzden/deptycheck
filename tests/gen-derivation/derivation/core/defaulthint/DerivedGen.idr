module DerivedGen

import Deriving.DepTyCheck

%default total

%language ElabReflection

g : Fuel -> Gen Unit
g = deriveGen
