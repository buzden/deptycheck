module DerivedGen

import public Test.DepTyCheck.Gen.Auto

%default total

%language ElabReflection

export
checkedGen : Fuel -> Gen Unit
--checkedGen = deriveGen
checkedGen = const empty
