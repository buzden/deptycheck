module ValidateInput

import Test.DepTyCheck.Gen.Auto

%language ElabReflection

%default total

--- Gen for type with no constructors ---

genVoid : Fuel -> Gen Void
genVoid = deriveGen
