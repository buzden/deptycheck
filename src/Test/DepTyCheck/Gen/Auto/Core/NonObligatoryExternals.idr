module Test.DepTyCheck.Gen.Auto.Core.NonObligatoryExternals

import public Test.DepTyCheck.Gen.Auto.Core

%default total

export
ConstructorDerivator where
  canonicConsBody sig name con = do
    let fuelArg = "fuel_cons_arg"
    pure [ canonicDefaultLHS sig name fuelArg .= ?cons_body_rhs ]
