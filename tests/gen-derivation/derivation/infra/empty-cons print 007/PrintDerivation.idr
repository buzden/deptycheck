module PrintDerivation

import public Test.DepTyCheck.Gen.Auto.Entry

%language ElabReflection

export covering
printDerived : DerivatorCore => Type -> Elab Unit
printDerived ty = logMsg "gen.auto.derive.infra" 0 $ "\n" ++ show !(deriveGenExpr !(quote ty))
