module PrintDerivation

import public Test.DepTyCheck.Gen.Auto.Entry

%language ElabReflection

export covering
printDerived : DerivatorCore => Type -> Elab Unit
printDerived ty = do
  ty <- quote ty
  logSugaredTerm "gen.auto.derive.infra" 0 "type" ty
  logMsg "gen.auto.derive.infra" 0 "\n\{!(deriveGenExpr ty)}"
