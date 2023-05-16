module PrintDerivation

import public Deriving.DepTyCheck.Gen.Entry

%language ElabReflection

export covering
printDerived : DerivatorCore => Type -> Elab $ IO Unit
printDerived ty = do
  ty <- quote ty
  logSugaredTerm "gen.auto.derive.infra" 0 "type" ty
  expr <- deriveGenExpr ty
  pure $ do
    putStrLn "LOG gen.auto.derive.infra:0: " -- mimic the original logging behaviour
    putStr $ interpolate expr
    putStrLn ""
