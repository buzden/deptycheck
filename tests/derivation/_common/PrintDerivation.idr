module PrintDerivation

import public Deriving.DepTyCheck.Gen

%language ElabReflection

export covering
printDerived : ConstructorDerivator => (core : DerivatorCore) => Type -> Elab Unit
printDerived ty = do
  ty <- quote ty
  logSugaredTerm "gen.auto.derive.infra" 0 "type" ty
  expr <- deriveGenExpr ty
  expr <- quote expr
  declare `[
    main : IO Unit
    main = do
      putStrLn "LOG gen.auto.derive.infra:0: " -- mimic the original logging behaviour
      putStr $ interpolate ~(expr)
      putStrLn ""
  ]
