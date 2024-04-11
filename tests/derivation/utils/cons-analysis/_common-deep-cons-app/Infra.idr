module Infra

import public ConsApps

import Deriving.DepTyCheck.Gen.Core.Util

%language ElabReflection

%hide Data.List.Quantifiers.Right
%hide Data.List.Quantifiers.Left

printDeepConsApp : List Name -> TTImp -> Elab Unit
printDeepConsApp freeNames tyExpr = do
  logMsg         "gen.auto.deep-cons-app" 0 ""
  logMsg         "gen.auto.deep-cons-app" 0 "given free names:    \{show freeNames}"
  logSugaredTerm "gen.auto.deep-cons-app" 0 "original expression" tyExpr
  logMsg         "gen.auto.deep-cons-app" 0 "------------------------"
  Just (appliedNames ** bindExprF) <- analyseDeepConsApp False (fromList freeNames) tyExpr
  | Nothing => logMsg "gen.auto.deep-cons-app" 0 "not a (deep) constructor application"
  logMsg         "gen.auto.deep-cons-app" 0 "applied names:   \{show appliedNames}"
  let bindExpr = bindExprF $ \idx => bindVar $ show (index' appliedNames idx) ++ show idx
  logSugaredTerm "gen.auto.deep-cons-app" 0 "bind expression" bindExpr

%runElab consApps >>= traverse_ (uncurry printDeepConsApp)
