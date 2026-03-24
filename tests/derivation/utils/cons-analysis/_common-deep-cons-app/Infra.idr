module Infra

import public ConsApps

import Control.Monad.Identity
import public Control.Monad.Writer

import Deriving.DepTyCheck.Util.DeepConsApp

%language ElabReflection

%hide Data.List.Quantifiers.Right
%hide Data.List.Quantifiers.Left

printDeepConsApp : List Name -> TTImp -> Elab Unit
printDeepConsApp freeNames tyExpr = do
  _ <- getNamesInfoInTypes' tyExpr
  logMsg         "deptycheck.deep-cons-app" 0 ""
  logMsg         "deptycheck.deep-cons-app" 0 "given free names:    \{show freeNames}"
  logSugaredTerm "deptycheck.deep-cons-app" 0 "original expression" tyExpr
  let Right tyExpr = resolveNamesUniquely (fromList freeNames) tyExpr
    | Left (n, alts) => logMsg "deptycheck.deep-cons-app" 0 "fail: name \{n} is not unique, alternatives: \{show alts}"
  logSugaredTerm "deptycheck.deep-cons-app" 0 "resolved expression" tyExpr
  logMsg         "deptycheck.deep-cons-app" 0 "------------------------"
  let ((appliedNames ** bindExprF), []) = runWriter {w=List String} $ analyseDeepConsApp True (fromList freeNames) tyExpr
    | (_, errs) => logMsg "deptycheck.deep-cons-app" 0 "not a (deep) constructor application, reason: \{joinBy "; " errs}"
  let appliedNames = fst <$> appliedNames.asVect
  logMsg         "deptycheck.deep-cons-app" 0 "applied names:   \{show appliedNames}"
  let bindExpr = bindExprF $ \idx => bindVar $ UN $ Basic $ show (index idx appliedNames) ++ show idx
  logSugaredTerm "deptycheck.deep-cons-app" 0 "bind expression" bindExpr

%runElab consApps >>= traverse_ (uncurry printDeepConsApp)
