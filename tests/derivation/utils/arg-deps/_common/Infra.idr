module Infra

import DepsCheck

import Deriving.DepTyCheck.Util.Reflection

import Language.Reflection.Compat

%language ElabReflection

ppTy : Type -> Elab Unit
ppTy ty = do
  expr <- quote ty
  let (args, ret) = unPi expr
  deps <- map SortedSet.toList <$> argDeps args
  let expr' = piAll ret $ {piInfo := ExplicitArg} <$> args -- as if all arguments were explicit
  logSugaredTerm "deptycheck.arg-deps" 0 "type        " expr'
  logMsg         "deptycheck.arg-deps" 0 "dependencies: \{show deps}\n"

%runElab for_ listToCheck ppTy
