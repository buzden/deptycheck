module Infra

import DepsCheck

import Deriving.DepTyCheck.Util

import Language.Reflection.Compat

%language ElabReflection

%hide Language.Reflection.Syntax.piAll

ppTy : Type -> Elab Unit
ppTy ty = do
  expr <- quote ty
  (args, ret) <- unPiNamed expr
  deps <- map SortedSet.toList <$> argDeps args
  let expr' = piAll ret $ {name $= Just, piInfo := ExplicitArg} <$> args -- as if all arguments were explicit
  logSugaredTerm "gen.auto.arg-deps" 0 "type        " expr'
  logMsg         "gen.auto.arg-deps" 0 "dependencies: \{show deps}\n"

%runElab for_ listToCheck ppTy
