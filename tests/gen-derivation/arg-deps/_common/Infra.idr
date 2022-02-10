module Infra

import Debug.Reflection

import DepsCheck

import Language.Reflection
import Language.Reflection.Syntax

import Test.DepTyCheck.Gen.Auto.Util

%language ElabReflection

ppTy : Type -> Elab Unit
ppTy ty = do
  expr <- quote ty
  (args, ret) <- unPiNamed expr
  deps <- map SortedSet.toList <$> argDeps args
  let expr' = piAll ret $ {name $= Just, piInfo := ExplicitArg} <$> args -- as if all arguments were explicit
  logSugaredTerm "gen.auto.arg-deps" 0 "type        " expr'
  logMsg         "gen.auto.arg-deps" 0 "dependencies: \{show deps}\n"

%runElab for_ listToCheck ppTy
