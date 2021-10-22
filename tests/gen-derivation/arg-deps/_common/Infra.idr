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
  args <- fst <$> unPiNamed expr
  deps <- map SortedSet.toList <$> argDeps args
  logMsg "gen.auto.arg-deps" 0 """
    -
    \n========================================
    \{show expr}
    ----------------
    dependencies: \{show deps}
    ________________________________________
    \n
    """

%runElab for_ listToCheck ppTy
