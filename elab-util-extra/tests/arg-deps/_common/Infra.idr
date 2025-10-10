module Infra

import DepsCheck

import Language.Reflection.Compat
import Language.Reflection.Expr

%language ElabReflection

unlist : TTImp -> List TTImp
unlist e = do
  let (_, [a, b]) = unApp e
--    | (IVar {}, []) => []
    | _             => []
  a :: unlist b

ppTys : (0 _ : List Type) -> Elab Unit
ppTys tys = do
  tys <- quote tys
  let tys = unlist tys
  for_ tys $ \expr => do
    let (args, ret) = unPi expr
    let deps = map Fin.Set.toList $ argDeps args
    let expr' = piAll ret $ {piInfo := ExplicitArg} <$> args -- as if all arguments were explicit
    logSugaredTerm "deptycheck.arg-deps" 0 "type        " expr'
    logMsg         "deptycheck.arg-deps" 0 "dependencies: \{show deps}\n"

%runElab ppTys listToCheck
