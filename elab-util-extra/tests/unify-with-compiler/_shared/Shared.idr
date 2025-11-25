module Shared

import public Language.Reflection.Unify

public export
(#:) : Name -> TTImp -> Arg
(#:) a b = MkArg MW ExplicitArg (Just a) b

export
infixl 10 #:

public export
runUnifyWithCompiler : {l,r : Nat} -> Vect l Arg -> TTImp -> Vect r Arg -> TTImp -> Elab UnificationResult
runUnifyWithCompiler lhsAs lhs rhsAs rhs = do
  let Yes lhsPs = all isNamedArg lhsAs
  | _ => do
    failAt !(getFC <$> quote lhsAs) "There are unnamed free variables in left-hand side."
  let Yes rhsPs = all isNamedArg rhsAs
  | _ => do
    failAt !(getFC <$> quote rhsAs) "There are unnamed free variables in right-hand side."
  Right res <- runEitherT {m=Elab} {e=Maybe UnificationError} $
    unifyWithCompiler' $ MkUniTask lhsAs lhs rhsAs rhs
  | Left err => fail "Unifier failed with: \{show err}"
  pure res

public export
runUnifyWithCompiler' : {l,r : Nat} -> Vect l Arg -> TTImp -> Vect r Arg -> TTImp -> Elab ()
runUnifyWithCompiler' lhsAs lhs rhsAs rhs =
  runUnifyWithCompiler lhsAs lhs rhsAs rhs *> pure ()

public export
withUnify' : {l,r : Nat} -> Vect l Arg -> TTImp -> Vect r Arg -> TTImp -> (UnificationResult -> Elab t) -> Elab t
withUnify' lhsAs lhs rhsAs rhs f =
  runUnifyWithCompiler lhsAs lhs rhsAs rhs >>= f

public export
showUnify' : {l,r : Nat} -> Vect l Arg -> TTImp -> Vect r Arg -> TTImp -> Elab ()
showUnify' lhsAs lhs rhsAs rhs = withUnify' lhsAs lhs rhsAs rhs $ logMsg "" 0 . show

public export
assertFV : UnificationResult -> Name -> TTImp -> Elab ()
assertFV ur n t = do
  let Just res = lookup n ur.fullResult
  | _ => fail "Free variable \{show n} doesn't have a value"
  when (res /= t) $
    fail "Free variable \{show n}'s value is \{show res} instead of \{show t}"

public export
assertFV' : UnificationResult -> Name -> Type -> TTImp -> Elab ()
assertFV' ur n ty expr = do
  let Just res = lookup n ur.fullResult
  | _ => fail "Free variable \{show n} doesn't have a value"
  expr <- normaliseAs ty expr
  when (res /= expr) $
    fail "Free variable \{show n}'s value is \{show res} instead of \{show expr}"

public export
assertOrder : UnificationResult -> List Name -> Elab ()
assertOrder ur expected = do
  let actualNames = name . flip index ur.uniDg.fvData <$> ur.order
  when (actualNames /= expected) $
    fail "Free variable order is \{show actualNames} instead of \{show expected}"
