module Shared

import public Control.Monad.Either
import public Control.Monad.Writer
import public Control.Monad.Identity
import public Decidable.Equality
import public Data.DPair
import public Data.Vect
import public Data.SnocVect
import public Data.Vect.Quantifiers
import public Derive.Prelude
import public Language.Reflection
import public Language.Reflection.Derive
import public Language.Reflection.Expr
import public Language.Reflection.Logging
import public Language.Reflection.Syntax
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
  Right res <- runEitherT {m=Elab} {e=String} $
    unifyWithCompiler' $ MkUniTask lhsAs lhs rhsAs rhs
  | Left err => fail "Unifier failed with: \{err}"
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
