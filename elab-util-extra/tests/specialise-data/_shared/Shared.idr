module Shared

import public Control.Monad.Either
import public Control.Monad.Writer
import public Control.Monad.Identity
import public Data.DPair
import public Data.Either
import public Data.List
import public Data.List.Quantifiers
import public Data.SnocVect
import public Data.SortedMap.Dependent
import public Data.Vect
import public Data.Vect.Quantifiers
import public Decidable.Decidable
import public Decidable.Equality
import public Derive.Prelude
import public Deriving.SpecialiseData
import public Language.Reflection
import public Language.Reflection.Derive
import public Language.Reflection.Expr
import public Language.Reflection.Logging
import public Language.Reflection.Syntax
import public Language.Reflection.Syntax.Ops
import public Language.Reflection.Types
import public Language.Reflection.Types.Extra
import public Language.Reflection.Unify
import public Language.Reflection.VarSubst

||| Verify that all values in list check to a given type
constructExprs : Type -> List TTImp -> Elab ()
constructExprs ty = traverse_ $ check {expected=ty}

||| Check type-level equality for two values
checkEq : TTImp -> TTImp -> Elab ()
checkEq a b = do
  eqT : Type <- check `(~a = ~b)
  _ : eqT <- check `(Refl)
  pure ()

||| Check runtime equality for two values
checkSoEq : TTImp -> TTImp -> Elab ()
checkSoEq a b = do
  _ : So True <- check `(the (So $ ~a == ~b) Oh)
  pure ()

||| Verify that cast (fromValue) == toValue
verifySingleCast : (fromType, toType : Type) -> (fromValue, toValue : TTImp) -> Elab ()
verifySingleCast fromT toT from to = do
  fromNorm <- normaliseAs fromT from
  resultNorm <- normaliseAs toT `(cast ~fromNorm)
  checkEq to resultNorm

||| Verify that cast (cast specialisedValue) == specialisedValue
verifyDoubleCast :
  (polymorphicType, specialisedType : Type) -> (specialisedValue: TTImp) -> Elab ()
verifyDoubleCast polyTy specTy val = do
  valNorm <- normaliseAs specTy val
  castNorm <- normaliseAs polyTy `(cast ~valNorm)
  cast2Norm <- normaliseAs specTy `(cast ~castNorm)
  checkEq valNorm cast2Norm

||| Run verifySingleCast for each pair of polymorphic and specialised value TTImps
verifySingleCasts' :
  (polymorphicType, specialisedType : Type) ->
  (valuePairs: List (TTImp, TTImp)) ->
  Elab ()
verifySingleCasts' polyTy specTy =
  traverse_ $ \(polyVal, specVal) => do
    verifySingleCast polyTy specTy polyVal specVal
    verifySingleCast specTy polyTy specVal polyVal


||| Run verifySingleCast for each value in list
verifySingleCasts :
  (polymorphicType, specialisedType : Type) -> (values: List TTImp) -> Elab ()
verifySingleCasts polyTy specTy vals = verifySingleCasts' polyTy specTy $ zip vals vals

||| Run verifyDoubleCast for each value in list
verifyDoubleCasts :
  (polymorphicType, specialisedType : Type) -> (values: List TTImp) -> Elab ()
verifyDoubleCasts polyTy monoTy = traverse_ $ verifyDoubleCast polyTy monoTy

||| Verify that DecEq implementations of polymorphicType and specialisedType
||| return the same result for a pair of values
verifyDecEq :
  (polymorphicType, specialisedType : Type) ->
  (specialisedLHS, specialisedRHS : TTImp) ->
  Elab ()
verifyDecEq polyTy specTy lhs rhs = do
  lhsNorm <- normaliseAs specTy lhs
  rhsNorm <- normaliseAs specTy rhs
  lhsCast <- normaliseAs polyTy `(cast ~lhsNorm)
  rhsCast <- normaliseAs polyTy `(cast ~rhsNorm)
  checkSoEq `(isYes $ decEq ~lhsNorm ~rhsNorm)
            `(isYes $ decEq ~lhsCast ~rhsCast)
  pure ()

||| Verify that Eq implementations of polymorphicType and specialisedType
||| return the same result for a pair of values
verifyEq :
  (polymorphicType, specialisedType : Type) ->
  (specialisedLHS, specialisedRHS : TTImp) ->
  Elab ()
verifyEq polyTy specTy lhs rhs = do
  lhsNorm <- normaliseAs specTy lhs
  rhsNorm <- normaliseAs specTy rhs
  lhsCast <- normaliseAs polyTy `(cast ~lhsNorm)
  rhsCast <- normaliseAs polyTy `(cast ~rhsNorm)
  checkSoEq `(~lhsNorm == ~rhsNorm) `(~lhsCast == ~rhsCast)
  checkSoEq `(~lhsNorm /= ~rhsNorm) `(~lhsCast /= ~rhsCast)

||| Verify that Show implementations for polymorphicType and specialisedType
||| return the same result for a given value
verifyShow : (polymorphicType, specialisedType : Type) -> (specialisedValue : TTImp) -> Elab ()
verifyShow polyTy specTy val = do
  valNorm <- normaliseAs specTy val
  valCast <- normaliseAs polyTy `(cast ~valNorm)
  s1 <- normaliseAs String `(show ~valNorm)
  s2 <- normaliseAs String `(show ~valCast)
  checkSoEq s1 s2

||| Verify that FromString implementations for polymorphicType and specialisedType
||| return the same result for a given string
verifyFromString : (polymorphicType, specialisedType : Type) -> String -> Elab ()
verifyFromString polyTy specTy str = do
  str' <- quote str
  polyFS <- normaliseAs polyTy `(fromString ~str')
  specFS <- normaliseAs specTy `(fromString ~str')
  checkSoEq polyFS `(cast ~specFS)

||| Verify that FromString implementations for polymorphicType and specialisedType
||| return the same result for a given string
verifyNum : (polymorphicType, specialisedType : Type) -> Integer -> Elab ()
verifyNum polyTy specTy i = do
  i' <- quote i
  polyFS <- normaliseAs polyTy `(Num.fromInteger ~i')
  specFS <- normaliseAs specTy `(Num.fromInteger ~i')
  checkSoEq polyFS `(cast ~specFS)

||| Run polymorphic and monomorphic `show` for every value in list
verifyShows :
  (polymorphicType, specialisedType : Type) -> (specialisedValues: List TTImp) -> Elab ()
verifyShows polyTy specTy = traverse_ $ verifyShow polyTy specTy

||| Verify correctness of DecEq for every possible pair of values from a given list
verifyDecEqs :
  (polymorphicType, specialisedType : Type) -> (specialisedValues: List TTImp) -> Elab ()
verifyDecEqs polyTy specTy vals = do
  for_ [| MkPair vals vals |] $ uncurry $ verifyDecEq polyTy specTy


||| Verify correctness of Eq for every possible pair of values from a given list
verifyEqs :
  (polymorphicType, specialisedType : Type) -> (specialisedValues: List TTImp) -> Elab ()
verifyEqs polyTy specTy vals = do
  for_ [| MkPair vals vals |] $ uncurry $ verifyEq polyTy specTy


||| Verify that FromString implementations for polymorphicType and specialisedType
||| return the same result for a given list of strings
export
verifyFromStrings : (polymorphicType, specialisedType : Type) -> List String -> Elab ()
verifyFromStrings polyTy specTy = traverse_ $ verifyFromString polyTy specTy

||| Verify that FromString implementations for polymorphicType and specialisedType
||| return the same result for a given list of strings
export
verifyNums : (polymorphicType, specialisedType : Type) -> List Integer -> Elab ()
verifyNums polyTy specTy = traverse_ $ verifyNum polyTy specTy

||| Helper function for interface verification
verifyInterfaces :
  (polymorphicType, specialisedType : Type) ->
  (values : List TTImp) ->
  (interfaces : List (Type -> Type, Type -> Type -> List TTImp -> Elab ())) ->
  Elab ()
verifyInterfaces polyTy specTy vals = traverse_ $ \(iface, verifyInterface) => do
  polyImpl : Maybe _ <- search $ iface polyTy
  specImpl : Maybe _ <- search $ iface specTy
  qInterface <- quote iface
  case (polyImpl, specImpl) of
      (Just _, Just _) => verifyInterface polyTy specTy vals
      (Nothing, Just _) => fail "Specialised type implements \{show qInterface}, while polymorhpic type doesn't"
      (Just _, Nothing) => fail "Polymorphic type implements \{show qInterface}, while specialised type doesn't"
      (Nothing, Nothing) => pure ()

||| Verify specialisation of polymorphicType into specialisedType for a given list of value pairs
||| where the first element is the value of the polymorphic type, and the second - of the monomorphic one
export
verifySpecialisation' :
  (polymorphicType, specialisedType : Type) -> (valuePairs: List (TTImp, TTImp)) -> Elab ()
verifySpecialisation' polyTy specTy pairs = do
  let (polyVals, specVals) = unzip pairs
  constructExprs specTy specVals
  verifySingleCasts' polyTy specTy pairs
  verifyDoubleCasts polyTy specTy specVals
  verifyDoubleCasts specTy polyTy polyVals
  verifyInterfaces polyTy specTy specVals
    [ (DecEq, verifyDecEqs)
    , (Show, verifyShows)
    , (Eq, verifyEqs)
    ]

||| Verify specialisation of polymorphicType into specialisedType for a given list of values
||| if polymorphic and monomorphic constructors share the same set of explicit arguments
export
verifySpecialisation : (polymorphicType, specialisedType : Type) -> List TTImp -> Elab ()
verifySpecialisation polyTy specTy vals = verifySpecialisation' polyTy specTy $ zip vals vals
