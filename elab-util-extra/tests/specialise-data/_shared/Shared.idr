module Shared

import public Control.Monad.Either
import public Control.Monad.Error.Either
import public Control.Monad.Error.Interface
import public Control.Monad.Writer
import public Control.Monad.Identity
import public Control.Monad.Trans
import public Control.Monad.Reader.Reader
import public Control.Monad.Reader.Interface
import public Control.Monad.Reader.Tuple
import public Control.Monad.State
import public Data.DPair
import public Data.Either
import public Data.List
import public Data.List.Quantifiers
import public Data.Maybe
import public Data.SnocVect
import public Data.SortedSet
import public Data.SortedMap.Dependent
import public Data.Vect
import public Data.Vect.Quantifiers
import public Decidable.Decidable
import public Decidable.Equality
import public Derive.Prelude
import public Deriving.SpecialiseData
import public Language.Mk
import public Language.Reflection
import public Language.Reflection.Compat
import public Language.Reflection.Compat.Constr
import public Language.Reflection.Compat.TypeInfo
import public Language.Reflection.Derive
import public Language.Reflection.Expr
import public Language.Reflection.Logging
import public Language.Reflection.Syntax
import public Language.Reflection.Syntax.Ops
import public Language.Reflection.TTImp
import public Language.Reflection.TT
import public Language.Reflection.Types
import public Language.Reflection.Unify
import public Language.Reflection.VarSubst

||| Verify that all values in list check to a given type
constructExprs : Type -> List TTImp -> Elab ()
constructExprs ty = traverse_ $ check {expected=ty}

||| Verify that all values in list check to a given type
export
verifyInvalidConstructors : (polymorphicType, specialisedType : Type) -> List TTImp -> Elab ()
verifyInvalidConstructors polyTy specTy = traverse_ $ \val => do
  Nothing <- catch $ check {expected=polyTy} val
  | _ => fail "Despite assertion to the contrary, polymorphic type may be instantiated by \{show val}"
  Nothing <- catch $ check {expected=specTy} val
  | _ => fail "Despite assertion to the contrary, specialised type may be instantiated by \{show val}"
  pure ()

export
verifyEmptyType : (polymorphicType, specialisedType : Type) -> Elab ()
verifyEmptyType polyTy specTy = do
  Nothing <- search polyTy
  | v => do
    val <- quote v
    fail "Despite assertion to the contrary, polymorphic type may be instantiated by \{show val}"
  Nothing <- search specTy
  | v => do
    val <- quote v
    fail "Despite assertion to the contrary, specialised type may be instantiated by \{show val}"
  pure ()


||| Check type-level equality for two values
checkEq : TTImp -> TTImp -> Elab ()
checkEq a b = do
  logPoint "verifySpecialisation.checkEq" [] $ show `(~a ~=~ ~b)
  eqT : Type <- check `(~a = ~b)
  logPoint "verifySpecialisation.checkEq" [] $ show !(quote eqT)
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
  (polymorphicType, specialisedType : Type) -> (specialisedValue : TTImp) -> Elab ()
verifyDoubleCast polyTy specTy val = do
  valNorm <- normaliseAs specTy val
  castNorm <- normaliseAs polyTy `(cast ~valNorm)
  cast2Norm <- normaliseAs specTy `(cast ~castNorm)
  checkEq valNorm cast2Norm

||| Run verifySingleCast for each pair of polymorphic and specialised value TTImps
verifySingleCasts' :
  (polymorphicType, specialisedType : Type) ->
  (valuePairs : List (TTImp, TTImp)) ->
  Elab ()
verifySingleCasts' polyTy specTy =
  traverse_ $ \(polyVal, specVal) => do
    verifySingleCast polyTy specTy polyVal specVal
    verifySingleCast specTy polyTy specVal polyVal


||| Run verifySingleCast for each value in list
verifySingleCasts :
  (polymorphicType, specialisedType : Type) -> (values : List TTImp) -> Elab ()
verifySingleCasts polyTy specTy vals = verifySingleCasts' polyTy specTy $ zip vals vals

||| Run verifyDoubleCast for each value in list
verifyDoubleCasts :
  (polymorphicType, specialisedType : Type) -> (values : List TTImp) -> Elab ()
verifyDoubleCasts polyTy specTy = traverse_ $ verifyDoubleCast polyTy specTy

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

||| Run polymorphic and specialised `show` for every value in list
verifyShows :
  (polymorphicType, specialisedType : Type) -> (specialisedValues : List TTImp) -> Elab ()
verifyShows polyTy specTy = traverse_ $ verifyShow polyTy specTy

||| Verify correctness of DecEq for every possible pair of values from a given list
verifyDecEqs :
  (polymorphicType, specialisedType : Type) -> (specialisedValues : List TTImp) -> Elab ()
verifyDecEqs polyTy specTy vals = do
  for_ [| MkPair vals vals |] $ uncurry $ verifyDecEq polyTy specTy


||| Verify correctness of Eq for every possible pair of values from a given list
verifyEqs :
  (polymorphicType, specialisedType : Type) -> (specialisedValues : List TTImp) -> Elab ()
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
      (Just _, Just _) => do
        logPoint "verifySpecialisation" [] "\{show qInterface}: Ok"
        verifyInterface polyTy specTy vals
      (Nothing, Just _) => fail "Specialised type implements \{show qInterface}, while polymorhpic type doesn't"
      (Just _, Nothing) => fail "Polymorphic type implements \{show qInterface}, while specialised type doesn't"
      (Nothing, Nothing) => pure ()

||| Verify specialisation of polymorphicType into specialisedType for a given list of value pairs
||| where the first element is the value of the polymorphic type, and the second - of the specialised one
export
verifySpecialisation' :
  (polymorphicType, specialisedType : Type) -> (valuePairs: List (TTImp, TTImp)) -> Elab ()
verifySpecialisation' polyTy specTy pairs = do
  let (polyVals, specVals) = unzip pairs
  constructExprs specTy specVals
  logPoint "verifySpecialisation" [] "Constructors: Ok"
  verifySingleCasts' polyTy specTy pairs
  logPoint "verifySpecialisation" [] "Single casts: Ok"
  verifyDoubleCasts polyTy specTy specVals
  logPoint "verifySpecialisation" [] "Double casts 1: Ok"
  verifyDoubleCasts specTy polyTy polyVals
  logPoint "verifySpecialisation" [] "Double casts 2: Ok"
  verifyInterfaces polyTy specTy specVals
    [ (DecEq, verifyDecEqs)
    , (Show, verifyShows)
    , (Eq, verifyEqs)
    ]

||| Verify specialisation of polymorphicType into specialisedType for a given list of values
||| if polymorphic and specialised constructors share the same set of explicit arguments
export
verifySpecialisation : (polymorphicType, specialisedType : Type) -> List TTImp -> Elab ()
verifySpecialisation polyTy specTy vals = verifySpecialisation' polyTy specTy $ zip vals vals
