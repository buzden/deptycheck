module Test.DepTyCheck.Gen.Auto

import Data.Either
import Data.List1
import public Data.So
import Data.Validated

import public Language.Reflection
import public Language.Reflection.Types
import public Language.Reflection.Syntax

import public Test.DepTyCheck.Gen

%default total
%language ElabReflection

--- Lists utilities ---

%inline
(.length) : List a -> Nat
xs.length = length xs

-- Not effective but clean
find' : (p : a -> Bool) -> (xs : List a) -> Maybe $ Fin xs.length
find' _ [] = Nothing
find' p (x::xs) = if p x then Just FZ else FS <$> find' p xs

--- Internal generation functions ---

data PresenceAtSignature = NotPresent | ExplicitArg | ImplicitArg

Eq PresenceAtSignature where
  NotPresent  == NotPresent  = True
  ExplicitArg == ExplicitArg = True
  ImplicitArg == ImplicitArg = True
  _ == _ = False

data ExternalGenAccess = ThruImplicit | ThruHint

generateGensFor' : (ty : TypeInfo) ->
                   (givenParams : Vect ty.args.length PresenceAtSignature) ->
                   (externalGens : List (TypeInfo, ExternalGenAccess)) -> -- todo maybe to use smth without constructors info instead of `TypeInfo`.
                   Elab ()

--- External generation interface and aux stuff for that ---

public export
data DatatypeArgPointer
       = Named Name
       | PositionalExplicit Nat

Show DatatypeArgPointer where
  show (Named x) = "named argument `\{show x}`"
  show (PositionalExplicit k) = "explicit argument #\{show k}"

public export
FromString DatatypeArgPointer where
  fromString = Named . fromString

namespace DatatypeArgPointer

  public export
  fromInteger : (x : Integer) -> (0 _ : So (x >= 0)) => DatatypeArgPointer
  fromInteger x = PositionalExplicit $ integerToNat x

Eq Namespace where
  (MkNS xs) == (MkNS ys) = xs == ys

Eq Name where -- I'm not sure that this implementation is correct for my case.
  (UN x)   == (UN y)   = x == y
  (MN x n) == (MN y m) = x == y && n == m
  (NS s n) == (NS p m) = s == p && n == m
  (DN x n) == (DN y m) = x == y && n == m
  (RF x)   == (RF y)   = x == y
  _ == _ = False

findNthExplicit : Nat -> (xs : List NamedArg) -> Maybe $ Fin xs.length
findNthExplicit _     []                              = Nothing
findNthExplicit Z     (MkArg _ ExplicitArg _ _ :: _ ) = Just FZ
findNthExplicit (S k) (MkArg _ ExplicitArg _ _ :: xs) = FS <$> findNthExplicit k xs
findNthExplicit n     (MkArg _ _           _ _ :: xs) = FS <$> findNthExplicit n xs

findArg : {ty : TypeInfo} -> DatatypeArgPointer -> Maybe $ Fin ty.args.length
findArg (Named n)              = find' ((== n) . name) ty.args
findArg (PositionalExplicit k) = findNthExplicit k ty.args

toIndex : {ty : TypeInfo} -> DatatypeArgPointer -> ValidatedL DatatypeArgPointer $ Fin ty.args.length
toIndex p = fromEitherL $ maybeToEither p $ findArg p

Show PresenceAtSignature where
  show NotPresent  = "-"
  show ExplicitArg = "explicit"
  show ImplicitArg = "implicit"

-- This is a straightforward version of `resolveGivens` below, that reduces better.
-- Functionally it stops at the first error instead of analyzing them all.
resolveGivens' : {ty : TypeInfo} -> PresenceAtSignature -> List DatatypeArgPointer -> Elab $ Vect ty.args.length PresenceAtSignature
resolveGivens' _ [] = pure $ replicate ty.args.length NotPresent
resolveGivens' p (curr::rest) = do
  let Just pos = findArg curr
    | Nothing => fail "Could not find \{show curr} of type \{show ty.name} listed in \{show p} givens"
  existing <- resolveGivens' p rest
  pure $ replaceAt pos p existing

resolveGivens : {ty : TypeInfo} -> PresenceAtSignature -> List DatatypeArgPointer -> Elab $ Vect ty.args.length PresenceAtSignature
resolveGivens p = copeErr . map foldResolved . traverse toIndex where

  foldResolved : List (Fin ty.args.length) -> Vect ty.args.length PresenceAtSignature
  foldResolved = foldr (`replaceAt` p) $ replicate ty.args.length NotPresent

  copeErr : ValidatedL DatatypeArgPointer (Vect ty.args.length PresenceAtSignature) -> Elab $ Vect ty.args.length PresenceAtSignature
  copeErr $ Invalid bads = fail "Could not find \{show bads} of type \{show ty.name} listed in \{show p} givens"
  copeErr $ Valid x      = pure x

mergeSignatureDefs : Vect n PresenceAtSignature -> Vect n PresenceAtSignature -> ValidatedL (Fin n) $ Vect n PresenceAtSignature
mergeSignatureDefs [] [] = pure []
mergeSignatureDefs (x::xs) (y::ys) = [| mergeSingle x y :: mapFst (map FS) (mergeSignatureDefs xs ys) |] where
  mergeSingle : PresenceAtSignature -> PresenceAtSignature -> ValidatedL (Fin n) $ PresenceAtSignature
  mergeSingle NotPresent r = pure r
  mergeSingle l NotPresent = pure l
  mergeSingle l r = if l == r then pure l else oneInvalid FZ

signatureDef : (impl, expl : List DatatypeArgPointer) -> {ty : TypeInfo} -> Elab $ Vect ty.args.length PresenceAtSignature
signatureDef impl expl = do
  impl' <- resolveGivens' ImplicitArg impl
  expl' <- resolveGivens' ExplicitArg expl
  let Valid merged = mergeSignatureDefs impl' expl'
    | Invalid badPositions => fail "Argument(s) \{show $ humanReadableArgumentFor ty <$> badPositions} is/are defined as both implicit and explicit given"
  pure merged
  where
    humanReadableArgumentFor : (ty : TypeInfo) -> (pos : Fin ty.args.length) -> String
    humanReadableArgumentFor ty pos =
      case index' ty.args pos of
        MkArg {piInfo=ExplicitArg, name=MN {}, _} => -- machine-generated explicit parameter
                                                     let expArg : NamedArg -> Bool
                                                         expArg $ MkArg {piInfo=ExplicitArg, _} = True
                                                         expArg _ = False
                                                     in show $ PositionalExplicit $ length $ filter expArg $ take (finToNat pos `minus` 1) ty.args
        MkArg {name, _} => show name

||| The entry-point function of automatic generation of `Gen`'s.
|||
||| Consider, you have a `data X (a : A) (b : B n) (c : C) where ...` and
||| you want an autogenerated `Gen` for `X`.
||| Say, you want to have `a` and `c` parameters of `X` to be set by the caller and the `b` parameter to be generated.
||| For this you can call `%runElab generateGensFor "X" [] ["a", "c"]` and
||| you get (besides all) a function with a signature `(a : A) -> (c : C) -> (n ** b : B n ** X a b c)`.
|||
||| You can use positional arguments adderssing instead of named (espesially for unnamed arguments),
||| including mix of positional and named ones.
||| Arguments count from zero and only explicit arguments count.
||| I.e., the following call is equivalent to the one above: `%runElab generateGensFor "X" ["a", 2]`.
|||
||| Say, you want `n` to be set by the caller to.
||| For this, you can use `%runElab generateGensFor "X" ["n"] ["a", "c"]` and
||| the signature of the main generated function becomes `{n : _} -> (a : A) -> (c : C) -> (b : B n ** X a b c)`.
|||
||| Say, you want your generator to be parameterized with some external `Gen`'s.
||| Some of these `Gen`'s are known declared `%hint x : Gen Y`, some of them should go as an `auto` parameters.
||| Consider types `data Y where ...`, `data Z1 where ...` and `data Z2 (b : B n) where ...`.
||| If you want to use `%hint` for `Gen Y` and `Gen`'s for `Z1` and `Z2` to be `auto` parameters, you can use
||| `%runElab generateGensFor "X" ["n"] ["a", "c"] {externalImplicitGens=["Z1", "Z2"]} {externalHintedGens=["Y"]}`
||| to have a function with a signature
||| `Gen Z1 => ({n : _} -> {b : B n} -> Gen (Z2 b)) => {n : _} -> (a : A) -> (c : C) -> (b : B n ** X a b c)`.
||| `%hint _ : Gen Y` from the current scope will be used as soon as a value of type `Y` will be needed for generation.
export
generateGensFor : Name ->
                  (givenImplicitParams : List DatatypeArgPointer) ->
                  (givenExplicitParams : List DatatypeArgPointer) ->
                  {default [] externalImplicitGens : List Name} ->
                  {default [] externalHintedGens : List Name} ->
                  Elab ()
generateGensFor n defImpl defExpl = do
  extImplResolved <- map (, ThruImplicit) <$> for externalImplicitGens getInfo'
  extHintResolved <- map (, ThruHint)     <$> for externalHintedGens   getInfo'
  let extResolved = extImplResolved ++ extHintResolved
  generateGensFor' !(getInfo' n) !(signatureDef defImpl defExpl) extResolved
