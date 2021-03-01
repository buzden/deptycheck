module Test.DepTyCheck.Gen

import Control.Monad.State

import Data.DPair
import Data.List
import Data.List.Lazier
import Data.List.Lazy
import Data.Stream
import Data.Vect

import Decidable.Equality

import Syntax.WithProof

import public System.Random.Simple

%default total

---------------------------------------------
--- General decisions and magic constants ---
---------------------------------------------

-- All of those can (and even should) be generalized some day.

public export %inline
Seed : Type
Seed = StdGen

-------------------------------------------------
--- General utility functions and definitions ---
-------------------------------------------------

public export
HavingTrue : (a : Type) -> (a -> Bool) -> Type
HavingTrue a p = Subset a \x => p x = True

-------------------------------
--- Definition of the `Gen` ---
-------------------------------

export
data Gen : Type -> Type where
  Uniform : LzList a -> Gen a
  AlternG : LzList (Gen a) -> Gen a
  Raw     : State Seed (LazyList a) -> Gen a

-- TODO To think about arbitrary discrete final probability distribution instead of only uniform.

export
bound : Gen a -> Maybe Nat
bound (Uniform xs) = Just $ length xs
bound (AlternG gs) = sum <$> traverse (assert_total bound) gs
bound (Raw _)      = Nothing

export
chooseAny : Random a => Gen a
chooseAny = Raw $ pure <$> random'

export
choose : Random a => (a, a) -> Gen a
choose bounds = Raw $ pure <$> randomR' bounds

shiftRandomly : RandomGen g => LzList a -> State g (LazyList a)
shiftRandomly xs = case @@ xs.length of
  (Z   ** _)   => pure []
  (S _ ** prf) => (\(ls, rs) => toLazyList $ rs ++ ls) <$> splitAt xs <$> rewrite prf in random'

traverseSt : RandomGen g => LazyList (State g a) -> State g (LazyList a)
traverseSt []      = pure []
traverseSt (x::xs) = ST \s =>
  let ((s1, s2), xx) = mapFst split $ runState s x in
  Id (s1, xx :: evalState s2 (traverseSt xs))

export
unGen : Gen a -> State Seed (LazyList a)
unGen (Raw sf)     = sf
unGen (Uniform xs) = shiftRandomly xs
unGen (AlternG gs) = shiftRandomly gs >>= map join . traverseSt . map (assert_total unGen)

export
Functor Gen where
  map f (Uniform xs) = Uniform $ map f xs
  map f (AlternG gs) = AlternG $ assert_total $ map f <$> gs
  map f (Raw gena)   = Raw $ map f <$> gena

apAsRaw : Gen (a -> b) -> Gen a -> Gen b
apAsRaw generalF generalA = Raw [| unGen generalF <*> unGen generalA |]

export
Applicative Gen where
  pure x = Uniform [x]

  Uniform fs <*> Uniform xs = Uniform $ fs <*> xs
  Uniform fs <*> AlternG gs = AlternG $ [| map fs gs |]
  AlternG gs <*> Uniform xs = AlternG $ [| (\gab, a => flip apply a <$> gab) gs xs |]
  AlternG fs <*> AlternG gs = AlternG $ assert_total $ [| fs <*> gs |]

  rawF@(Raw {}) <*> generalA = apAsRaw rawF generalA
  generalF <*> rawA@(Raw {}) = apAsRaw generalF rawA

export
Alternative Gen where
  empty = Uniform []
  AlternG ls <|> Delay (AlternG rs) = AlternG $ ls ++ rs
  AlternG ls <|> Delay (generalR  ) = AlternG $ ls ++ [generalR]
  generalL   <|> Delay (AlternG rs) = AlternG $ [generalL] ++ rs
  generalL   <|> Delay (generalR  ) = AlternG $ [generalL, generalR]

||| Makes the given `Gen` to act as an independent generator according to the `Alternative` combination.
||| That is, in `independent (independent a <|> independent b)` given `a` and `b` are distributed evenly.
export
independent : Gen a -> Gen a
independent alt@(AlternG xs) = AlternG $ pure $ alt
independent other = other

||| Choose one of the given generators uniformly.
|||
||| All the given generators are treated as independent, i.e. `oneOf [a <|> b, c]` is not the same as `a <|> b <|> c`.
||| In this example case, generator `a <|> b` and generator `c` will have the same probability in the resulting generator,
||| i.e., `oneOf [a <|> b, c]` is equivalent to `independent (a <|> b) <|> independent c`.
|||
||| If you want generators in the list to be treated non-independent, you can use the `choice` function from prelude.
|||
||| The resulting generator is not independent, i.e. `oneOf [a, b, c] <|> oneOf [d, e]` is equivalent to `oneOf [a, b, c, d, e]`.
public export
oneOf : List (Gen a) -> Gen a
oneOf = choiceMap independent

||| Choose one of the given generators with probability proportional to the given value, treating all source generators independently.
|||
||| This function treats given generators in the same way as `oneOf` do, but the resulting generator uses generator
||| from the given list the more frequently, the higher number is has.
||| If generator `g1` has the frequency `n1` and generator `g2` has the frequency `n2`, than `g1` will be used `n1/n2` times
||| more frequently than `g2` in the resulting generator (in case when `g1` and `g2` always generate some value).
|||
||| The resulting generator is not independent, i.e. `frequency [(n1, g1), (n2, g2)] <|> frequency [(n3, g3), (n4, g4)]` is
||| equivalent to `frequency [(n1, g1), (n2, g2), (n3, g3), (n4, g4)]`.
||| Also, `frequency [(n, g), (m, h)] <|> oneOf [u, w]` is equivalent to `frequency [(n, g), (m, h), (1, u), (1, w)]`.
export
frequency : List (Nat, Gen a) -> Gen a
frequency = AlternG . concatMap (\(n, g) => replicate n $ independent g)

||| Choose one of the given generators with probability proportional to the given value, treating all source generators dependently.
|||
||| This function is similar to `frequency` but as of it takes internal alternative combinations inside the given generators level up.
||| That is, unlike the `frequency` function, `frequency' [(n, oneOf [a, b, c]), (m, x)]` is equivalent to
||| `frequency [(n, a), (n, b), (n, c), (m, x)]`
export
frequency' : List (Nat, Gen a) -> Gen a
frequency' = AlternG . concatMap (uncurry replicate)

export
Monad Gen where
  Uniform gs >>= c = AlternG $ c <$> gs
  g >>= c = Raw $ unGen g >>= map join . traverseSt . map (unGen . c)

export
mapMaybe : (a -> Maybe b) -> Gen a -> Gen b
mapMaybe p (Uniform l) = Uniform $ mapMaybe p l
mapMaybe p (AlternG l) = AlternG $ assert_total $ mapMaybe p <$> l
mapMaybe p (Raw sf)    = Raw $ mapMaybe p <$> sf

export
suchThat_withPrf : Gen a -> (p : a -> Bool) -> Gen $ a `HavingTrue` p
suchThat_withPrf g p = mapMaybe lp g where
  lp : a -> Maybe $ a `HavingTrue` p
  lp x = case @@ p x of
    (True ** prf) => Just $ Element x prf
    (False ** _)  => Nothing

infixl 4 `suchThat`

public export
suchThat : Gen a -> (a -> Bool) -> Gen a
suchThat g p = fst <$> suchThat_withPrf g p

export
suchThat_dec : Gen a -> ((x : a) -> Dec (prop x)) -> Gen $ Subset a prop
suchThat_dec g f = mapMaybe d g where
  d : a -> Maybe $ Subset a prop
  d x = case f x of
    Yes p => Just $ Element x p
    No  _ => Nothing

||| Filters the given generator so, that resulting values `x` are solutions of equation `y = f x` for given `f` and `y`.
export
suchThat_invertedEq : DecEq b => Gen a -> (y : b) -> (f : a -> b) -> Gen $ Subset a \x => y = f x
suchThat_invertedEq g y f = g `suchThat_dec` \x => y `decEq` f x

-- TODO to reimplement `variant` to ensure that variant of `Uniform` is left `Uniform`.
export
variant : Nat -> Gen a -> Gen a
variant Z       gen = gen
variant x@(S _) gen = Raw $ modify (index x . iterate (fst . next)) *> unGen gen

export
uniform : LzList a -> Gen a
uniform = Uniform

export
listOf : Gen a -> {default (choose (0, 10)) length : Gen Nat} -> Gen (List a)
listOf g = sequence $ replicate !length g

export
vectOf : Gen a -> {n : Nat} -> Gen (Vect n a)
vectOf g = sequence $ replicate n g
