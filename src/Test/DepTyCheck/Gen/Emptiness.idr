module Test.DepTyCheck.Gen.Emptiness

import Control.Relation
import Control.Order

import public Language.Implicits.IfUnsolved

%default total

--- The data ---

public export
data Emptiness = NonEmpty | MaybeEmpty

public export
Eq Emptiness where
  NonEmpty   == NonEmpty   = True
  MaybeEmpty == MaybeEmpty = True
  NonEmpty   == MaybeEmpty = False
  MaybeEmpty == NonEmpty   = False

--- Order by strength ---

public export
data NoWeaker : (from, to : Emptiness) -> Type where
  NN : NonEmpty `NoWeaker` NonEmpty
  AS : em       `NoWeaker` MaybeEmpty

export infix 6 `NoWeaker`

Uninhabited (MaybeEmpty `NoWeaker` NonEmpty) where
  uninhabited _ impossible

||| Smaller is the value that gives less guarantees
export
Ord Emptiness where
  compare MaybeEmpty NonEmpty   = LT
  compare NonEmpty   MaybeEmpty = GT
  compare _          _          = EQ

export
Reflexive _ NoWeaker where
  reflexive {x=NonEmpty}   = %search
  reflexive {x=MaybeEmpty} = %search

export
transitive' : x `NoWeaker` y -> y `NoWeaker` z -> x `NoWeaker` z
transitive' NN NN = %search
transitive' NN AS = %search
transitive' AS AS = %search

export
Transitive _ NoWeaker where
  transitive = transitive'

export
Antisymmetric _ NoWeaker where
  antisymmetric NN NN = Refl
  antisymmetric AS AS = Refl

export
Preorder _ NoWeaker where

export
PartialOrder _ NoWeaker where

export
Connex _ NoWeaker where
  connex {x=NonEmpty}   {y=NonEmpty}   = %search
  connex {x=MaybeEmpty} {y=MaybeEmpty} = %search
  connex {x=NonEmpty}   {y=MaybeEmpty} = %search
  connex {x=MaybeEmpty} {y=NonEmpty}   = %search

export
LinearOrder _ NoWeaker where

export
StronglyConnex _ NoWeaker where
  order NonEmpty   NonEmpty   = %search
  order NonEmpty   MaybeEmpty = %search
  order MaybeEmpty NonEmpty   = %search
  order MaybeEmpty MaybeEmpty = %search

export %hint
rev : {a, b : _} -> Not (a `NoWeaker` b) -> b `NoWeaker` a
rev f = either (absurd . f) id $ order a b

export %hint
nonEmptyIsStrongest : {em : _} -> NonEmpty `NoWeaker` em
nonEmptyIsStrongest {em=NonEmpty}   = NN
nonEmptyIsStrongest {em=MaybeEmpty} = AS

export
maybeEmptyIsMinimal : (0 _ : MaybeEmpty `NoWeaker` em) -> em = MaybeEmpty
maybeEmptyIsMinimal nw = irrelevantEq $ case nw of AS => Refl

export
nonEmptyIsMaximal : (0 _ : em `NoWeaker` NonEmpty) -> em = NonEmpty
nonEmptyIsMaximal nw = irrelevantEq $ case nw of NN => Refl

export
minMaybeEmptyLeft : (0 em : Emptiness) -> min MaybeEmpty em = MaybeEmpty
minMaybeEmptyLeft em = irrelevantEq $ case em of
  NonEmpty   => Refl
  MaybeEmpty => Refl

export
minMaybeEmptyRight : (0 em : Emptiness) -> min em MaybeEmpty = MaybeEmpty
minMaybeEmptyRight em = irrelevantEq $ case em of
  NonEmpty   => Refl
  MaybeEmpty => Refl

export
minNonEmptyLeft : (0 em : Emptiness) -> min NonEmpty em = em
minNonEmptyLeft em = irrelevantEq $ case em of
  NonEmpty   => Refl
  MaybeEmpty => Refl

export
minNonEmptyRight : (0 em : Emptiness) -> min em NonEmpty = em
minNonEmptyRight em = irrelevantEq $ case em of
  NonEmpty   => Refl
  MaybeEmpty => Refl

export
minSame : (0 em : Emptiness) -> min em em = em
minSame em = irrelevantEq $ case em of
  NonEmpty   => Refl
  MaybeEmpty => Refl

export
minNoWeaker : a1 `NoWeaker` a2 -> b1 `NoWeaker` b2 ->
              min a1 b1 `NoWeaker` min a2 b2
minNoWeaker NN nw = rewrite minNonEmptyLeft b1 in
                    rewrite minNonEmptyLeft b2 in
                    nw
minNoWeaker AS _ = rewrite minMaybeEmptyLeft b2 in AS

export
minNoWeakerLeft : {c : _} -> a `NoWeaker` b -> min a c `NoWeaker` min b c
minNoWeakerLeft nw = minNoWeaker nw reflexive

export
minNoWeakerRight : {c : _} -> a `NoWeaker` b -> min c a `NoWeaker` min c b
minNoWeakerRight nw = minNoWeaker reflexive nw

export
leftNoWeakerMin : {a, b : _} -> a `NoWeaker` min a b
leftNoWeakerMin {a=NonEmpty}   = nonEmptyIsStrongest
leftNoWeakerMin {a=MaybeEmpty} = rewrite minMaybeEmptyLeft b in reflexive

export
rightNoWeakerMin : {a, b : _} -> b `NoWeaker` min a b
rightNoWeakerMin {b=NonEmpty}   = nonEmptyIsStrongest
rightNoWeakerMin {b=MaybeEmpty} = rewrite minMaybeEmptyRight a in reflexive

export %hint
noWeakerReflexive : {em : _} -> em `NoWeaker` em
noWeakerReflexive = reflexive
