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

noWeaker : (from, to : Emptiness) -> Dec $ from `NoWeaker` to
noWeaker NonEmpty   NonEmpty   = Yes %search
noWeaker MaybeEmpty NonEmpty   = No uninhabited
noWeaker _          MaybeEmpty = Yes %search

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
maybeEmptyIsMinimal : (0 _ : MaybeEmpty `NoWeaker` x) -> x = MaybeEmpty
maybeEmptyIsMinimal nw = irrelevantEq $ maybeEmptyIsMinimal' nw where
  maybeEmptyIsMinimal' : forall x. MaybeEmpty `NoWeaker` x -> x = MaybeEmpty
  maybeEmptyIsMinimal' AS = Refl

export
nonEmptyIsMaximal : (0 _ : x `NoWeaker` NonEmpty) -> x = NonEmpty
nonEmptyIsMaximal nw = irrelevantEq $ nonEmptyIsMaximal' nw where
  nonEmptyIsMaximal' : forall x. x `NoWeaker` NonEmpty -> x = NonEmpty
  nonEmptyIsMaximal' NN = Refl

export %hint
nonEmptyReflexive : {em : _} -> em `NoWeaker` em
nonEmptyReflexive = reflexive
