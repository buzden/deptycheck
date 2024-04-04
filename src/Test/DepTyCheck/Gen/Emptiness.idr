module Test.DepTyCheck.Gen.Emptiness

import Control.Relation
import Control.Order

import public Language.Implicits.IfUnsolved

%default total

--- The data ---

public export
data Emptiness = NonEmpty | MaybeEmptyDeep | MaybeEmpty

public export
Eq Emptiness where
  NonEmpty       == NonEmpty       = True
  MaybeEmptyDeep == MaybeEmptyDeep = True
  MaybeEmpty     == MaybeEmpty     = True

  NonEmpty       == MaybeEmptyDeep = False
  NonEmpty       == MaybeEmpty     = False
  MaybeEmptyDeep == NonEmpty       = False
  MaybeEmptyDeep == MaybeEmpty     = False
  MaybeEmpty     == NonEmpty       = False
  MaybeEmpty     == MaybeEmptyDeep = False

--- Order by strength ---

public export
data NoWeaker : (from, to : Emptiness) -> Type where
  NN : NonEmpty       `NoWeaker` NonEmpty
  ND : NonEmpty       `NoWeaker` MaybeEmptyDeep
  DD : MaybeEmptyDeep `NoWeaker` MaybeEmptyDeep
  AS : em             `NoWeaker` MaybeEmpty

export infix 6 `NoWeaker`

noWeaker : (from, to : Emptiness) -> Dec $ from `NoWeaker` to
noWeaker NonEmpty       NonEmpty       = Yes %search
noWeaker MaybeEmptyDeep NonEmpty       = No $ \case _ impossible
noWeaker MaybeEmpty     NonEmpty       = No $ \case _ impossible
noWeaker NonEmpty       MaybeEmptyDeep = Yes %search
noWeaker MaybeEmptyDeep MaybeEmptyDeep = Yes %search
noWeaker MaybeEmpty     MaybeEmptyDeep = No $ \case _ impossible
noWeaker _              MaybeEmpty     = Yes %search

export
Reflexive _ NoWeaker where
  reflexive {x = NonEmpty}       = %search
  reflexive {x = MaybeEmptyDeep} = %search
  reflexive {x = MaybeEmpty}     = %search

export
transitive' : x `NoWeaker` y -> y `NoWeaker` z -> x `NoWeaker` z
transitive' NN NN = %search
transitive' NN ND = %search
transitive' NN AS = %search
transitive' ND DD = %search
transitive' ND AS = %search
transitive' DD DD = %search
transitive' DD AS = %search
transitive' AS AS = %search

export
Transitive _ NoWeaker where
  transitive = transitive'

export
Antisymmetric _ NoWeaker where
  antisymmetric NN NN = Refl
  antisymmetric DD DD = Refl
  antisymmetric AS AS = Refl

export
Preorder _ NoWeaker where

export
PartialOrder _ NoWeaker where

export
Connex _ NoWeaker where
  connex {x = NonEmpty}       {y = NonEmpty}       nxy = void $ nxy Refl
  connex {x = MaybeEmpty}     {y = MaybeEmpty}     nxy = void $ nxy Refl
  connex {x = MaybeEmptyDeep} {y = MaybeEmptyDeep} nxy = void $ nxy Refl

  connex {x = NonEmpty}       {y = MaybeEmpty}     nxy = %search
  connex {x = NonEmpty}       {y = MaybeEmptyDeep} nxy = %search
  connex {x = MaybeEmpty}     {y = NonEmpty}       nxy = %search
  connex {x = MaybeEmptyDeep} {y = NonEmpty}       nxy = %search

  connex {x = MaybeEmpty}     {y = MaybeEmptyDeep} nxy = %search
  connex {x = MaybeEmptyDeep} {y = MaybeEmpty}     nxy = %search

export
LinearOrder _ NoWeaker where

export
StronglyConnex _ NoWeaker where
  order NonEmpty         NonEmpty         = %search
  order NonEmpty         (MaybeEmptyDeep) = %search
  order NonEmpty         (MaybeEmpty)     = %search
  order (MaybeEmptyDeep) NonEmpty         = %search
  order (MaybeEmpty)     NonEmpty         = %search
  order (MaybeEmpty)     (MaybeEmpty)     = %search
  order (MaybeEmpty)     (MaybeEmptyDeep) = %search
  order (MaybeEmptyDeep) (MaybeEmpty)     = %search
  order (MaybeEmptyDeep) (MaybeEmptyDeep) = %search

public export
CanBeEmpty : Emptiness -> Type
CanBeEmpty em = MaybeEmptyDeep `NoWeaker` em

export
decCanBeEmpty : (em : _) -> Dec $ CanBeEmpty em
decCanBeEmpty _ = noWeaker _ _

namespace NonEmpty

  export
  extractNE : (0 _ : Not $ CanBeEmpty em) -> em = NonEmpty
  extractNE ncbe = irrelevantEq $ extractNE' ncbe where
    extractNE' : {em : _} -> Not (CanBeEmpty em) -> em = NonEmpty
    extractNE' {em = NonEmpty      } _ = Refl
    extractNE' {em = MaybeEmptyDeep} f = absurd $ f %search
    extractNE' {em = MaybeEmpty    } f = absurd $ f %search

export
canBeEmpty : (em : _) -> Either (em = NonEmpty) (CanBeEmpty em)
canBeEmpty NonEmpty       = %search
canBeEmpty MaybeEmptyDeep = %search
canBeEmpty MaybeEmpty     = %search

public export
NotImmediatelyEmpty : Emptiness -> Type
NotImmediatelyEmpty em = em `NoWeaker` MaybeEmptyDeep

export
canBeNotImmediatelyEmpty : (em : _) -> Either (em = MaybeEmpty) (NotImmediatelyEmpty em)
canBeNotImmediatelyEmpty NonEmpty       = %search
canBeNotImmediatelyEmpty MaybeEmptyDeep = %search
canBeNotImmediatelyEmpty MaybeEmpty     = %search

export
relaxAnyCanBeEmpty : CanBeEmpty cbe => em `NoWeaker` MaybeEmptyDeep -> em `NoWeaker` cbe
relaxAnyCanBeEmpty @{DD} ND = %search
relaxAnyCanBeEmpty @{DD} DD = %search
relaxAnyCanBeEmpty @{AS} ND = %search
relaxAnyCanBeEmpty @{AS} DD = %search

export %hint
rev : {a, b : _} -> Not (a `NoWeaker` b) -> b `NoWeaker` a
rev f = either (absurd . f) id $ order a b

export %hint
nonEmptyIsStrongest : {em : _} -> NonEmpty `NoWeaker` em
nonEmptyIsStrongest {em = NonEmpty}       = NN
nonEmptyIsStrongest {em = MaybeEmptyDeep} = ND
nonEmptyIsStrongest {em = MaybeEmpty}     = AS

export %hint
nonEmptyReflexive : {em : _} -> em `NoWeaker` em
nonEmptyReflexive = reflexive

--- Relations for particular generator cases ---

-- bind --

public export
data BindToOuter : (emOfBind, outerEm : Emptiness) -> Type where
  BTO : (CanBeEmpty biem -> CanBeEmpty em) -> BindToOuter biem em

export %hint
BindNE : BindToOuter NonEmpty em
BindNE = BTO $ \case _ impossible

namespace BindToOuter

  export
  extractNE : (0 _ : BindToOuter em NonEmpty) -> em = NonEmpty
  extractNE bto = irrelevantEq $ extractNE' bto where
    extractNE' : {em : _} -> BindToOuter em NonEmpty -> em = NonEmpty
    extractNE' {em=NonEmpty      } _       = Refl
    extractNE' {em=MaybeEmptyDeep} $ BTO f = case f %search of _ impossible
    extractNE' {em=MaybeEmpty    } $ BTO f = case f %search of _ impossible

export %hint
btoRefl : BindToOuter em em
btoRefl = BTO id

export
Reflexive _ BindToOuter where
  reflexive = btoRefl

export
bindToOuterRelax : x `BindToOuter` y -> y `NoWeaker` z -> x `BindToOuter` z
bindToOuterRelax f NN = %search
bindToOuterRelax f ND = %search
bindToOuterRelax f DD = %search
bindToOuterRelax f AS = %search
