module Test.DepTyCheck.Gen.Emptiness

import Control.Relation
import Control.Order

import public Language.Implicits.IfUnsolved

%default total

--- The data ---

public export
data Emptiness = NonEmpty | CanBeEmptyDynamic | CanBeEmptyStatic

public export
Eq Emptiness where
  NonEmpty == NonEmpty = True
  CanBeEmptyDynamic == CanBeEmptyDynamic = True
  CanBeEmptyStatic == CanBeEmptyStatic = True

  NonEmpty          == CanBeEmptyDynamic = False
  NonEmpty          == CanBeEmptyStatic  = False
  CanBeEmptyDynamic == NonEmpty          = False
  CanBeEmptyDynamic == CanBeEmptyStatic  = False
  CanBeEmptyStatic  == NonEmpty          = False
  CanBeEmptyStatic  == CanBeEmptyDynamic = False

--- Order by strength ---

public export
data NoWeaker : (from, to : Emptiness) -> Type where
  NN : NonEmpty          `NoWeaker` NonEmpty
  ND : NonEmpty          `NoWeaker` CanBeEmptyDynamic
  DD : CanBeEmptyDynamic `NoWeaker` CanBeEmptyDynamic
  AS : em                `NoWeaker` CanBeEmptyStatic

infix 6 `NoWeaker`

noWeaker : (from, to : Emptiness) -> Dec $ from `NoWeaker` to
noWeaker NonEmpty          NonEmpty          = Yes %search
noWeaker CanBeEmptyDynamic NonEmpty          = No $ \case _ impossible
noWeaker CanBeEmptyStatic  NonEmpty          = No $ \case _ impossible
noWeaker NonEmpty          CanBeEmptyDynamic = Yes %search
noWeaker CanBeEmptyDynamic CanBeEmptyDynamic = Yes %search
noWeaker CanBeEmptyStatic  CanBeEmptyDynamic = No $ \case _ impossible
noWeaker _                 CanBeEmptyStatic  = Yes %search

export
Reflexive _ NoWeaker where
  reflexive {x = NonEmpty}          = %search
  reflexive {x = CanBeEmptyStatic}  = %search
  reflexive {x = CanBeEmptyDynamic} = %search

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
  connex {x = NonEmpty}          {y = NonEmpty}          nxy = void $ nxy Refl
  connex {x = CanBeEmptyStatic}  {y = CanBeEmptyStatic}  nxy = void $ nxy Refl
  connex {x = CanBeEmptyDynamic} {y = CanBeEmptyDynamic} nxy = void $ nxy Refl

  connex {x = NonEmpty} {y = CanBeEmptyStatic}  nxy = %search
  connex {x = NonEmpty} {y = CanBeEmptyDynamic} nxy = %search
  connex {x = CanBeEmptyStatic}  {y = NonEmpty} nxy = %search
  connex {x = CanBeEmptyDynamic} {y = NonEmpty} nxy = %search

  connex {x = CanBeEmptyStatic}  {y = CanBeEmptyDynamic} nxy = %search
  connex {x = CanBeEmptyDynamic} {y = CanBeEmptyStatic}  nxy = %search

export
LinearOrder _ NoWeaker where

export
StronglyConnex _ NoWeaker where
  order NonEmpty            NonEmpty            = %search
  order NonEmpty            (CanBeEmptyDynamic) = %search
  order NonEmpty            (CanBeEmptyStatic)  = %search
  order (CanBeEmptyDynamic) NonEmpty            = %search
  order (CanBeEmptyStatic)  NonEmpty            = %search
  order (CanBeEmptyStatic)  (CanBeEmptyStatic)  = %search
  order (CanBeEmptyStatic)  (CanBeEmptyDynamic) = %search
  order (CanBeEmptyDynamic) (CanBeEmptyStatic)  = %search
  order (CanBeEmptyDynamic) (CanBeEmptyDynamic) = %search

public export
CanBeEmpty : Emptiness -> Type
CanBeEmpty em = CanBeEmptyDynamic `NoWeaker` em

export
decCanBeEmpty : (em : _) -> Dec $ CanBeEmpty em
decCanBeEmpty _ = noWeaker _ _

namespace NonEmpty

  export
  extractNE : {em : _} -> Not (CanBeEmpty em) -> em = NonEmpty
  extractNE {em = NonEmpty         } _ = Refl
  extractNE {em = CanBeEmptyDynamic} f = absurd $ f %search
  extractNE {em = CanBeEmptyStatic } f = absurd $ f %search

export
canBeEmpty : (em : _) -> Either (em = NonEmpty) (CanBeEmpty em)
canBeEmpty NonEmpty          = %search
canBeEmpty CanBeEmptyDynamic = %search
canBeEmpty CanBeEmptyStatic  = %search

public export
NotImmediatelyEmpty : Emptiness -> Type
NotImmediatelyEmpty em = em `NoWeaker` CanBeEmptyDynamic

export
relaxAnyCanBeEmpty : CanBeEmpty cbe => em `NoWeaker` CanBeEmptyDynamic -> em `NoWeaker` cbe
relaxAnyCanBeEmpty @{DD} ND = %search
relaxAnyCanBeEmpty @{DD} DD = %search
relaxAnyCanBeEmpty @{AS} ND = %search
relaxAnyCanBeEmpty @{AS} DD = %search

export %hint
rev : {a, b : _} -> Not (a `NoWeaker` b) -> b `NoWeaker` a
rev f = either (absurd . f) id $ order a b

export %hint
nonEmptyIsStrongest : {em : _} -> NonEmpty `NoWeaker` em
nonEmptyIsStrongest {em = NonEmpty}          = NN
nonEmptyIsStrongest {em = CanBeEmptyDynamic} = ND
nonEmptyIsStrongest {em = CanBeEmptyStatic}  = AS

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
  extractNE : {em : _} -> BindToOuter em NonEmpty -> em = NonEmpty
  extractNE {em=NonEmpty         } _       = Refl
  extractNE {em=CanBeEmptyDynamic} $ BTO f = case f %search of _ impossible
  extractNE {em=CanBeEmptyStatic } $ BTO f = case f %search of _ impossible

export
Reflexive _ BindToOuter where
  reflexive {x=NonEmpty}          = %search
  reflexive {x=CanBeEmptyDynamic} = %search
  reflexive {x=CanBeEmptyStatic}  = %search

export %hint
btoRefl : {em : _} -> BindToOuter em em
btoRefl = reflexive

export
bindToOuterRelax : x `BindToOuter` y -> y `NoWeaker` z -> x `BindToOuter` z
bindToOuterRelax f NN = %search
bindToOuterRelax f ND = %search
bindToOuterRelax f DD = %search
bindToOuterRelax f AS = %search
