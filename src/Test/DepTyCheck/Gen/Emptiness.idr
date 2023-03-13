module Test.DepTyCheck.Gen.Emptiness

import Control.Relation
import Control.Order

import public Language.Implicits.IfUnsolved

%default total

--- The data ---

public export
data Depth = Dynamic | Static

public export
data Emptiness = NonEmpty | CanBeEmpty Depth

--- Order by strength ---

public export
data NoWeaker : (from, to : Emptiness) -> Type where
  NN : NonEmpty           `NoWeaker` NonEmpty
  ND : NonEmpty           `NoWeaker` CanBeEmpty Dynamic
  DD : CanBeEmpty Dynamic `NoWeaker` CanBeEmpty Dynamic
  AS : em                 `NoWeaker` CanBeEmpty Static

infix 6 `NoWeaker`

export
Reflexive _ NoWeaker where
  reflexive {x = NonEmpty}           = %search
  reflexive {x = CanBeEmpty Static}  = %search
  reflexive {x = CanBeEmpty Dynamic} = %search

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
  connex {x = NonEmpty}           {y = NonEmpty}           nxy = void $ nxy Refl
  connex {x = CanBeEmpty Static}  {y = CanBeEmpty Static}  nxy = void $ nxy Refl
  connex {x = CanBeEmpty Dynamic} {y = CanBeEmpty Dynamic} nxy = void $ nxy Refl

  connex {x = NonEmpty} {y = CanBeEmpty Static}  nxy = %search
  connex {x = NonEmpty} {y = CanBeEmpty Dynamic} nxy = %search
  connex {x = CanBeEmpty Static}  {y = NonEmpty} nxy = %search
  connex {x = CanBeEmpty Dynamic} {y = NonEmpty} nxy = %search

  connex {x = CanBeEmpty Static}  {y = CanBeEmpty Dynamic} nxy = %search
  connex {x = CanBeEmpty Dynamic} {y = CanBeEmpty Static}  nxy = %search

export
LinearOrder _ NoWeaker where

export
StronglyConnex _ NoWeaker where
  order NonEmpty             NonEmpty             = %search
  order NonEmpty             (CanBeEmpty Dynamic) = %search
  order NonEmpty             (CanBeEmpty Static)  = %search
  order (CanBeEmpty Dynamic) NonEmpty             = %search
  order (CanBeEmpty Static)  NonEmpty             = %search
  order (CanBeEmpty Static)  (CanBeEmpty Static)  = %search
  order (CanBeEmpty Static)  (CanBeEmpty Dynamic) = %search
  order (CanBeEmpty Dynamic) (CanBeEmpty Static)  = %search
  order (CanBeEmpty Dynamic) (CanBeEmpty Dynamic) = %search

export
relaxAnyCanBeEmpty : {dp : _} -> em `NoWeaker` CanBeEmpty Dynamic -> em `NoWeaker` CanBeEmpty dp
relaxAnyCanBeEmpty {dp = Dynamic} ND = %search
relaxAnyCanBeEmpty {dp = Dynamic} DD = %search
relaxAnyCanBeEmpty {dp = Static}  ND = %search
relaxAnyCanBeEmpty {dp = Static}  DD = %search

export %hint
nonEmptyIsStrongest : {em : _} -> NonEmpty `NoWeaker` em
nonEmptyIsStrongest {em = NonEmpty}           = NN
nonEmptyIsStrongest {em = CanBeEmpty Dynamic} = ND
nonEmptyIsStrongest {em = CanBeEmpty Static}  = AS

export %hint
nonEmptyReflexive : {em : _} -> em `NoWeaker` em
nonEmptyReflexive = reflexive

--- Relations for particular generator cases ---

-- bind --

public export
data BindToOuter : (emOfBind, outerEm : Emptiness) -> Type where
  BndNE : BindToOuter NonEmpty em
  BndEE : (0 _ : IfUnsolved dp Dynamic) =>
          (0 _ : IfUnsolved idp Dynamic) =>
          BindToOuter (CanBeEmpty idp) (CanBeEmpty dp)

export
Reflexive _ BindToOuter where
  reflexive {x=NonEmpty}           = %search
  reflexive {x=CanBeEmpty Dynamic} = %search
  reflexive {x=CanBeEmpty Static}  = %search

export
bindToOuterRelax : x `BindToOuter` y -> y `NoWeaker` z -> x `BindToOuter` z
bindToOuterRelax BndNE NN = %search
bindToOuterRelax BndNE ND = %search
bindToOuterRelax BndNE DD = %search
bindToOuterRelax BndNE AS = %search
bindToOuterRelax BndEE DD = %search
bindToOuterRelax BndEE AS = %search
