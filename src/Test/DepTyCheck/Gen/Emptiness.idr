module Test.DepTyCheck.Gen.Emptiness

import Control.Relation
import Control.Order

import public Language.Implicits.IfUnsolved

%default total

--- The data ---

public export
data Depth = Static | Dynamic

public export
data Emptiness = NonEmpty | CanBeEmpty Depth

--- Order by strength ---

public export
data NoWeaker : (from, to : Emptiness) -> Type where
  NE   : NonEmpty           `NoWeaker` em
  Dyn  : CanBeEmpty Dynamic `NoWeaker` CanBeEmpty Dynamic
  Stat : em                 `NoWeaker` CanBeEmpty Static

infix 6 `NoWeaker`

export
Reflexive _ NoWeaker where
  reflexive {x = NonEmpty}           = %search
  reflexive {x = CanBeEmpty Static}  = %search
  reflexive {x = CanBeEmpty Dynamic} = %search

export
transitive' : x `NoWeaker` y -> y `NoWeaker` z -> x `NoWeaker` z
transitive' NE   _    = %search
transitive' Dyn  NE   impossible
transitive' Dyn  Dyn  = %search
transitive' Dyn  Stat = %search
transitive' _    Stat = %search

export
Transitive _ NoWeaker where
  transitive = transitive'

export
Antisymmetric _ NoWeaker where
  antisymmetric NE   NE   = %search
  antisymmetric Dyn  Dyn  = %search
  antisymmetric Stat Stat = %search

export
Preorder _ NoWeaker where

export
PartialOrder _ NoWeaker where

export
Connex _ NoWeaker where
  connex {x = NonEmpty}           {y = NonEmpty}           nxy = void $ nxy Refl
  connex {x = CanBeEmpty Static}  {y = CanBeEmpty Static}  nxy = void $ nxy Refl
  connex {x = CanBeEmpty Dynamic} {y = CanBeEmpty Dynamic} nxy = void $ nxy Refl

  connex {x = NonEmpty}     {y = CanBeEmpty _} nxy = %search
  connex {x = CanBeEmpty _} {y = NonEmpty}     nxy = %search

  connex {x = CanBeEmpty Static}  {y = CanBeEmpty Dynamic} nxy = %search
  connex {x = CanBeEmpty Dynamic} {y = CanBeEmpty Static}  nxy = %search

export
LinearOrder _ NoWeaker where

export
StronglyConnex _ NoWeaker where
  order NonEmpty             NonEmpty             = %search
  order NonEmpty             (CanBeEmpty _)       = %search
  order (CanBeEmpty _)       NonEmpty             = %search
  order (CanBeEmpty Static)  (CanBeEmpty Static)  = %search
  order (CanBeEmpty Static)  (CanBeEmpty Dynamic) = %search
  order (CanBeEmpty Dynamic) (CanBeEmpty Static)  = %search
  order (CanBeEmpty Dynamic) (CanBeEmpty Dynamic) = %search

weakest : (lem, rem : Emptiness) -> (em ** (lem `NoWeaker` em, rem `NoWeaker` em, Either (lem = em) (rem = em)))
weakest NonEmpty             NonEmpty             = (NonEmpty           ** %search)
weakest NonEmpty             (CanBeEmpty Dynamic) = (CanBeEmpty Dynamic ** %search)
weakest NonEmpty             (CanBeEmpty Static)  = (CanBeEmpty Static  ** %search)
weakest (CanBeEmpty Dynamic) NonEmpty             = (CanBeEmpty Dynamic ** %search)
weakest (CanBeEmpty Static)  NonEmpty             = (CanBeEmpty Static  ** %search)
weakest (CanBeEmpty Static)  (CanBeEmpty _)       = (CanBeEmpty Static  ** %search)
weakest (CanBeEmpty Dynamic) (CanBeEmpty Static)  = (CanBeEmpty Static  ** %search)
weakest (CanBeEmpty Dynamic) (CanBeEmpty Dynamic) = (CanBeEmpty Dynamic ** %search)

--- Relations for particular generator cases ---

public export %inline
CanBeInAlternatives : Emptiness -> Type
CanBeInAlternatives = NoWeaker $ CanBeEmpty Dynamic

public export
data BindToOuter : (emOfBind, outerEm : Emptiness) -> Type where
  BndNE : BindToOuter NonEmpty em
  BndEE : (0 _ : IfUnsolved dp Dynamic) =>
          (0 _ : IfUnsolved idp Dynamic) =>
          BindToOuter (CanBeEmpty idp) (CanBeEmpty dp)

export
bindToOuterRelax : x `BindToOuter` y -> y `NoWeaker` z -> x `BindToOuter` z
bindToOuterRelax BndNE _    = BndNE
bindToOuterRelax BndEE Dyn  = BndEE
bindToOuterRelax BndEE Stat = BndEE
