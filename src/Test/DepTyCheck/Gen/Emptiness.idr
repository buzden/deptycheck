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
  Refl : em       `NoWeaker` em
  NE   : NonEmpty `NoWeaker` em
  Stat : em       `NoWeaker` CanBeEmpty Static

infix 6 `NoWeaker`

export
Reflexive _ NoWeaker where
  reflexive = Refl

export
Transitive _ NoWeaker where
  transitive Refl Refl = Refl
  transitive Refl NE   = NE
  transitive Refl Stat = Stat
  transitive NE   _ = NE
  transitive Stat Refl = Stat
  transitive Stat NE   impossible
  transitive Stat Stat = Stat

export
Antisymmetric _ NoWeaker where
--  antisymmetric Refl Refl = Refl
  antisymmetric Refl Refl = Refl
  antisymmetric Refl NE   = Refl
  antisymmetric Refl Stat = Refl
  antisymmetric NE   Refl = Refl
  antisymmetric NE   NE   = Refl
  antisymmetric Stat Refl = Refl
  antisymmetric Stat Stat = Refl

export
Preorder _ NoWeaker where

export
PartialOrder _ NoWeaker where

export
Connex _ NoWeaker where
  connex {x = NonEmpty}           {y = NonEmpty}           nxy = void $ nxy Refl
  connex {x = CanBeEmpty Static}  {y = CanBeEmpty Static}  nxy = void $ nxy Refl
  connex {x = CanBeEmpty Dynamic} {y = CanBeEmpty Dynamic} nxy = void $ nxy Refl

  connex {x = NonEmpty}     {y = CanBeEmpty _} nxy = Left NE
  connex {x = CanBeEmpty _} {y = NonEmpty}     nxy = Right NE

  connex {x = CanBeEmpty Static}  {y = CanBeEmpty Dynamic} nxy = Right Stat
  connex {x = CanBeEmpty Dynamic} {y = CanBeEmpty Static}  nxy = Left Stat

export
LinearOrder _ NoWeaker where

export
StronglyConnex _ NoWeaker where
  order NonEmpty             NonEmpty             = Left Refl
  order NonEmpty             (CanBeEmpty _)       = Left NE
  order (CanBeEmpty _)       NonEmpty             = Right NE
  order (CanBeEmpty Static)  (CanBeEmpty Static)  = Left Refl
  order (CanBeEmpty Static)  (CanBeEmpty Dynamic) = Right Stat
  order (CanBeEmpty Dynamic) (CanBeEmpty Static)  = Left Stat
  order (CanBeEmpty Dynamic) (CanBeEmpty Dynamic) = Left Refl

weakest : (lem, rem : Emptiness) -> (em ** (lem `NoWeaker` em, rem `NoWeaker` em, Either (lem = em) (rem = em)))
weakest NonEmpty             NonEmpty             = (NonEmpty           ** (Refl, Refl, Left  Refl))
weakest NonEmpty             (CanBeEmpty x)       = (CanBeEmpty x       ** (NE  , Refl, Right Refl))
weakest (CanBeEmpty x)       NonEmpty             = (CanBeEmpty x       ** (Refl, NE  , Left  Refl))
weakest (CanBeEmpty Static)  (CanBeEmpty _)       = (CanBeEmpty Static  ** (Refl, Stat, Left  Refl))
weakest (CanBeEmpty Dynamic) (CanBeEmpty Static)  = (CanBeEmpty Static  ** (Stat, Refl, Right Refl))
weakest (CanBeEmpty Dynamic) (CanBeEmpty Dynamic) = (CanBeEmpty Dynamic ** (Refl, Refl, Left  Refl))

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
