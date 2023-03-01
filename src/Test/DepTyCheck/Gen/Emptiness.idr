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
  Refl : em                `NoWeaker` em
  NE   : NonEmpty          `NoWeaker` CanBeEmpty dp
  Stat : CanBeEmpty Static `NoWeaker` CanBeEmpty Dynamic

infix 6 `NoWeaker`

export
Reflexive _ NoWeaker where
  reflexive = Refl

export
Transitive _ NoWeaker where
  transitive Refl x    = x
  transitive NE   Refl = NE
  transitive NE   Stat = NE
  transitive Stat Refl = Stat

export
Antisymmetric _ NoWeaker where
  antisymmetric Refl Refl = Refl

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

  connex {x = CanBeEmpty Static}  {y = CanBeEmpty Dynamic} nxy = Left Stat
  connex {x = CanBeEmpty Dynamic} {y = CanBeEmpty Static}  nxy = Right Stat

export
LinearOrder _ NoWeaker where

export
StronglyConnex _ NoWeaker where
  order NonEmpty             NonEmpty             = Left Refl
  order NonEmpty             (CanBeEmpty _)       = Left NE
  order (CanBeEmpty _)       NonEmpty             = Right NE
  order (CanBeEmpty Static)  (CanBeEmpty Static)  = Left Refl
  order (CanBeEmpty Static)  (CanBeEmpty Dynamic) = Left Stat
  order (CanBeEmpty Dynamic) (CanBeEmpty Static)  = Right Stat
  order (CanBeEmpty Dynamic) (CanBeEmpty Dynamic) = Left Refl

--- Relations for particular generator cases ---

public export %inline
CanBeInAlternatives : Emptiness -> Type
CanBeInAlternatives = NoWeaker $ CanBeEmpty Dynamic

public export
data BindToOuter : (emOfBind, outerEm : Emptiness) -> Type where
  BndNE : BindToOuter NonEmpty NonEmpty
  BndEE : (0 _ : IfUnsolved em Dynamic) =>
          (0 _ : IfUnsolved iem Dynamic) =>
          BindToOuter (CanBeEmpty iem) (CanBeEmpty em)
