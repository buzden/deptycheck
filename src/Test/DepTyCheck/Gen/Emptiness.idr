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
  Refl : em                 `NoWeaker` em
  NED  : NonEmpty           `NoWeaker` CanBeEmpty Dynamic
  NES  : NonEmpty           `NoWeaker` CanBeEmpty Static
  EDS  : CanBeEmpty Dynamic `NoWeaker` CanBeEmpty Static

infix 6 `NoWeaker`

export
Reflexive _ NoWeaker where
  reflexive {x = NonEmpty}           = %search
  reflexive {x = CanBeEmpty Static}  = %search
  reflexive {x = CanBeEmpty Dynamic} = %search

export
transitive' : x `NoWeaker` y -> y `NoWeaker` z -> x `NoWeaker` z
transitive' Refl v = v
transitive' v Refl = v
transitive' NED EDS = NES

export
Transitive _ NoWeaker where
  transitive = transitive'

export
Antisymmetric _ NoWeaker where
  antisymmetric Refl _ = Refl

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

weakest : (lem, rem : Emptiness) -> (em ** (lem `NoWeaker` em, rem `NoWeaker` em, Either (lem = em) (rem = em)))
weakest NonEmpty             NonEmpty             = (NonEmpty           ** %search)
weakest NonEmpty             (CanBeEmpty Dynamic) = (CanBeEmpty Dynamic ** %search)
weakest (CanBeEmpty Dynamic) NonEmpty             = (CanBeEmpty Dynamic ** %search)
weakest (CanBeEmpty Dynamic) (CanBeEmpty Dynamic) = (CanBeEmpty Dynamic ** %search)
weakest NonEmpty             (CanBeEmpty Static)  = (CanBeEmpty Static  ** %search)
weakest (CanBeEmpty Static)  NonEmpty             = (CanBeEmpty Static  ** %search)
weakest (CanBeEmpty Static)  (CanBeEmpty Dynamic) = (CanBeEmpty Static  ** %search)
weakest (CanBeEmpty Static)  (CanBeEmpty Static)  = (CanBeEmpty Static  ** %search)
weakest (CanBeEmpty Dynamic) (CanBeEmpty Static)  = (CanBeEmpty Static  ** %search)

--- Relations for particular generator cases ---

-- alternatives --

public export
data AltsToOuter : (emOfAlts, outerEm : Emptiness) -> Type where
  AltsNE : {em : _} -> AltsToOuter NonEmpty em
  AltsEE : {dp : _} ->
           (0 _ : IfUnsolved dp Dynamic) =>
           AltsToOuter (CanBeEmpty Dynamic) (CanBeEmpty dp)

export
altsToOuterRefl : AltsToOuter em rem => AltsToOuter em em
altsToOuterRefl @{AltsNE} = %search
altsToOuterRefl @{AltsEE} = %search

export
altsToOuterRefl' : em `NoWeaker` CanBeEmpty Dynamic => AltsToOuter em em
altsToOuterRefl' @{Refl} = %search
altsToOuterRefl' @{NED}  = %search

export
altsToOuterRelax : x `AltsToOuter` y -> y `NoWeaker` z -> x `AltsToOuter` z
altsToOuterRelax v      Refl = v
altsToOuterRelax AltsNE NED  = %search
altsToOuterRelax AltsNE NES  = %search
altsToOuterRelax AltsNE EDS  = %search
altsToOuterRelax AltsEE EDS  = %search

export
altsToOuterRelax' : x `AltsToOuter` y -> x `NoWeaker` y
altsToOuterRelax' $ AltsNE {em = NonEmpty}           = %search
altsToOuterRelax' $ AltsNE {em = CanBeEmpty Static}  = %search
altsToOuterRelax' $ AltsNE {em = CanBeEmpty Dynamic} = %search
altsToOuterRelax' $ AltsEE {dp = Static}             = %search
altsToOuterRelax' $ AltsEE {dp = Dynamic}            = %search

-- bind --

public export
data BindToOuter : (emOfBind, outerEm : Emptiness) -> Type where
  BndNE : BindToOuter NonEmpty em
  BndEE : (0 _ : IfUnsolved dp Dynamic) =>
          (0 _ : IfUnsolved idp Dynamic) =>
          BindToOuter (CanBeEmpty idp) (CanBeEmpty dp)

export
bindToOuterRelax : x `BindToOuter` y -> y `NoWeaker` z -> x `BindToOuter` z
bindToOuterRelax _     Refl = %search
bindToOuterRelax BndNE NED  = %search
bindToOuterRelax BndNE NES  = %search
bindToOuterRelax BndNE EDS  = %search
bindToOuterRelax BndEE EDS  = %search
