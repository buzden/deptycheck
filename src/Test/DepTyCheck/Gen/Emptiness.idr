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
  AS : {em : _} -> em     `NoWeaker` CanBeEmpty Static

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
min : Emptiness -> Emptiness -> Emptiness
min s@(CanBeEmpty Static) _ = s
min _ s@(CanBeEmpty Static) = s
min d@(CanBeEmpty Dynamic) _ = d
min _ d@(CanBeEmpty Dynamic) = d
min NonEmpty NonEmpty = NonEmpty

minWeakest : (lem, rem : Emptiness) -> (em = lem `min` rem) -> (lem `NoWeaker` em, rem `NoWeaker` em, Either (lem = em) (rem = em))
minWeakest NonEmpty             NonEmpty             Refl = %search
minWeakest NonEmpty             (CanBeEmpty Dynamic) Refl = %search
minWeakest (CanBeEmpty Dynamic) NonEmpty             Refl = %search
minWeakest (CanBeEmpty Dynamic) (CanBeEmpty Dynamic) Refl = %search
minWeakest NonEmpty             (CanBeEmpty Static)  Refl = %search
minWeakest (CanBeEmpty Static)  NonEmpty             Refl = %search
minWeakest (CanBeEmpty Static)  (CanBeEmpty Dynamic) Refl = %search
minWeakest (CanBeEmpty Static)  (CanBeEmpty Static)  Refl = %search
minWeakest (CanBeEmpty Dynamic) (CanBeEmpty Static)  Refl = %search

export
minWeakestL : (lem, rem : Emptiness) -> lem `NoWeaker` (lem `min` rem)
minWeakestL lem rem = fst $ minWeakest lem rem Refl

export
minWeakestR : (lem, rem : Emptiness) -> rem `NoWeaker` (lem `min` rem)
minWeakestR lem rem = fst $ snd $ minWeakest lem rem Refl

export
minStrongestAmongWeakests : (lem, rem, em : Emptiness) ->
                            (lem `NoWeaker` em) -> (rem `NoWeaker` em) ->
                            (lem `min` rem) `NoWeaker` em
minStrongestAmongWeakests lem rem em x y = case snd $ snd $ minWeakest lem rem Refl of
  Left  z => rewrite sym z in x
  Right z => rewrite sym z in y

data Min : (lem, rem, minem : Emptiness) -> Type where
  SL  : Min (CanBeEmpty Static) _ (CanBeEmpty Static)
  SR  : Min _ (CanBeEmpty Static) (CanBeEmpty Static)
  DLR : Min (CanBeEmpty Dynamic) (CanBeEmpty Dynamic) (CanBeEmpty Dynamic)
  NEL : Min NonEmpty x x

--- Relations for particular generator cases ---

-- bind --

public export
data BindToOuter : (emOfBind, outerEm : Emptiness) -> Type where
  BndNE : BindToOuter NonEmpty em
  BndEE : (0 _ : IfUnsolved dp Dynamic) =>
          (0 _ : IfUnsolved idp Dynamic) =>
          BindToOuter (CanBeEmpty idp) (CanBeEmpty dp)

export
bindToOuterRelax : x `BindToOuter` y -> y `NoWeaker` z -> x `BindToOuter` z
bindToOuterRelax BndNE NN = %search
bindToOuterRelax BndNE ND = %search
bindToOuterRelax BndNE DD = %search
bindToOuterRelax BndNE AS = %search
bindToOuterRelax BndEE DD = %search
bindToOuterRelax BndEE AS = %search
