module Data.Vect.Uniq

import Data.Fuel
import public Data.So
import Data.Vect

import Test.DepTyCheck.Gen

%default total

public export
data UniqStrVect : Nat -> Type
public export
data NotIn : String -> (n : Nat) -> UniqStrVect n -> Type

data UniqStrVect : Nat -> Type where
  Nil  : UniqStrVect Z
  (::) : (s : String) -> (ss : UniqStrVect n) -> NotIn s n ss => UniqStrVect $ S n

data NotIn : String -> (n : Nat) -> UniqStrVect n -> Type where
  N : NotIn x 0 []
  S : So (x /= s) => NotIn x n ss -> NotIn x (S n) $ (s::ss) @{sub}

public export
toVect : UniqStrVect n -> Vect n String
toVect []      = []
toVect (s::ss) = s :: toVect ss

export
genUniqStrVect : Fuel -> (Fuel -> Gen MaybeEmpty String) => (n : Nat) -> Gen MaybeEmpty $ UniqStrVect n
