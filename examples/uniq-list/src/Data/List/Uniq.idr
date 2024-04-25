module Data.List.Uniq

import Data.Fuel
import public Data.So

import Test.DepTyCheck.Gen

%default total

public export
data UniqStrList : Type
public export
data NotIn : String -> UniqStrList -> Type

data UniqStrList : Type where
  Nil  : UniqStrList
  (::) : (s : String) -> (ss : UniqStrList) -> s `NotIn` ss => UniqStrList

data NotIn : String -> UniqStrList -> Type where
  N : NotIn x []
  S : So (x /= s) => x `NotIn` ss -> x `NotIn` (s::ss) @{sub}

public export
toList : UniqStrList -> List String
toList []      = []
toList (s::ss) = s :: toList ss

public export
length : UniqStrList -> Nat
length []      = Z
length (_::xs) = S $ length xs

export
genUniqStrList : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty UniqStrList
