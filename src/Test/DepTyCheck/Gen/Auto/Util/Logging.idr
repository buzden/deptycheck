module Test.DepTyCheck.Gen.Auto.Util.Logging

import public Data.So

import public Language.Reflection

%default total

public export
interface SingleLogPosition a where
  logPosition : a -> String

public export
data LogPosition : Type where
  Nil  : LogPosition
  (::) : SingleLogPosition a => a -> LogPosition -> LogPosition

-- Prints space at the end on the non-empty list
export
Interpolation LogPosition where
  interpolate = concat . toList [<] where
    toList : SnocList String -> LogPosition -> SnocList String
    toList acc []      = acc
    toList acc (x::xs) = toList (acc :< logPosition x :< " ") xs

export
length : LogPosition -> Nat
length []      = Z
length (_::xs) = S $ length xs

export
logBounds : Elaboration m => {default 5 level : Nat} -> (subTopic : String) -> So (subTopic /= "") => (position : LogPosition) -> m a -> m a
logBounds subTopic position action = do
  let topic = "deptycheck.derive.\{subTopic}"
  let ticksCnt = (4 `minus` length position) `max` 1

  let startFence = replicate ticksCnt '_'
  let startMark = "\{startFence} start \{startFence}"

  let endFence = replicate ticksCnt '^'
  let endMark = "\{endFence}  end  \{endFence}"

  let lg : String -> m () := \mark => logMsg topic level "\{position}\{mark}"

  lg startMark *> action <* lg endMark
