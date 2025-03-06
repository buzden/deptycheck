module Deriving.DepTyCheck.Util.Logging

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

public export %inline
Info, Details, DeepDetails, Trace, DetailedTrace, Debug, DetailedDebug : Nat
Info = 2; Details = 5; DeepDetails = 7; Trace = 10; DetailedTrace = 12; Debug = 15; DetailedDebug = 20

public export %inline
DefaultLogLevel : Nat
DefaultLogLevel = Trace

export
logPoint :
  Elaboration m =>
  {default DefaultLogLevel level : Nat} ->
  (subTopic : String) -> So (subTopic /= "") =>
  (position : LogPosition) ->
  (mark : String) ->
  m ()
logPoint subTopic position mark = do
  let topic = "deptycheck.derive.\{subTopic}"
  logMsg topic level "\{position}\{mark}"

export
logBounds :
  Elaboration m =>
  {default DefaultLogLevel level : Nat} ->
  (subTopic : String) -> So (subTopic /= "") =>
  (position : LogPosition) ->
  m a ->
  m a
logBounds subTopic position action = do
  let ticksCnt = (4 `minus` length position) `max` 1

  let startFence = replicate ticksCnt '_'
  let startMark = "\{startFence} start \{startFence}"

  let endFence = replicate ticksCnt '^'
  let endMark = "\{endFence}  end  \{endFence}"

  let lg = logPoint {level} subTopic position

  -- vertical monadic style seems to use much less memory than `lg startMark *> action <* lg endMark`
  lg startMark
  r <- action
  lg endMark
  pure r
