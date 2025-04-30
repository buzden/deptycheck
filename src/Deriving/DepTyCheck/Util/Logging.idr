module Deriving.DepTyCheck.Util.Logging

import public Data.List.Extra
import public Data.So

import public Deriving.DepTyCheck.Util.Primitives

import public Language.Reflection.Compat

%default total

public export
interface SingleLogPosition a where
  logPosition : a -> String

export
SingleLogPosition Con where
  logPosition con = do
    let fullName = show con.name
    let fullName' = unpack fullName
    maybe fullName (pack . flip drop fullName' . S . finToNat) $ findLastIndex (== '.') fullName'

export
SingleLogPosition TypeInfo where
  logPosition ti = "\{show $ extractTargetTyExpr ti}"

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

public export
data LogLevel
  = Info
  | Details
  | DeepDetails
  | Trace
  | DetailedTrace
  | Debug
  | DetailedDebug

public export
toNatLevel : LogLevel -> Nat
toNatLevel Info          = 2
toNatLevel Details       = 5
toNatLevel DeepDetails   = 7
toNatLevel Trace         = 10
toNatLevel DetailedTrace = 12
toNatLevel Debug         = 15
toNatLevel DetailedDebug = 20

public export %inline
DefaultLogLevel : LogLevel
DefaultLogLevel = Trace

export
logPoint : Elaboration m =>
           {default DefaultLogLevel level : LogLevel} ->
           (subTopic : String) -> So (subTopic /= "") =>
           (position : LogPosition) ->
           (mark : String) ->
           m ()
logPoint subTopic position mark = do
  let topic = "deptycheck.derive.\{subTopic}"
  logMsg topic (toNatLevel level) "\{position}\{mark}"

export
logBounds : Elaboration m =>
            {default DefaultLogLevel level : LogLevel} ->
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
