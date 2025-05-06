module Language.Reflection.Logging

import public Data.So
import public Data.String -- public due to compiler's bug #2439

import public Language.Reflection

%default total

public export
interface LogPosition a where
  logPosition : a -> String

public export
data LogPositions : Type where
  Nil  : LogPositions
  (::) : LogPosition a => a -> LogPositions -> LogPositions

export
Interpolation LogPositions where
  interpolate = joinBy " " . Prelude.toList . toList [<] where
    toList : SnocList String -> LogPositions -> SnocList String
    toList acc []      = acc
    toList acc (x::xs) = toList (acc :< logPosition x) xs

export
length : LogPositions -> Nat
length []      = Z
length (_::xs) = S $ length xs

public export
data LogLevel
  = Warning
  | Info
  | Details
  | FineDetails
  | Trace
  | DetailedTrace
  | Debug
  | DetailedDebug

public export
interface ElabLogLevels where
  toNatLevel : LogLevel -> Nat
  defaultLogLevel : LogLevel

public export %defaulthint
DefaultElabLogLevels : ElabLogLevels
DefaultElabLogLevels = I where
  [I] ElabLogLevels where
    toNatLevel Warning       = 0
    toNatLevel Info          = 2
    toNatLevel Details       = 5
    toNatLevel FineDetails   = 7
    toNatLevel Trace         = 10
    toNatLevel DetailedTrace = 12
    toNatLevel Debug         = 15
    toNatLevel DetailedDebug = 20
    defaultLogLevel = Trace

export
logPoint : Elaboration m =>
           ElabLogLevels =>
           {default defaultLogLevel level : LogLevel} ->
           (topic : String) -> So (topic /= "") =>
           (positions : LogPositions) ->
           (desc : String) ->
           m ()
logPoint topic positions desc = logMsg topic (toNatLevel level) "\{positions} \{desc}"

export
logBounds : Elaboration m =>
            ElabLogLevels =>
            {default defaultLogLevel level : LogLevel} ->
            (topic : String) -> So (topic /= "") =>
            (positions : LogPositions) ->
            m a ->
            m a
logBounds topic positions action = do
  let ticksCnt = (4 `minus` length positions) `max` 1

  let startFence = replicate ticksCnt '_'
  let startMark = "\{startFence} start \{startFence}"

  let endFence = replicate ticksCnt '^'
  let endMark = "\{endFence}  end  \{endFence}"

  let lg = logPoint {level} topic positions

  -- vertical monadic style seems to use much less memory than `lg startMark *> action <* lg endMark`
  lg startMark
  r <- action
  lg endMark
  pure r
