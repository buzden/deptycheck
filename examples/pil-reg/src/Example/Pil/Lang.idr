-- Primitive Imperative Language --
module Example.Pil.Lang

import public Data.List.Lookup

import public Example.Pil.Lang.Expression
import public Example.Pil.Lang.Statement

public export
SomeOps : Ops
SomeOps = MkOps
  {unary = [ (Int', "inc", Int')
           , (String', "as_str", Int')
           , (Bool', "!", Bool')
           ]}
  {binary = [ (Int', "+", Int', Int')
            , (Int', "*", Int', Int')
            , (String', "concat", String', String')
            , (Bool', "&&", Bool', Bool')
            , (Bool', "||", Bool', Bool')
            , (Bool', "<", Int', Int')
            , (Bool', "<=", Int', Int')
            ]}
