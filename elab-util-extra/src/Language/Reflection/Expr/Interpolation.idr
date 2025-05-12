module Language.Reflection.Expr.Interpolation

import Language.Reflection.Pretty
import Language.Reflection.TTImp

import Text.PrettyPrint.Bernardy

%default total

export %hint
InterpolationTTImp' : Interpolation TTImp
InterpolationTTImp' = ThroughPretty {layout = Opts {lineLength = 152}}
