module Language.Reflection.Expr.Interpolation

import Language.Reflection.Pretty
import Language.Reflection.TTImp

import Text.PrettyPrint.Bernardy

%default total

[FromPretty] Pretty a => (layout : LayoutOpts) => Interpolation a where
  interpolate = render layout . pretty

DefaultLayout : LayoutOpts
DefaultLayout = Opts {lineLength = 152}

export %hint
InterpolationTTImp : Interpolation TTImp
InterpolationTTImp = FromPretty {layout = DefaultLayout}
