module Language.Reflection.Expr.Interpolation

import Language.Reflection.Pretty
import Language.Reflection.TTImp

import Text.PrettyPrint.Bernardy

%default total

[FromPretty] Pretty a => (layout : LayoutOpts) => Interpolation a where
  interpolate = render layout . pretty

export %hint
InterpolationTTImp : (layout : LayoutOpts) => Interpolation TTImp
InterpolationTTImp = FromPretty

public export %defaulthint %inline
DefaultLayout : LayoutOpts
DefaultLayout = Opts {lineLength = 152}
