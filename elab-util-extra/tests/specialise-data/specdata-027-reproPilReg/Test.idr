module Test

import Shared

%default total

%language ElabReflection

public export
data Lookup : a -> List (a, b) -> Type where
  Here : (y : b) -> Lookup x $ (x, y)::xys
  There : Lookup z xys -> Lookup z $ (x, y)::xys

public export
data Type' = Bool' | Int' | String'



%runElab do
  let task =
    \ x =>
        \ y =>
          Lookup
            {b = Builtin.Pair String (Type', Type')}
            {a = Type'}
            x
            y
  qtask <- quote task
  let (lArgs, lRhs) = unLambda qtask
  (nlt', nl') <- normaliseTask lArgs lRhs
  nlt : Type <- check nlt'
  nl : nlt <- check nl'
  specialiseDataLam' "Y" nl

