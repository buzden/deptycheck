module Language.PilDyn.Utils

import public Test.DepTyCheck.Gen

export %hint
ints : Gen MaybeEmpty Int32
ints = elements [-40..40]

-- For `pick`ing
export
Interpolation a => Interpolation (Maybe a) where
  interpolate Nothing = "<nothing>"
  interpolate (Just x) = interpolate x
