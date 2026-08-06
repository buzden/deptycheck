||| `oneOf` with three live alternatives on the recursion edge.
|||
||| The point of this subject is the *comparison* with two alternatives: the
||| investigation finds that the third alternative buys a constant factor of about
||| 1.8 and does not move the exponent at all. So branching existence sets the
||| degree and branching arity sets the constant. Nightly rather than per-PR,
||| because it adds no mechanism that `oneof-arity-two` does not already cover ---
||| it only confirms that the degree has stopped growing.
module Perf

import PerfHarness

import XGens

%default total

||| Higher than the two-alternative band although the asymptotic exponents are
||| equal, because over a short low-n range the constant factor is still being
||| absorbed into the slope.
band : Band
band = MkBand 2.60 4.20

main : IO ()
main = runSubjects
  [ MkSubject "genXOneOf3" (sqrt2Grid 10 17) band $ \n => depth <$> genXOneOf3 n ]
