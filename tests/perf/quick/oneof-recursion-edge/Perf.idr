||| A single `oneOf` with a single always-live alternative, re-created at every
||| recursion level (investigation, sections 7.4 and 7.5).
|||
||| Nothing here is chosen and nothing branches, yet this is super-quadratic
||| while `oneof-placement`, which contains the same node in a different place, is
||| linear. This is the most valuable single measurement in the suite: it is the
||| mechanism the investigation holds responsible for derived generators being
||| super-quadratic, and it is stated in plain library calls, so it will keep
||| working as a canary even if derivation is rewritten.
|||
||| If the upstream fix that specialises a singleton `oneOf` lands, this test
||| fails with "faster than expected" --- which is the intended way to find out.
module Perf

import PerfHarness

import XGens

%default total

||| Measures 2.26 to 2.40 over this grid, with a confidence half-width of about
||| 0.13. Both edges are four or more half-widths away. The lower one is still
||| far above the 1.0 that a fix specialising a singleton `oneOf` would produce;
||| the upper one excludes the behaviour of two live alternatives.
band : Band
band = MkBand 1.65 2.95

main : IO ()
main = runSubjects
  [ MkSubject "genXOneOf1" (sqrt2Grid 14 23) band $ \n => depth <$> genXOneOf1 n ]
