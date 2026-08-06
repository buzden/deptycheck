||| The derived generator for the non-branching probe type (investigation,
||| section 7.2).
|||
||| `X n` has exactly one inhabitant, so this measures derivation's machinery with
||| nothing to choose and nothing to branch on. The derived generator is
||| fuel-inert for such a type in the current implementation --- fuel 0, 3 and 10
||| coincide in exponent and in constant --- so one fuel level is enough, and
||| fuel 0 is the cheapest.
|||
||| This is the subject the first upstream issue is about: the derived generator
||| is super-quadratic where the hand-written one is linear, five orders of
||| magnitude apart at n = 16384.
module Perf

import PerfHarness

import XDerived

%default total

||| Measures 2.26 over this grid, with a confidence half-width of about 0.10 ---
||| the same value, to within scatter, as a single hand-written `oneOf` on the
||| recursion edge, which is the investigation's central quantitative claim. Keep
||| this band and `oneof-recursion-edge`'s in step: if they ever stop agreeing,
||| the two have decoupled and that is worth knowing.
band : Band
band = MkBand 1.65 2.95

main : IO ()
main = runSubjects
  [ MkSubject "genX (derived, fuel 0)" (sqrt2Grid 14 23) band $
      \n => depth <$> genX (limit 0) n
  ]
