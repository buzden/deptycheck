||| `oneOf` with two live alternatives on the recursion edge (investigation,
||| section 7.4).
|||
||| The step from one alternative to two is where the exponent jumps by about one
||| and a half powers; going from two to three then costs a constant factor only.
||| So this subject is what tells us whether "branching exists" still sets the
||| degree.
|||
||| Note that the band is a range-local exponent, not the asymptotic one. The
||| investigation reads about 3.7 asymptotically, but only past n = 512, where a
||| single sample already costs seconds; over the grid that is affordable on CI
||| the exponent is still climbing and measures about 2.9. Widening the grid
||| upward would change the expected value, which is why the grid is pinned here
||| together with the band.
module Perf

import PerfHarness

import XGens

%default total

||| The widest interval in the suite, because the curve is still bending over
||| the affordable range; the grid is carried up to n = 512, which costs a couple
||| of minutes but is what buys the lever arm. A drop to the single-alternative
||| class measures about 1.7 over this range, so it is still detected with room
||| to spare.
band : Band
band = MkBand 2.30 3.95

main : IO ()
main = runSubjects
  [ MkSubject "genXOneOf2" (sqrt2Grid 8 18) band $ \n => depth <$> genXOneOf2 n ]
