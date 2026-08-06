||| The original case study: a length-indexed list, which unlike `X` really
||| branches (investigation, section 7.1).
|||
||| Three subjects that generate the same shape of value, so that the cost can be
||| attributed:
|||
|||   * fuel 0, where every element can only be `Z`, so nothing branches --- this
|||     is the same super-quadratic behaviour `derived-x` shows;
|||   * fuel 3, where branching is on and the exponent is higher. Fuel saturates
|||     fast: 3, 10 and 20 all sit on the same plateau, so measuring one level
|||     above the threshold is enough and 3 is by far the cheapest;
|||   * the hand-written spine with the element hardcoded, which never calls the
|||     derived element generator and is linear. It is the reference for the
|||     five-orders-of-magnitude headline, and it is what would move if the cost
|||     ever turned out to live in the spine recursion or in the unary index
|||     rather than in the element generator.
module Perf

import PerfHarness

import NatListGens

%default total

||| Measures 2.33, half-width about 0.08. Coincides with `derived-x`, which is
||| what makes the fuel-0 case legible as the same phenomenon.
noBranching : Band
noBranching = MkBand 1.60 2.95

||| As with `oneof-arity-two` this is a range-local exponent: the asymptotic
||| value is about 3.6, reached only past the top of this grid. What the band has
||| to discriminate against below is branching ceasing to cost anything extra,
||| which over this range would read about 1.6.
branching : Band
branching = MkBand 2.20 3.80

main : IO ()
main = runSubjects
  [ MkSubject "genNatList (derived, fuel 0)" (sqrt2Grid 16 24) noBranching $
      \n => weighNatList <$> genNatList (limit 0) n
  , MkSubject "genNatList (derived, fuel 3)" (sqrt2Grid 8 18) branching $
      \n => weighNatList <$> genNatList (limit 3) n
  , MkSubject "genDegenerateLists" linearGrid linear $
      \n => weighNatList <$> genDegenerateLists n
  ]
