||| `frequency` matched against `oneOf`, arity for arity, plus a control for the
||| structural weight recomputation that derivation emits (investigation,
||| section 7.4).
|||
||| Three things are being watched here. That `frequency` stays in the same class
||| as `oneOf` of the same arity, so that weights are known to change the
||| distribution and not the complexity. That the two-alternative case behaves the
||| same whether the weights are constant or recomputed in linear time per level,
||| which is what makes the recomputation invisible at scale. And that the
||| single-alternative case tracks `oneOf` with one alternative.
|||
||| Nightly rather than per-PR: the `oneOf` family already covers the mechanism,
||| and these add only the bookkeeping on top of it.
module Perf

import PerfHarness

import XGens

%default total

||| Tracks `oneOf` with one alternative, so this range is deliberately the same
||| as `oneof-recursion-edge`'s.
single : ExpectedRange
single = MkExpectedRange 1.65 2.95

||| One range covers the constant-weight and the recomputed-weight case, since
||| the point of the pair is that they agree.
double : ExpectedRange
double = MkExpectedRange 2.25 4.20

main : IO ()
main = runSubjects
  [ MkSubject "genXFreq1"         (sqrt2Grid 14 23) single $ \n => depth <$> genXFreq1 n
  , MkSubject "genXFreq2Const"    (sqrt2Grid 8 17)  double $ \n => depth <$> genXFreq2Const n
  , MkSubject "genXFreq2Weighted" (sqrt2Grid 8 17)  double $ \n => depth <$> genXFreq2Weighted n
  ]
