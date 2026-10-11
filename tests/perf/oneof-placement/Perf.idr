||| Where a single `oneOf` node has to sit for it to cost a power of `n`
||| (investigation, section 7.5).
|||
||| Both of these contain exactly one `oneOf` and both are expected to stay
||| linear: one sits on top of a body that telescopes, the other sits in the base
||| case and is reached exactly once. Together with `oneof-recursion-edge`, which
||| differs from them only in where the same node goes, they are what pins the
||| mechanism down --- if one of these two turned quadratic, the story that the
||| cost comes from re-interposition on the recursion edge would be wrong.
module Perf

import PerfHarness

import XGens

%default total

main : IO ()
main = runSubjects
  [ MkSubject "genXOneOfOffEdge" linearGrid linear $ \n => depth <$> genXOneOfOffEdge n
  , MkSubject "genXOneOfInBase"  linearGrid linear $ \n => depth <$> genXOneOfInBase n
  ]
