||| Hand-written generators whose bind continuations are all `pure`, so the chain
||| telescopes and sampling is one traversal.
|||
||| These are the control group. They touch no derivation machinery at all, so if
||| one of them changes class, the change is in `Gen` itself --- and if all of
||| them change class at once, suspect the harness or the runner rather than the
||| library.
module Perf

import PerfHarness

import XGens

%default total

main : IO ()
main = runSubjects
  [ MkSubject "genXByHand" linearGrid linear $ \n => depth <$> genXByHand n
  , MkSubject "genXMap"    linearGrid linear $ \n => depth <$> genXMap n
  , MkSubject "genXAp"     linearGrid linear $ \n => depth <$> genXAp n
  ]
