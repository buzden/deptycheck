||| Timing harness for measuring the complexity class of a generator on a shared
||| CI machine.
|||
||| The output is split deliberately. Only the verdict goes to standard output,
||| where the golden runner compares it against `expected`; every number goes to
||| standard error and to `perf-data.tsv`, neither of which is compared. So the
||| test is reproducible although the measurement is not.
module PerfHarness

import Data.List
import Data.Stream
import Data.String

import public PerfStat

import System.Clock
import System.File
import System.Random.Pure
import System.Random.Pure.StdGen

import public Test.DepTyCheck.Gen

%default total

--- Subjects ---

||| A family of generators indexed by a size, together with the complexity
||| expected of it.
public export
record Subject where
  constructor MkSubject
  ||| Appears in the golden output, so keep it stable.
  name : String
  ||| Sizes to measure at. Pinned as part of the test, because `expected` is
  ||| calibrated over exactly these sizes.
  sizes : List Nat
  ||| Exponent expected over `sizes`.
  expected : ExpectedRange
  ||| Generates a value of the given size and reduces it to a number.
  |||
  ||| The reduction must walk the whole value. It is the only thing that forces
  ||| generation to really happen inside the timed window; a `case` on the outer
  ||| constructor forces the constructor and nothing else, which is how the
  ||| investigation ended up with a generator that appeared to be O(1) (its
  ||| section 7.3).
  weigh : (n : Nat) -> Gen MaybeEmpty Nat

||| Geometric grid running from `2 ^ (loHalfPow / 2)` to `2 ^ (hiHalfPow / 2)`.
|||
||| Two properties matter. Equal spacing of `log n` is what makes Sen's interval
||| exactly applicable rather than approximately. And a step of sqrt 2 gives two
||| points per doubling, which is what distinguishes "the exponent is still
||| climbing" from "the exponent has settled" (investigation, section 8.2).
public export
sqrt2Grid : (loHalfPow, hiHalfPow : Nat) -> List Nat
sqrt2Grid lo hi = halfPow <$> [lo .. hi] where
  halfPow : Nat -> Nat
  halfPow i = let logN    : Double := 0.5 * cast i * log 2.0
                  rounded : Double := 0.5 + exp logN
               in integerToNat $ cast rounded

||| The grid shared by every subject expected to stay linear.
|||
||| It starts at n = 512 rather than lower so that the fixed cost of a draw ---
||| building the generator, stepping the seed --- stays a few per cent of the
||| measured time. Below that it would depress the slope at the cheap end of the
||| grid and make a linear generator look sublinear.
public export
linearGrid : List Nat
linearGrid = sqrt2Grid 18 28

||| The expected range shared by every subject expected to stay linear.
|||
||| Calibrated on the investigation's data, where these generators measure
||| between 0.92 and 1.11 over `linearGrid` with a confidence half-width of
||| about 0.16. The range leaves three to four half-widths of margin on each
||| side, and excludes by a wide margin the quadratic behaviour that a `oneOf`
||| appearing on one of these recursion edges would produce.
public export
linear : ExpectedRange
linear = MkExpectedRange 0.55 1.55

--- Timing a batch ---

||| Shortest timed window we accept.
|||
||| Long enough that the clock's resolution and the cost of reading it are
||| negligible: the investigation found a microsecond-granular clock under which
||| every linear generator read as a flat 1 us floor for all n below about 1024
||| (its section 8.3, item 3). Batching until the window is this long removes
||| that floor instead of working around it by only measuring huge n.
minWindowNs : Integer
minWindowNs = 30000000

||| What a batch of draws produced: the sum of the weights, which exists only to
||| force the values, and the number of draws that came back empty.
record Batch where
  constructor MkBatch
  weight, misses : Nat

||| Draws `reps` values, re-creating the generator each time, exactly as the
||| investigation's harness did --- so what is measured is the cost of building
||| the generator and sampling it once, not of sampling a cached one.
draw : (reps : Nat) -> StdGen -> (weigh : Nat -> Gen MaybeEmpty Nat) -> (n : Nat) -> Batch -> Batch
draw Z     _    _     _ acc                     = acc
draw (S k) seed weigh n (MkBatch weight misses) =
  let (seed', drawn) = Prelude.head $ unGenTryAll' seed $ weigh n in
  case drawn of
    Just w  => draw k seed' weigh n $ MkBatch (weight + w) misses
    Nothing => draw k seed' weigh n $ MkBatch weight (S misses)

seedFor : Nat -> StdGen
seedFor n = mkStdGen $ cast $ the Integer $ cast n

||| The seed is a fixed function of `n`, so the sequence of generated values ---
||| and hence the amount of work --- is the same on every pass, on every runner
||| and in every rerun. For a branching generator such as the one for `NatList`
||| this removes a whole source of variance that the investigation lived with.
timedDraw : (reps : Nat) -> Subject -> (n : Nat) -> IO (Integer, Batch)
timedDraw reps s n = do
  start <- clockTime Monotonic
  let MkBatch weight misses = draw reps (seedFor n) s.weigh n $ MkBatch 0 0
  finish <- clockTime Monotonic
  pure (toNano $ timeDifference finish start, MkBatch weight misses)

||| Chooses how many values to draw per window at size `n`, doubling until the
||| window is long enough.
|||
||| Doubles as the warm-up: everything it draws is discarded, so first-call
||| effects --- code loading, the heap reaching its working size --- cannot land
||| in a measurement (investigation, section 8.3, item 1). The count is then
||| fixed for the whole run, so that all passes are directly comparable and the
||| tuning itself cannot leak into the slope.
calibrate : Subject -> (n : Nat) -> IO Nat
calibrate s n = go 30 1 where
  go : Nat -> Nat -> IO Nat
  go Z     reps = pure reps
  go (S k) reps = do
    (elapsed, _) <- timedDraw reps s n
    if elapsed >= minWindowNs then pure reps else go k (reps * 2)

--- Passes over the grid ---

||| Keys the list with a fixed-seed pseudo-random sequence and sorts by the keys.
shuffled : StdGen -> List a -> List a
shuffled seed xs = map snd $ sortBy (comparing fst) $ keyed seed xs where
  keyed : StdGen -> List a -> List (Bits64, a)
  keyed _ []        = []
  keyed s (x :: xs) = let (s', k) = next s in (k, x) :: keyed s' xs

||| One measurement pass: every grid point once, in an order that differs from
||| pass to pass.
|||
||| Randomising the order is what keeps anything drifting with wall-clock time
||| --- frequency scaling, a co-tenant arriving, the heap growing --- from
||| correlating with `n` and biasing the slope. Measuring the grid in ascending
||| order, as one naturally would, makes any monotone drift indistinguishable
||| from a change of exponent. The seed is fixed, so the run stays reproducible.
onePass : Subject -> (pass : Nat) -> (plan : List (Nat, Nat)) -> IO (List (Nat, Double), Nat)
onePass s pass plan = do
  results <- for (shuffled (seedFor pass) plan) $ \(n, reps) => do
    (elapsed, batch) <- timedDraw reps s n
    let nanos   : Double := cast elapsed
        perDraw : Double := nanos / cast reps
    pure ((n, perDraw), batch.misses)
  pure (sortBy (comparing fst) $ map fst results, sum $ map snd results)

||| Point-wise minimum of two passes.
|||
||| The minimum, not the mean. Interference on a shared machine can only add
||| time, never remove it, so the noise is one-sided and the minimum over passes
||| is the natural estimator of the undisturbed cost --- and it has far less
||| variance than the mean, which imports every spike it sees. The investigation
||| averaged, which is the right thing when describing how a machine actually
||| behaves; here we want the machine out of the way.
leastOf : List (Nat, Double) -> List (Nat, Double) -> List (Nat, Double)
leastOf = zipWith $ \(n, a), (_, b) => (n, min a b)

record Measurement where
  constructor MkMeasurement
  points : List (Nat, Double)
  passes, misses : Nat

||| Least and most passes we will spend on one subject.
minPasses, maxPasses : Nat
minPasses = 5
maxPasses = 9

logPoints : List (Nat, Double) -> List LogPoint
logPoints = map $ \(n, ns) => MkLogPoint (log $ cast n) (log ns)

||| Runs passes until the interval is narrow enough to decide, or until the
||| budget is spent.
|||
||| The stopping rule reads only the *width* of the interval, never where it sits
||| relative to the range. That distinction is the whole point: stopping on width
||| is fixed-precision sampling and leaves the significance level alone, whereas
||| stopping on the outcome --- "keep sampling until it passes" --- would inflate
||| the false-negative rate without bound.
measure : Subject -> IO Measurement
measure s = do
    plan <- for s.sizes $ \n => (n,) <$> calibrate s n
    (firstPass, missed) <- onePass s 1 plan
    go (maxPasses `minus` 1) plan $ MkMeasurement firstPass 1 missed

  where
    precise : Measurement -> Bool
    precise m = m.passes >= minPasses &&
                maybe False (\e => e.halfWidth <= resolution s.expected) (estimate $ logPoints m.points)

    go : (budget : Nat) -> List (Nat, Nat) -> Measurement -> IO Measurement
    go Z     _    m = pure m
    go (S k) plan m = if precise m then pure m else do
      (nextPass, missed) <- onePass s (S m.passes) plan
      go k plan $ MkMeasurement (leastOf m.points nextPass) (S m.passes) (m.misses + missed)

--- Reporting ---

note : String -> IO ()
note = ignore . fPutStrLn stderr

||| Both a coarse index of how fast this runner is and a warm-up for the process
||| as a whole.
|||
||| It exists so that the absolute times in `perf-data.tsv` can be compared
||| across runners of different speeds when someone plots them over time. It is
||| reported and never asserted on: absolute times on GitHub's runners are not
||| comparable, which is the reason this suite measures exponents in the first
||| place.
machineIndexNs : IO Integer
machineIndexNs = do
    start <- clockTime Monotonic
    let True = allocate 2000000 == 2000000
      | False => pure 0
    finish <- clockTime Monotonic
    pure $ toNano $ timeDifference finish start

  where
    ||| Allocates a list and immediately consumes it, rather than spinning on
    ||| arithmetic, because allocation is what generators spend their time on.
    allocate : Nat -> Nat
    allocate n = foldl (+) 0 $ List.replicate n $ the Nat 1

||| A miss outranks everything: a generator that returned nothing was measured
||| failing rather than generating, so its timings mean nothing at all.
verdictLine : Subject -> Measurement -> Maybe Estimate -> String
verdictLine s m est = "\{s.name}: \{outcome}" where
  outcome : String
  outcome = if m.misses > 0
              then "invalid: generator produced no value"
              else maybe "inconclusive: no usable points" (interpolate . verdictOf s.expected) est

diagnose : Subject -> Measurement -> Maybe Estimate -> IO ()
diagnose s m est = do
  note "# \{s.name}: \{show m.passes} passes, \{show m.misses} misses, expected \{s.expected}"
  note $ maybe "#   exponent: no estimate" (\e => "#   exponent \{e}") est
  for_ m.points $ \(n, ns) => note "#   n=\{show n} \{show ns} ns/sample"

||| Tab-separated rows for the run's artifact, one per grid point.
rows : Subject -> Measurement -> Maybe Estimate -> List String
rows s m est = m.points <&> \(n, ns) =>
  joinBy "\t" [ s.name, show n, show ns, show m.passes
              , maybe "" (\e => show e.exponent) est
              , maybe "" (\e => show e.lower) est
              , maybe "" (\e => show e.upper) est
              , show s.expected.lo, show s.expected.hi
              ]

||| Measures every subject, prints one verdict line per subject to standard
||| output, and leaves the numbers in `perf-data.tsv` beside the test.
export
runSubjects : List Subject -> IO ()
runSubjects subjects = do
  index <- machineIndexNs
  note "# machine index: \{show index} ns"
  measured <- for subjects $ \s => do
    m <- measure s
    let est = estimate $ logPoints m.points
    diagnose s m est
    putStrLn $ verdictLine s m est
    pure $ rows s m est
  ignore $ writeFile "perf-data.tsv" $ unlines $
    "subject\tn\tns_per_sample\tpasses\texponent\tci_lo\tci_hi\texpected_lo\texpected_hi" ::
    "# machine_index_ns\t\{show index}" :: concat measured
