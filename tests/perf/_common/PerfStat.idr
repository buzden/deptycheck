||| Estimation of the exponent of a power law, with a confidence interval, and a
||| verdict on whether that exponent still lies in an expected band.
|||
||| Why the exponent and not the time. A CI runner is a shared virtual machine,
||| so its speed relative to any other runner is an unknown factor `c`. Under
||| `T(n) = c * n^b` the slope of `log T` against `log n` is `b`, whatever `c`
||| is. The exponent is therefore measurable on GitHub's infrastructure, while
||| an absolute time is not: everything the runner lottery does to us lands in
||| `c` and cancels.
module PerfStat

import Data.List
import Data.Maybe
import Data.Nat

%default total

--- Measured curves ---

||| One point of a log-log curve. The base of the logarithm is irrelevant --- it
||| cancels in every ratio below --- as long as it is the same for both fields.
public export
record LogPoint where
  constructor MkLogPoint
  logSize, logTime : Double

||| An exponent estimate with a two-sided confidence interval.
public export
record Estimate where
  constructor MkEstimate
  exponent, lower, upper : Double

public export %inline
(.halfWidth) : Estimate -> Double
e.halfWidth = (e.upper - e.lower) / 2

export
Interpolation Estimate where
  interpolate e = "\{show e.exponent} (ci [\{show e.lower}, \{show e.upper}])"

--- Small numeric helpers ---

||| Every unordered pair of distinct elements.
allPairs : List a -> List (a, a)
allPairs []        = []
allPairs (x :: xs) = map (x,) xs ++ allPairs xs

at : Nat -> List Double -> Double
at _     []        = 0
at Z     (x :: _)  = x
at (S k) (_ :: xs) = at k xs

median : List Double -> Double
median xs = let sorted = sort xs
                half   = length xs `div` 2 in
            if length xs `mod` 2 == 1
              then at half sorted
              else (at (half `minus` 1) sorted + at half sorted) / 2

||| Index into an ascending list of `count` elements, clamped to it.
clampIdx : (count : Nat) -> Double -> Nat
clampIdx count x = if x <= 0 then 0 else min (count `minus` 1) (integerToNat $ cast x)

||| Standard deviation of Kendall's `S` statistic over `m` untied observations.
sigmaS : (m : Nat) -> Double
sigmaS m = sqrt $ cast (m * (m `minus` 1) * (2 * m + 5)) / 18

--- The estimator ---

||| The two-sided normal quantile `z(1 - alpha/2)` at `alpha` = 5%, i.e.
||| `z(0.975)`.
|||
||| Fixed rather than computed from a significance level. 5% is the conventional
||| choice and nothing in this suite has any reason to want another one, so
||| computing it would mean pulling an inverse normal CDF --- and, through it, a
||| binding to libm --- into a benchmark, in exchange for a parameter no caller
||| ever sets.
|||
||| On the reference data of the investigation this level yields intervals of
||| half-width 0.08 to 0.42, from two to ten times narrower than the one-power
||| gap between the complexity classes that have to be told apart.
z975 : Double
z975 = 1.959963985

||| Theil--Sen slope of the given points, with a distribution-free confidence
||| interval at the 5% level.
|||
||| The estimate is the median of the slopes of all pairs of points. Its
||| breakdown point is about 29%, so up to roughly a third of the sweep may be
||| arbitrarily corrupted without moving the answer --- and that is the shape of
||| CI noise, where a co-tenant or a garbage collection inflates a few points
||| and leaves the rest alone. Least squares has a breakdown point of zero: one
||| spike tilts the whole fit, which is exactly the failure the investigation
||| kept running into (see its section 8.3, item 2).
|||
||| The interval is Sen's. With the `N` pairwise slopes sorted ascending, the
||| bounds are the order statistics at ranks `(N -/+ C) / 2`, where
||| `C = z(0.975) * sigma(S)` comes from the normal approximation to
||| Kendall's `S`. It assumes only that the residuals are independent and
||| identically distributed: no normality, no equal variances, no model of what
||| the noise looks like --- which matters, because runner noise is strongly
||| right-skewed and nobody knows its distribution. The approximation to `S` is
||| the reason the grids below carry at least eight points. Ranks are rounded
||| outwards, so the interval errs towards being too wide, i.e. towards not
||| reporting a change.
export
estimate : List LogPoint -> Maybe Estimate
estimate points = case sort $ mapMaybe pairSlope $ allPairs points of
    []              => Nothing
    slopes@(_ :: _) => Just $ MkEstimate (median slopes) (lowerBound slopes) (upperBound slopes)

  where
    ||| Half-width of the rank window, in units of pairwise slopes.
    c : Double
    c = z975 * sigmaS (length points)

    pairSlope : (LogPoint, LogPoint) -> Maybe Double
    pairSlope (p, q) = toMaybe (p.logSize /= q.logSize) $
                         (q.logTime - p.logTime) / (q.logSize - p.logSize)

    lowerBound : List Double -> Double
    lowerBound slopes = let n = length slopes in
                        at (clampIdx n $ (cast n - c) / 2 - 1) slopes

    upperBound : List Double -> Double
    upperBound slopes = let n = length slopes in
                        at (clampIdx n $ (cast n + c) / 2 + 1) slopes

--- Verdicts ---

||| The complexity expected of a subject, as an interval of exponents.
|||
||| These are range-local exponents, not asymptotic ones. For the expensive
||| generators the range affordable on CI stops well before the exponent
||| settles --- the investigation's section 7.4 shows `oneOf` with two
||| alternatives still climbing at n = 256 --- so each band is calibrated
||| against what the current implementation shows *over that subject's own
||| grid*, and the grid is pinned as part of the test.
public export
record Band where
  constructor MkBand
  lo, hi : Double

export
Interpolation Band where
  interpolate b = "[\{show b.lo}, \{show b.hi}]"

||| Widest interval we are still willing to draw a conclusion from: as wide as
||| the band it is being compared against, and no wider.
|||
||| Without a guard of this kind a measurement with no power at all would report
||| a pass, which is the standard way a performance gate rots into decoration.
||| Scaling it to the band rather than fixing it at a constant is what makes it a
||| statement about resolution: an interval as wide as the band is one where an
||| exponent sitting dead centre could still reach outside it, and where an
||| exponent a whole class away could still overlap it. Below that width, the
||| measurement resolves the exponent finely enough for the question being asked
||| --- and the question is narrower for the subjects whose reference exponent is
||| known more precisely, which is exactly when the band is narrow.
public export
resolution : Band -> Double
resolution b = (b.hi - b.lo) / 2

public export
data Verdict = AsExpected | Faster | Slower | TooNoisy

export
Interpolation Verdict where
  interpolate AsExpected = "ok"
  interpolate Faster     = "complexity class changed: faster than expected"
  interpolate Slower     = "complexity class changed: slower than expected"
  interpolate TooNoisy   = "inconclusive: interval too wide to decide"

||| A subject fails only when its interval lies wholly outside its band, that
||| is, only on positive evidence that the exponent moved. Noise widens the
||| interval, and a wide interval reports `TooNoisy`, never a change --- so this
||| suite cannot fail because a runner had a bad minute, only because the
||| complexity did change.
|||
||| Note that `Faster` fails too. An improvement is a change in documented
||| behaviour and has to be acknowledged by widening or moving the band, in the
||| same way a golden test has to be re-blessed.
export
verdictOf : Band -> Estimate -> Verdict
verdictOf band e = if e.halfWidth > resolution band then TooNoisy
                   else if e.upper < band.lo         then Faster
                   else if e.lower > band.hi         then Slower
                   else AsExpected
