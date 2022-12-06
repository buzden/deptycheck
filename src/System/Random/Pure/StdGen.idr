module System.Random.Pure.StdGen

import System
import public System.Random.Pure

import Data.Bits

%default total

export
data StdGen = MkStdGen BaseGenTy BaseGenTy

export
someStdGen : StdGen
someStdGen = MkStdGen 23462 254334222987

export
Show StdGen where
  show (MkStdGen i j) = "MkStdGen " ++ show i ++ " " ++ show j

-- Based on a port of QuickCheck to Idris 1, which in its turn based on some translation of Haskell code
export
RandomGen StdGen where
  next (MkStdGen s1 s2) =
    let k : BaseGenTy = s1 `div` 53668 in
    let s1' : BaseGenTy  = 40014 * (s1 - k * 53668) - k * 12211 in
    let s1'' : BaseGenTy = if s1' < 0 then s1' + 2147483563 else s1' in
    let k' : BaseGenTy = s2 `div` 52774 in
    let s2' : BaseGenTy = 40692 * (s2 - k' * 52774) - k' * 3791 in
    let s2'' : BaseGenTy = if s2' <= 0 then s2' + 2147483399 else s2' in
    let z : BaseGenTy = s1'' - s2'' in
    let z' : BaseGenTy = if z < 1 then z + 2147483562 else z in
    (MkStdGen s1'' s2'', z')

  genRange _ = (0, 2147483562)
  split (MkStdGen s1 s2) =
    let gen' : StdGen = fst (next (MkStdGen s1 s2)) in
    let t1 : BaseGenTy = case gen' of { MkStdGen a b => a } in
    let t2 : BaseGenTy = case gen' of { MkStdGen a b => b } in
    let new_s1 : BaseGenTy = if s1 >= 2147483562 || s1 < 1
                         then 1
                         else s1 + 1 in
    let new_s2 : BaseGenTy = if s2 <= 1 || s2 >= 2147483398
                         then 2147483398
                         else s2 - 1 in
    let left : StdGen = MkStdGen (new_s1 - 1) t2 in
    let right : StdGen = MkStdGen t1 (new_s2 + 1) in
    (left, right)

-- The following function contains translation from the Haskell code taken from
-- https://hackage.haskell.org/package/splitmix-0.1.0.4/docs/src/System.Random.SplitMix.html
export
mkStdGen : BaseGenTy -> StdGen
mkStdGen s = MkStdGen (mix64 s) (mixGamma (s + goldenGamma)) where

  goldenGamma : BaseGenTy
  goldenGamma = 0x9e3779b97f4a7c15

  shiftXor : Index {a=BaseGenTy} -> BaseGenTy -> BaseGenTy
  shiftXor n w = w `xor` (w `shiftR` n)

  shiftXorMultiply : Index {a=BaseGenTy} -> BaseGenTy -> BaseGenTy -> BaseGenTy
  shiftXorMultiply n k w = shiftXor n w * k

  mix64, mix64v13 : BaseGenTy -> BaseGenTy
  mix64    = shiftXor 33 . shiftXorMultiply 33 0xc4ceb9fe1a85ec53 . shiftXorMultiply 33 0xff51afd7ed558ccd
  mix64v13 = shiftXor 31 . shiftXorMultiply 27 0x94d049bb133111eb . shiftXorMultiply 30 0xbf58476d1ce4e5b9

  mixGamma : BaseGenTy -> BaseGenTy
  mixGamma z0 = do
    let z1 = mix64v13 z0 .|. 1             -- force to be odd
        n  = popCount $ z1 `xor` (z1 `shiftR` 1)
    -- see: http://www.pcg-random.org/posts/bugs-in-splitmix.html
    -- let's trust the text of the paper, not the code.
    if n >= 24
      then z1
      else z1 `xor` 0xaaaaaaaaaaaaaaaa

export
initStdGen : HasIO io => io StdGen
initStdGen = mkStdGen <$> aSeed where
  aSeed : io BaseGenTy
  aSeed = pure $ cast !time `xor` cast !getPID
