module System.Random.Pure.StdGen

import public System.Random.Pure

%default total

export
data StdGen = MkStdGen BaseGenTy BaseGenTy

export
someStdGen : StdGen
someStdGen = MkStdGen 23462 254334222987

export
Show StdGen where
  show (MkStdGen i j) = "MkStdGen " ++ show i ++ " " ++ show j

-- Blatantly stolen from Haskell
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
