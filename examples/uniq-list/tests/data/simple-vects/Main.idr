import Data.Vect.Uniq

%default total

abcd : UniqStrVect 4
abcd = ["a", "b", "c", "d"]

failing "Mismatch between: 0 and 1"
  abc_4 : UniqStrVect 4
  abc_4 = ["a", "b", "c"]

failing "Mismatch between: S ?n and 0"
  abcde_4 : UniqStrVect 4
  abcde_4 = ["a", "b", "c", "d", "e"]

failing "Can't find an implementation"
  abdd : UniqStrVect 4
  abdd = ["a", "b", "d", "d"]

failing "Can't find an implementation"
  dbcd : UniqStrVect 4
  dbcd = ["d", "b", "c", "d"]
