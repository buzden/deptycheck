import Data.List.Uniq

%default total

abcd : UniqStrList
abcd = ["a", "b", "c", "d"]

failing "Can't find an implementation"
  abdd : UniqStrList
  abdd = ["a", "b", "d", "d"]

failing "Can't find an implementation"
  dbcd : UniqStrList
  dbcd = ["d", "b", "c", "d"]
