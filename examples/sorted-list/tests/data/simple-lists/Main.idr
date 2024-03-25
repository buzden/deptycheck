import Data.List.Sorted

%default total

x0123 : SortedList
x0123 = [0, 1, 2, 3]

x01230 : SortedList
x01230 = [0, 1, 2, 30]

failing "Can't find an implementation for AllGT 10 [1, 2, 30]"
  x101230 : SortedList
  x101230 = [10, 1, 2, 30]

failing "Can't find an implementation for AllGT 1 [1, 2, 30]"
  x11230 : SortedList
  x11230 = [1, 1, 2, 30]
