import Data.SortedBinTree

%default total

y : SortedBinTree1 ? ?
y = NodeLR 1 (Leaf 0) (Leaf 2)

failing "Can't find"
  y' : SortedBinTree1 ? ?
  y' = NodeLR 1 (Leaf 1) (Leaf 2)

--        3
--       / \
--      1   4
--     / \
--    0   2

x : SortedBinTree1 ? ?
x = NodeLR 3 (NodeLR 1 (Leaf 0) (Leaf 2)) (Leaf 4)
