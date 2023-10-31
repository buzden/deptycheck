import Data.SortedBinTree

%default total

y : SortedBinTree
y = Node 1 (Leaf 0) (Leaf 2)

failing "Can't find"
  y' : SortedBinTree
  y' = Node 1 (Leaf 1) (Leaf 2)

--        3
--       / \
--      1   4
--     / \
--    0   2

x : SortedBinTree
x = Node 3 (Node 1 (Leaf 0) (Leaf 2)) (Leaf 4)
