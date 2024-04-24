import Data.SortedBinTree

%default total

y : SortedBinTree1 ? ?
y = Node (Node (Leaf 0) (Leaf 1)) (Leaf 2)

failing "Can't find"
  y' : SortedBinTree1 ? ?
  y' = Node (Node (Leaf 1) (Leaf 1)) (Leaf 2)

--        .
--       / \
--      .   .
--     / \  |\
--    0   . 3 4
--       / \
--      1   2

x : SortedBinTree1 ? ?
x = Node
      (Node (Leaf 0) $ Node (Leaf 1) (Leaf 2))
      (Node (Leaf 3) (Leaf 4))
