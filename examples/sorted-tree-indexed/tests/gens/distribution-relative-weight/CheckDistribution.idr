module CheckDistribution

import Data.DPair
import Data.SortedBinTree.Gen

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

%language ElabReflection

-- Check how weights of subtrees are related between left and right subtree of a root

getLR : (mi ** ma ** SortedBinTree1 mi ma) -> Maybe $ let t = Exists $ Exists . SortedBinTree1 in (t, t)
getLR (_ ** _ ** Leaf {}) = Nothing
getLR (_ ** _ ** Node l r) = Just (Evidence _ $ Evidence _ l, Evidence _ $ Evidence _ r)

mainFor : (depth : Nat) -> IO ()
mainFor depth = printVerdict' getLR (genSortedBinTree1 $ limit depth) $ fromList
                  $ [ coverWith 1 (\(l, r) => weight l.snd.snd `f` weight r.snd.snd)
                    | (r, f) <-
                      [ (ratio 1 2, (>))
                      , (ratio 1 10, (==))
                      , (ratio 1 2, (<))
                      ]
                    ]

main : IO ()
main = do
  mainFor 2
  mainFor 4
  mainFor 6
