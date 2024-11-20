module UsePil

import Language.PilDyn

%default total

p1 : LinBlock [Just I, Nothing, Just B, Just I] [Nothing, Just I, Just B, Just B]
p1 = do
  3 #= Binary LT (Read 0) (Read 3)
  1 #= Binary Add (Read 0) 4
  End
