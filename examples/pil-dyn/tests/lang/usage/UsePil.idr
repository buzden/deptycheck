module UsePil

import Language.PilDyn

%default total

p1 : LinBlock [Just I, Nothing, Just B, Just I] [Nothing, Just I, Just B, Just B]
p1 = do
  3 #= Binary (Read 0) LTE (Read 3)
  1 #= Binary (Read 0) Add 4
  End
