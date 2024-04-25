module UsePil

import Language.PilFun.DSL

%default total

StdF : Funs
StdF = [< [< Int', Int'] ==> Just Int'    -- "+"
       ,  [< Int', Int'] ==> Just Bool'   -- "<"
       ,  [< Int'] ==> Just Int'          -- "++"
       ,  [< Bool', Bool'] ==> Just Bool' -- "||"
       ,  [< Int' ] ==> Nothing           -- printf for ints
       ]
Plus, LT, Inc, Or : IndexIn StdF
Plus = 0; LT = 1; Inc = 2; Or = 3
Print : IndexIn StdF
Print = 4

program : Stmts StdF [<] 0 Nothing
program = do
  NewV Int' -- 0
  0 #= C 5
  NewV Int' -- 1
  NewV Bool' -- 2
  1 #= F Plus [< V 0, C 1]
  If (F LT [< F Inc [< V 0], V 1])
     (do 1 #= C 0
         2 #= C False
         Nop)
     (do NewV Int' -- 3
         3 #= F Plus [< V 0, V 1]
         NewV Bool' -- 4
         4 #= F LT [< V 0, C 5]
         2 #= F Or [< V 4, F LT [< V 3, C 6]]
         Nop)
  Call Print [< V 1]
  Nop

failing -- "Mismatch between: Int' and Bool'"
  bad : Stmts StdF [<] 0 Nothing
  bad = do
    NewV Int' -- 0
    0 #= C 5
    NewV Bool' -- 1
    1 #= F Plus [< V 0, C 1]
    Nop

failing -- "Mismatch between: [<] and [<Int']"
  bad : Stmts StdF [<] 0 Nothing
  bad = do
    NewV Int' -- 0
    0 #= C 5
    NewV Int' -- 1
    1 #= F Plus [< V 0]
    Nop

failing -- "Mismatch between: Bool' and Int'"
  bad : Stmts StdF [<] 0 Nothing
  bad = do
    NewV Int' -- 0
    0 #= C 5
    NewV Int' -- 1
    1 #= F Plus [< C True, V 0]
    Nop

failing #"Can't find an implementation for LTE 3 (length [<Int'])"#
  bad : Stmts StdF [<] 0 Nothing
  bad = do
    NewV Int' -- 0
    0 #= C 5
    2 #= V 0
    Nop

failing #"Can't find an implementation for LTE 3 (length [<Int'])"#
  bad : Stmts StdF [<] 0 Nothing
  bad = do
    NewV Int' -- 0
    0 #= V 2
    Nop
