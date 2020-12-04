module Example.Pil.ExampleUsages

import Example.Pil.Lang

-------------------------
--- Examples of usage ---
-------------------------

--- Functions lifted to the expression level ---

export %inline
(+) : Expression ctx Int' -> Expression ctx Int' -> Expression ctx Int'
(+) = B (+) {opName="+"}

export %inline
div : Expression ctx Int' -> Expression ctx Int' -> Expression ctx Int'
div = B div {opName="/"}

export %inline
mod : Expression ctx Int' -> Expression ctx Int' -> Expression ctx Int'
mod = B mod {opName="%"}

export %inline
(<) : Expression ctx Int' -> Expression ctx Int' -> Expression ctx Bool'
(<) = B (<) {opName="<"}

export %inline
(>) : Expression ctx Int' -> Expression ctx Int' -> Expression ctx Bool'
(>) = B (>) {opName=">"}

export %inline
(==) : Eq (idrTypeOf a) => Expression ctx a -> Expression ctx a -> Expression ctx Bool'
(==) = B (==) {opName="=="}

export %inline
(/=) : Eq (idrTypeOf a) => Expression ctx a -> Expression ctx a -> Expression ctx Bool'
(/=) = B (/=) {opName="!="}

export %inline
(&&) : Expression ctx Bool' -> Expression ctx Bool' -> Expression ctx Bool'
(&&) = B (\a, b => a && b) {opName="&&"} -- recoded because of laziness

export %inline
(++) : Expression ctx String' -> Expression ctx String' -> Expression ctx String'
(++) = B (++) {opName="??concat??"}

export %inline
show : Show (idrTypeOf ty) => Expression ctx ty -> Expression ctx String'
show = U show {opName="toString"}

--- Example statements ---

simple_ass : Statement ctx $ ("x", Int')::ctx
simple_ass = do
  Int'. "x"
  "x" #= C 2

lost_block : Statement ctx ctx
lost_block = do
  block $ do
    Int'. "x"
    "x" #= C 2
    Int'. "y" #= V "x"
    Int'. "z" #= C 3
    print $ V "y" + V "z" + V "x"

some_for : Statement ctx ctx
some_for = for (do Int'. "x" #= C 0; Int'. "y" #= C 0) (V "x" < C 5 && V "y" < C 10) ("x" #= V "x" + C 1) $ do
             "y" #= V "y" + V "x" + C 1

--bad_for : Statement ctx ctx
--bad_for = for (do Int'. "x" #= C 0; Int'. "y" #= C 0)
--                (V "y")
--                  ("x" #= V "x" + C 1) $ do
--             "y" #= V "y" `div` V "x" + C 1

euc : {0 ctx : Context} -> let c = ("a", Int')::("b", Int')::ctx in Statement c $ ("res", Int')::c
euc = do
  while (V "a" /= C 0 && V "b" /= C 0) $ do
    if__ (V "a" > V "b")
      ("a" #= V "a" `mod` V "b")
      ("b" #= V "b" `mod` V "a")
  Int'. "res" #= V "a" + V "b"

name_shadowing : Statement ctx ctx
name_shadowing = block $ do
  Int'. "x" #= C 0
  block $ do
    Int'. "x" #= C 3
    Int'. "y" #= V "x" + C 2
    String'. "x" #= C "foo"
    print $ V "x" ++ C "bar" ++ show (V "y")
  Int'. "z" #= V "x" + C 2
