module Example.Pil.ExampleUsages

import Example.Pil.Lang

-------------------------
--- Examples of usage ---
-------------------------

--- Functions lifted to the expression level ---

export %inline
(+) : Expression vars regs Int' -> Expression vars regs Int' -> Expression vars regs Int'
(+) = B (+) {opName="+"}

export %inline
div : Expression vars regs Int' -> Expression vars regs Int' -> Expression vars regs Int'
div = B div {opName="/"}

export %inline
mod : Expression vars regs Int' -> Expression vars regs Int' -> Expression vars regs Int'
mod = B mod {opName="%"}

export %inline
(<) : Expression vars regs Int' -> Expression vars regs Int' -> Expression vars regs Bool'
(<) = B (<) {opName="<"}

export %inline
(>) : Expression vars regs Int' -> Expression vars regs Int' -> Expression vars regs Bool'
(>) = B (>) {opName=">"}

export %inline
(==) : Eq (idrTypeOf a) => Expression vars regs a -> Expression vars regs a -> Expression vars regs Bool'
(==) = B (==) {opName="=="}

export %inline
(/=) : Eq (idrTypeOf a) => Expression vars regs a -> Expression vars regs a -> Expression vars regs Bool'
(/=) = B (/=) {opName="!="}

export %inline
(&&) : Expression vars regs Bool' -> Expression vars regs Bool' -> Expression vars regs Bool'
(&&) = B (\a, b => a && b) {opName="&&"} -- recoded because of laziness

export %inline
(++) : Expression vars regs String' -> Expression vars regs String' -> Expression vars regs String'
(++) = B (++) {opName="??concat??"}

export %inline
show : Show (idrTypeOf ty) => Expression vars regs ty -> Expression vars regs String'
show = U show {opName="toString"}

--- Example statements ---

simple_ass : Statement vars regs (("x", Int')::vars) regs
simple_ass = do
  Int'. "x"
  "x" #= C 2

lost_block : Statement vars regs vars regs
lost_block = do
  block $ do
    Int'. "x"
    "x" #= C 2
    Int'. "y" !#= V "x"
    Int'. "z" !#= C 3
    print $ V "y" + V "z" + V "x"

some_for : Statement vars regs vars regs
some_for = for (do Int'. "x" !#= C 0; Int'. "y" !#= C 0) (V "x" < C 5 && V "y" < C 10) ("x" #= V "x" + C 1) $ do
             "y" #= V "y" + V "x" + C 1

--bad_for : Statement vars regs vars regs
--bad_for = for (do Int'. "x" #= C 0; Int'. "y" #= C 0)
--                (V "y")
--                  ("x" #= V "x" + C 1) $ do
--             "y" #= V "y" `div` V "x" + C 1

euc : {0 vars : Variables} -> {0 regs : Registers rc} -> let c = ("a", Int')::("b", Int')::vars in Statement c regs (("res", Int')::c) regs
euc = do
  while (V "a" /= C 0 && V "b" /= C 0) $ do
    if__ (V "a" > V "b")
      ("a" #= V "a" `mod` V "b")
      ("b" #= V "b" `mod` V "a")
  Int'. "res" !#= V "a" + V "b"

name_shadowing : Statement vars regs vars regs
name_shadowing = block $ do
  Int'. "x" !#= C 0
  block $ do
    Int'. "x" !#= C 3
    Int'. "y" !#= V "x" + C 2
    String'. "x" !#= C "foo"
    print $ V "x" ++ C "bar" ++ show (V "y")
  Int'. "z" !#= V "x" + C 2
