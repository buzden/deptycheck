module Positive

import Example.Pil.Lang

import Common

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

-- Registers-related --

read_reg_base : Statement vars (Base [Nothing, Nothing, Just Int', Nothing]) vars (Base [Nothing, Nothing, Just Int', Nothing])
read_reg_base = block $ do
  Int'. "x" !#= R 2

read_reg_undef_with : Statement vars (AllUndefined {rc=4} `With` (3, Just Int'))
                                vars (AllUndefined {rc=4} `With` (3, Just Int'))
read_reg_undef_with = block $ do
  Int'. "x" !#= R 3

read_reg_with : {0 regs : Registers 5} -> Statement vars (regs `With` (3, Just Int')) vars (regs `With` (3, Just Int'))
read_reg_with = block $ do
  Int'. "x" !#= R 3 + C 0

registers_ass : {0 regs : Registers 5} -> Statement vars regs vars $ regs `With` (3, Just Int')
registers_ass = block $ do
  Int'. "x" !#= C 0
  3 %= V "x"

registers_multiple_ass : {0 regs : Registers 5} ->
                         Statement vars regs vars $ ((regs `With` (3, Just Bool')) `With` (3, Just Int')) `With` (3, Just String')
registers_multiple_ass = do
  3 %= C False
  3 %= C 42
  3 %= C "foo"

-- Basic if tests

if_local_vars : {cond : Expression (("x", Int')::vars) regs Bool'} -> Statement vars regs vars $ regs `Merge` regs
if_local_vars = block $ do
  Int'. "x" !#= C 0
  if__ cond (String'. "x" !#= C "foo") (Bool'. "x" !#= C True)
  "x" #= C 42

-- Registers are correctly merged in if clauses --

if_merge_two_branches : {0 regs : Registers 3} -> {cond : Expression vars regs Bool'} ->
                        Statement vars regs (("x", Int')::vars) $ (regs `With` (1, Just Int')) `Merge` (regs `With` (1, Just Int'))
if_merge_two_branches = do
    if__ cond thenBranch elseBranch
    Int' . "x" !#= R 1
  where
    thenBranch : Statement vars regs vars $ regs `With` (1, Just Int')
    thenBranch = do
      1 %= C 1
    elseBranch : Statement vars regs vars $ regs `With` (1, Just Int')
    elseBranch = do
      1 %= C 1

if_merge_two_branches' : {0 regs : Registers 3} -> {cond : Expression vars regs Bool'} -> Exists2 $ Statement vars regs
if_merge_two_branches' = Evidence2 _ _ $ do
    if__ cond
      (1 %= C 1)
      (1 %= C 2)
    Int' . "x" !#= R 1

if_merge_one_branch : {0 regs : Registers 3} -> {cond : Expression (("x", Int')::vars) (regs `With` (1, Just Int')) Bool'} ->
                      Statement
                        vars
                        regs
                        (("x", Int')::vars)
                        ((regs `With` (1, Just Int')) `Merge` ((regs `With` (1, Just Int')) `With` (1, Just Int')))
if_merge_one_branch = do
  Int' . "x" !#= C 1
  1 %= C 2
  if__ cond ("x" #= C 3) (1 %= C 4)
  "x" #= R 1
