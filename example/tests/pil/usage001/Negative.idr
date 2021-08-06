module Negative

import Example.Pil.Lang

import Common
import Positive -- this import insures that negative tests would compile after positive

-- Simple tests --

bad_ass_no_var : Statement vars regs vars regs
bad_ass_no_var = do
  "x" #= C 42

bad_ass_type_mismatch : Statement vars regs (("x", Int')::vars) regs
bad_ass_type_mismatch = do
  Int'. "x"
  "x" #= C "foo"

bad_ass_var_to_var_type_mismatch : Statement vars regs (("y", Bool')::("x", Int')::vars) regs
bad_ass_var_to_var_type_mismatch = do
  Int'. "x"
  "x" #= C 42
  Bool'. "y"
  "y" #= V "x"

bad_block_local_vars : Statement vars regs vars regs
bad_block_local_vars = do
  block $ do
    Int'. "x"
  "x" #= C 1

--- Example statements ---

bad_for : Statement vars regs vars regs
bad_for = for (do Int'. "x" #= C 0; Int'. "y" #= C 0)
                (V "y")
                  ("x" #= V "x" + C 1) $ do
             "y" #= V "y" `div` V "x" + C 1

-- Registers-related --

bad_read_reg_base : Statement vars (Base [Nothing, Nothing, Just Int', Nothing]) vars (Base [Nothing, Nothing, Just Int', Nothing])
bad_read_reg_base = block $ do
  Int'. "x" !#= R 1

bad_read_reg_undef_with : Statement vars (AllUndefined {rc=4} `With` (3, Just Int'))
                                    vars (AllUndefined {rc=4} `With` (3, Just Int'))
bad_read_reg_undef_with = block $ do
  Int'. "x" !#= R 2

bad_read_reg_with : {0 regs : Registers 5} -> Statement vars (regs `With` (3, Just Int')) vars (regs `With` (3, Just Int'))
bad_read_reg_with = block $ do
  Int'. "x" !#= R 2 + C 0

bad_registers_ass : {0 regs : Registers 5} -> Statement vars regs vars $ regs `With` (3, Just Int')
bad_registers_ass = block $ do
  Int'. "x" !#= C 0
  6 %= V "x"

-- Basic if statement tests --

bad_if_access_local : {cond : Expression vars regs Bool'} -> Statement vars regs vars $ regs `Merge` regs
bad_if_access_local = block $ do
  if__ cond (Int'. "x" !#= C 1) (Int'. "x" !#= C 2)
  Int'. "y" !#= V "x"

-- Registers are correctly merged in if clauses --

bad_if_taints_register : {0 regs : Registers 5} -> {cond : Expression vars (regs `With` (3, Just Int')) Bool'} -> Statement vars regs vars $ ((regs `With` (3, Just Int')) `With` (3, Just Int')) `Merge` ((regs `With` (3, Just Int')) `With` (3, Just Bool'))
bad_if_taints_register = block $ do
  3 %= C 1
  if__ cond (3 %= C 2) (3 %= C True)
  Int'. "x" !#= R 3

bad_if_single_branch_taint : {0 regs : Registers 5} -> {cond : Expression vars (regs `With` (3, Just Int')) Bool'} -> Statement vars regs vars $ ((regs `With` (3, Just Int')) `With` (3, Just String')) `Merge` (regs `With` (3, Just Int'))
bad_if_single_branch_taint = block $ do
  3 %= C 1
  if__ cond (3 %= C "foo") nop
  Int' . "x" !#= R 3
