module Negative

import Example.Pil.Lang

import Common
import Positive -- this import insures that negative tests would compile after positive

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
