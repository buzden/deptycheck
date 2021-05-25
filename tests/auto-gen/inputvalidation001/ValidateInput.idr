module ValidateInput

import Test.DepTyCheck.Gen.Auto

%language ElabReflection

--------------------
--- Unknown type ---
--------------------

-- %runElab generateGensFor "X" [] [] [] []

----------------------------------
--- Known type, unknown givens ---
----------------------------------

--- Unknown named argument ---

data Y : Type -> Type -> Type where
  MkY : Y Int String

-- %runElab generateGensFor "Y" ["a"] [] [] []

--- Lacking positional argument (with no params in type) ---

data NoParam : Type where
  MkNoParam : NoParam

-- %runElab generateGensFor "NoParam" [0] [] [] []

--- Lacking positional argument (with existing parameters) ---

data TwoExplParams : Type -> Type -> Type where
  MkTwoExplParams : TwoExplParams a b

-- %runElab generateGensFor "TwoExplParams" [2, 0] [] [] []

-- Two errors
-- %runElab generateGensFor "TwoExplParams" [2, 3] [] [] []

--- Lacking explicit positional arguments ---

data TwoExplParamsWithImpl : Type -> Vect n a -> Type where
  MkTwoExplParamsWithImpl : TwoExplParamsWithImpl a v

-- %runElab generateGensFor "TwoExplParamsWithImpl" [2, 0] [] [] []
