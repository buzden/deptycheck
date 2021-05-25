module ValidateInput

import Test.DepTyCheck.Gen.Auto

%language ElabReflection

--------------------
--- Unknown type ---
--------------------

-- %runElab generateGensFor "X" [] []

----------------------------------
--- Known type, unknown givens ---
----------------------------------

--- Unknown named argument ---

data Y : Type -> Type -> Type where
  MkY : Y Int String

-- %runElab generateGensFor "Y" ["a"] []

--- Lacking positional argument (with no params in type) ---

data NoParam : Type where
  MkNoParam : NoParam

-- %runElab generateGensFor "NoParam" [0] []

--- Lacking positional argument (with existing parameters) ---

data TwoExplParams : Type -> Type -> Type where
  MkTwoExplParams : TwoExplParams a b

-- %runElab generateGensFor "TwoExplParams" [2, 0] []

-- Two errors
-- %runElab generateGensFor "TwoExplParams" [2, 3] []

--- Lacking explicit positional arguments ---

data TwoExplParamsWithImpl : Type -> Vect n a -> Type where
  MkTwoExplParamsWithImpl : TwoExplParamsWithImpl a v

-- %runElab generateGensFor "TwoExplParamsWithImpl" [2, 0] []

---------------------------------------------------
--- Known type, too many or incompatible givens ---
---------------------------------------------------

data TwoExplParamsWithImpl' : (b : Type) -> (v : Vect n a) -> Type where
  MkTwoExplParamsWithImpl' : TwoExplParamsWithImpl' a v

--- Repeating implicit givens ---

-- %runElab generateGensFor "TwoExplParamsWithImpl" [0, 1, 1] []
-- %runElab generateGensFor "TwoExplParamsWithImpl'" [0, "v", 1] []

--- Repeating explciit givens ---

-- %runElab generateGensFor "TwoExplParamsWithImpl" [] [0, 1, 1]
-- %runElab generateGensFor "TwoExplParamsWithImpl'" [] [0, 1, "v"]

--- Repeating both implicit and explicit givens ---

-- %runElab generateGensFor "TwoExplParamsWithImpl" [1, 1] [0, 0]
-- %runElab generateGensFor "TwoExplParamsWithImpl'" [1, "v"] ["b", 0]

--- Existence of a given which is both implicit and explicit ---

-- %runElab generateGensFor "TwoExplParamsWithImpl" [1] [0, 1]
-- %runElab generateGensFor "TwoExplParamsWithImpl'" ["v"] [0, 1]
