module Test

import Deriving.DepTyCheck.Util.Reflection

%default total

---------------------------
-- Check some basic case --
---------------------------

S_name : Name
S_name = `{S}.dataCon

S_name_corr : S_name = `{Prelude.Types.S}
S_name_corr = Refl

-- Using string literal for `Name` from `elab-util`
S_name' : Name
S_name' = "S".dataCon

S_name'_corr : S_name' = `{Prelude.Types.S}
S_name'_corr = Refl

-------------------------------------------------------------------
-- Check that ambiguous constructors lead to a compilation error --
-------------------------------------------------------------------

failing "Ambiguous data constructors"
  Cons_name : Name
  Cons_name = `{(::)}.dataCon

---------------------------------------------------------------
-- Check that a function nearby does not distract the search --
---------------------------------------------------------------

S : String -> String
S = (++ "haha")

S_name'' : Name
S_name'' = `{S}.dataCon

S_name''_corr : S_name'' = `{Prelude.Types.S}
S_name''_corr = Refl

-----------------------------------------------------------
-- Check that a type nearby does not distract the search --
-----------------------------------------------------------

namespace STypeCon

  export
  data S : Nat -> Type where
    MkS : Nat -> S 5

S_name''' : Name
S_name''' = `{S}.dataCon

S_name'''_corr : S_name''' = `{Prelude.Types.S}
S_name'''_corr = Refl

---------------------------------------------------------------------
-- Check that another data constructor nearby distracts the search --
---------------------------------------------------------------------

namespace AnotherSDataCon
  data ATy : Nat -> Type where
    S : Nat -> ATy 5

  failing "Ambiguous data constructors"
    Bad_S : Name
    Bad_S = `{S}.dataCon

--------------------------------------------------------------------------
-- Check that non-visible data constructor does not distract the search --
--------------------------------------------------------------------------

S_name'''' : Name
S_name'''' = `{S}.dataCon

S_name''''_corr : S_name'''' = `{Prelude.Types.S}
S_name''''_corr = Refl
