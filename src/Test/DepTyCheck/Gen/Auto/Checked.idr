||| Internal generation functions, after user input checks
module Test.DepTyCheck.Gen.Auto.Checked

import public Language.Reflection.Types

import public Test.DepTyCheck.Gen.Auto.Util

%default total

-----------------------------------------------------
--- Data types for the safe signature formulation ---
-----------------------------------------------------

public export
data ArgExplicitness = ExplicitArg | ImplicitArg

public export
Eq ArgExplicitness where
  ExplicitArg == ExplicitArg = True
  ImplicitArg == ImplicitArg = True
  _ == _ = False

public export
data ExternalGenAccess = ThruAutoImplicit | ThruHint

------------------------------------------
--- The entry-point generator function ---
------------------------------------------

-- TODO maybe to use smth without constructors info instead of `TypeInfo` for the `externalGens` parameter.
export
generateGensFor : (ty : TypeInfo) ->
                  (givenParams : Vect ty.args.length $ Maybe ArgExplicitness) ->
                  (externalGens : List (TypeInfo, ExternalGenAccess)) ->
                  Elab ()
