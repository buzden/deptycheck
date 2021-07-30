module Test.DepTyCheck.Gen.Auto.Checked

import public Language.Reflection.Types

import public Test.DepTyCheck.Gen.Auto.Util

%default total

--------------------------------------------------------------
--- Internal generation functions, after user input checks ---
--------------------------------------------------------------

public export
data PresenceAtSignature = NotPresent | ExplicitArg | ImplicitArg

public export
Eq PresenceAtSignature where
  NotPresent  == NotPresent  = True
  ExplicitArg == ExplicitArg = True
  ImplicitArg == ImplicitArg = True
  _ == _ = False

public export
data ExternalGenAccess = ThruImplicit | ThruHint

export
generateGensFor : (ty : TypeInfo) ->
                  (givenParams : Vect ty.args.length PresenceAtSignature) ->
                  (externalGens : List (TypeInfo, ExternalGenAccess)) -> -- todo maybe to use smth without constructors info instead of `TypeInfo`.
                  Elab ()
