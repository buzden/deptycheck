module Infra

import public Data.Fuel

import public Debug.Reflection

import public Test.DepTyCheck.Gen
import public Test.DepTyCheck.Gen.Auto.Derive

import public Language.Reflection.Types

%default total

export
Eq TTImp where
  -- The following is a non-complete trick, dealing with the fact that unnamed arguments are named after compler's check for being `Type`
  -- It works only for the top-level `Pi` type and only when `Pi` type is on the top level.
  IPi _ MW ExplicitArg Nothing argTy retTy == IPi _ MW ExplicitArg (Just $ MN _ _) argTy' retTy' = argTy == argTy' && retTy == retTy'
  x == y = show x == show y

public export %inline
TestCaseData : Type
TestCaseData = (TTImp, Type)

public export %inline
TestCaseDesc : Type
TestCaseDesc = (String, TestCaseData)

export
chk : (ty : TypeInfo) -> List (Fin ty.args.length) -> Type -> TestCaseData
chk ty giv expr = (canonicSig (MkGenSignature ty $ fromList giv), Fuel -> expr)

export
caseVerdict : TestCaseDesc -> Elab String
caseVerdict (desc, given, expected) = do
  expected <- quote expected
  pure $ if given == expected
    then "\{desc}:\tOKAY"
    else """
         \{desc}:\tFAILED
           - given: \{show given}
           - expected: \{show expected}
         """

export
logCheck : String -> Elab ()
logCheck = \s => logMsg "gen.auto.canonic.check-sig" 0 s

export
checkAndLog : TestCaseDesc -> Elab ()
checkAndLog = logCheck <=< caseVerdict
