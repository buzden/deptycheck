module Infra

import public Data.Fuel

import public Test.DepTyCheck.Gen
import public Test.DepTyCheck.Gen.Auto.Core

import public Language.Reflection.Types

%default total

public export %inline
TestCaseData : Type
TestCaseData = (TTImp, Type)

public export %inline
TestCaseDesc : Type
TestCaseDesc = (String, TestCaseData)

export
chk : (ty : TypeInfo) -> List (Fin ty.args.length) -> Type -> TestCaseData
chk ty giv expr = (canonicSig ForSure (MkGenSignature ty $ fromList giv), Fuel -> expr)

export
caseVerdict : TestCaseDesc -> Elab String
caseVerdict (desc, given, expected) = do
  expected <- quote expected
  pure $ if (given == expected) @{UpToRenaming}
    then "\{desc}:\tOKAY"
    else """
         \{desc}:\tFAILED
           - given: \{given}
           - expected: \{expected}
         """

export
logCheck : String -> Elab ()
logCheck = \s => logMsg "gen.auto.canonic.check-sig" 0 s

export
checkAndLog : TestCaseDesc -> Elab ()
checkAndLog = logCheck <=< caseVerdict
