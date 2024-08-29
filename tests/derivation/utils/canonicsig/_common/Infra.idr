module Infra

import public Data.Fuel

import public Deriving.DepTyCheck.Gen.Core

import public Test.DepTyCheck.Gen

import public Language.Reflection.Compat

%default total

public export %inline
TestCaseData : Type
TestCaseData = (TTImp, Type)

public export %inline
TestCaseDesc : Type
TestCaseDesc = (String, TestCaseData)

%hint %macro
ATAN : {ty : _} -> Elab $ AllTyArgsNamed ty
ATAN = ensureTyArgsNamed ty

export
chk : (ty : TypeInfo) -> (0 _ : AllTyArgsNamed ty) => List (Fin ty.tyArgs.length) -> Type -> TestCaseData
chk ty giv expr = (canonicSig (MkGenSignature ty $ fromList giv), Fuel -> expr)

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
logCheck = \s => logMsg "deptycheck.canonic.check-sig" 0 s

export
checkAndLog : TestCaseDesc -> Elab ()
checkAndLog = logCheck <=< caseVerdict
