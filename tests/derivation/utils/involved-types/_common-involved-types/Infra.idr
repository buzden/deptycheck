module Infra

import public TypesAndInvolved

import Deriving.DepTyCheck.Gen.Core.Util

%language ElabReflection

printInvolvedTypesVerdict : Name -> Count -> List Name -> Elab Unit
printInvolvedTypesVerdict tyName minRig expected = do
  logMsg "deptycheck.involved-types" 0 "given type: \{show tyName}"
  invTys <- allInvolvedTypes minRig !(getInfo' tyName)
  let invTys   = sortBy (comparing show) $ invTys <&> name
  expected <- for expected $ map TypeInfo.name . getInfo'
  let expected = sortBy (comparing show) expected
  when (invTys /= expected) $ do
    logMsg "deptycheck.involved-types" 0 "-------- !!! --------"
    logMsg "deptycheck.involved-types" 0 "found   : \{show invTys}"
    logMsg "deptycheck.involved-types" 0 "expected: \{show expected}"

%runElab for_ typesAndInvolved $ \(n, r, ns) => printInvolvedTypesVerdict n r ns
