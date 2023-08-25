module Infra

import public TypesAndInvolved

import Data.Vect.Extra

import Deriving.DepTyCheck.Gen.Core.Util

%language ElabReflection

printInvolvedTypesVerdict : Name -> List Name -> Elab Unit
printInvolvedTypesVerdict tyName expected = do
  logMsg "gen.auto.involved-types" 0 "given type: \{show tyName}"
  invTys <- allInvolvedTypes !(getInfo' tyName)
  let invTys   = sortBy (comparing show) $ invTys <&> name
  expected <- for expected $ map name . getInfo'
  let expected = sortBy (comparing show) expected
  when (invTys /= expected) $ do
    logMsg "gen.auto.involved-types" 0 "-------- !!! --------"
    logMsg "gen.auto.involved-types" 0 "found   : \{show invTys}"
    logMsg "gen.auto.involved-types" 0 "expected: \{show expected}"

%runElab for_ typesAndInvolved $ uncurry printInvolvedTypesVerdict
