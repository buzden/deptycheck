module Test

import Data.Fin
import Shared

%language ElabReflection

%logging "deptycheck.util.specialisation" 20


%runElab do
  (Just (_, ti), _) <- runSIN'' Nothing False `(List Nat)
    | _  => fail "Didn't generate a specialised type!"
  logMsg "" 0 $ show ti.name
  specNIIT <- getNamesInfoInTypes ti
  logMsg "" 0 $ show $ keys $ knownTypes
  runSIN (Just specNIIT) False `(List Nat)

-- specRes : Maybe (TTImp, TypeInfo)
-- specRes = %runElab runSIN' Nothing True `(List Nat)
--

-- specNIIT : NamesInfoInTypes
-- specNIIT = %runElab do
--   let Just (_, ti) = specRes
--     | _ => fail "Didn't find specialised type!"
--   getNamesInfoInTypes ti
--
-- %runElab runSIN (Just specNIIT) False `(List Nat)
