module Test

import Data.Fin
import Shared

%language ElabReflection

%logging "deptycheck.derive.specialisation" 20
%logging "specialiseData.taskFormation" 20


%runElab do
  (Nothing, _) <- runSIN'' Nothing False `(List a)
    | _ => fail "List[0(a)] should not lead to specialisation!"
  pure ()
