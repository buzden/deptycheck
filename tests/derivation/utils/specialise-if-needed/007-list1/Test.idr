module Test

import Data.List1
import Data.Fin
import Shared

%language ElabReflection

%logging "deptycheck.derive.specialisation" 20
%logging "specialiseData.taskFormation" 20


%runElab do
  (_, _) <- runSIN'' Nothing False `(List1 Unit)
  pure ()
