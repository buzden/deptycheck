module Test

import Shared

%language ElabReflection

%runElab specialiseDataLam' "MyVoid" Void

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e0' = %runElab verifyEmptyType Void MyVoid
