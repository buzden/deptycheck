module CanonicSigCheck

import public Infra

%default total

%language ElabReflection

data Y = Y0 | Y1

cases : List TestCaseDesc
cases = [ ("trivial type; no givens",) $ chk (getInfo "Y") [] $ Gen Y
        ]

%runElab for_ cases checkAndLog
