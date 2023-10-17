module DerivedGen

import AlternativeCore
import PrintDerivation

%default total

%language ElabReflection

%runElab printDerived {core=Ext_XSS} $ Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty XSS
