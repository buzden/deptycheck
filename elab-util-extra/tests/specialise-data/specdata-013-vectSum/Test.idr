module Test

import Shared

%language ElabReflection

--- Currently, when one or more constructors return ?postpone during unification,
--- the corresponding specialised constructor is assumed to be nonexistent.
--- This is not the desired beaviour. Once we implement unifyManually and fording,
--- It should be possible to represent such constructors using condition auto-implicits.

%runElab specialiseData' "VectSum" $ \a,b => Vect (a + b) Nat

failing "x _ is not a valid impossible case."
  x : Vect (a + b) Nat -> Nat
  x _ impossible

y : VectSum a b -> Nat
y _ impossible

