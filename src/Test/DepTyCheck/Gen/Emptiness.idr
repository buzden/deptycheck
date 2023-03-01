module Test.DepTyCheck.Gen.Emptiness

import public Language.Implicits.IfUnsolved

%default total

public export
data Depth = Static | Dynamic

public export
data Emptiness = NonEmpty | CanBeEmpty Depth

public export
data Relaxable : (from, to : Emptiness) -> Type where
  Drought  : Relaxable em em
  CanEmpty : Relaxable NonEmpty (CanBeEmpty dp)

public export
data CanBeInAlternatives : Emptiness -> Type where
  AltNE : CanBeInAlternatives NonEmpty
  AltDE : CanBeInAlternatives (CanBeEmpty Dynamic)

public export
data BindToOuter : (emOfBind, outerEm : Emptiness) -> Type where
  BndNE : BindToOuter NonEmpty NonEmpty
  BndEE : (0 _ : IfUnsolved em Dynamic) =>
          (0 _ : IfUnsolved iem Dynamic) =>
          BindToOuter (CanBeEmpty iem) (CanBeEmpty em)
