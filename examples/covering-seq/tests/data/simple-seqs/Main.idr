import Data.List.Covering

%default total

MaskIIII : BitMask ?
MaskIIII = [True, True, True, True]

x0123 : CoveringSequence ? MaskIIII
x0123 = Hit 0 $ Hit 1 $ Hit 2 $ Hit 3 $ End

x0123' : CoveringSequence ? MaskIIII
x0123' = Hit 0 $ Hit 1 $ Miss 20 $ Hit 2 $ Hit 3 $ Miss 30 $ End

x2301 : CoveringSequence ? MaskIIII
x2301 = Hit 2 $ Hit 3 $ Hit 0 $ Hit 1 $ End

x2301' : CoveringSequence ? MaskIIII
x2301' = Hit 2 $ Hit 3 $ Miss 20 $ Hit 0 $ Hit 1 $ Miss 30 $ End

failing "Can't find an implementation for AtIndex"
  x23012 : CoveringSequence ? MaskIIII
  x23012 = Hit 2 $ Hit 3 $ Hit 0 $ Hit 1 $ Hit 2 $ End

MaskIIOI : BitMask ?
MaskIIOI = [True, True, False, True]

x013 : CoveringSequence ? MaskIIOI
x013 = Hit 0 $ Hit 1 $ Hit 3 $ End

x103 : CoveringSequence ? MaskIIOI
x103 = Hit 1 $ Hit 0 $ Hit 3 $ End

failing "Can't find an implementation for AtIndex"
  badx0123 : CoveringSequence ? MaskIIOI
  badx0123 = Hit 0 $ Hit 1 $ Hit 2 $ Hit 3 $ End
