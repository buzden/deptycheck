module Test

import Shared

%language ElabReflection

%runElab specialiseData' (List Nat) "ListNat"

ln0 : ListNat
ln0 = []

failing
  ln1 : ListNat
  ln1 = ["test"]

ln1 : ListNat
ln1 = [1]

ln10 : ListNat
ln10 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

lnCast1 : List Nat
lnCast1 = cast $ the ListNat [1,2,3,4,5]

lnCast1' : Test.lnCast1 = [1,2,3,4,5]
lnCast1' = Refl

lnCast2 : ListNat
lnCast2 = cast $ the (List Nat) [6,7,8,9,10]

lnCast2' : Test.lnCast2 = [6,7,8,9,10]
lnCast2' = Refl

lnDecEq1 : (decEq (the (List Nat) [1,2]) (the (List Nat) [3,4]) = No ?)
lnDecEq1 = Refl

lnDecEq2 :  (decEq (the (List Nat) [1,2]) (the (List Nat) [1,2])) = Yes Refl
lnDecEq2 = Refl

lnEq : ((the ListNat [1,2]) == (the ListNat [3,4])) = False
lnEq = Refl

lnEq' : ((the ListNat [1,2]) == (the ListNat [1,2])) = True
lnEq' = Refl

lnNEq : ((the ListNat [1,2]) /= (the ListNat [3,4])) = True
lnNEq = Refl

lnNEq' : ((the ListNat [1,2]) /= (the ListNat [1,2])) = False
lnNEq' = Refl

%runElab logMsg "" 0 $ show (the ListNat [1,2])

%runElab specialiseData' (List (List String)) "ListListString"

lss0 : ListListString
lss0 = []

lss1 : ListListString
lss1 = [["Hello world"]]

lssCast1 : List (List String)
lssCast1 = cast $ (the ListListString [["lol"]])

lssCast1' : Test.lssCast1 = [["lol"]]
lssCast1' = Refl

%runElab specialiseData' (List Type) "ListType"

lt : ListType
lt = [Nat, String]

failing
  ltDecEq : Dec (the ListType [Nat] = the ListType [String])
  ltDecEq = decEq (the ListType [Nat]) (the ListType [String])
