module ListVectNat

import Shared

%language ElabReflection

%runElab specialiseData' (\a => List $ Vect a Nat) "ListVectNat"

lvn0 : ListVectNat 0
lvn0 = Nil 0

lvn1 : ListVectNat 0
lvn1 = (::) 0 [] []

lvn2 : ListVectNat 1
lvn2 = (::) 1 [1] [[2]]

lvnCast0 : List $ Vect 1 Nat
lvnCast0 = cast $ (::) 1 [1] [[2]]

lvnCast0' : ListVectNat.lvnCast0 = [[1], [2]]
lvnCast0' = Refl

lvnCast1 : ListVectNat 1
lvnCast1 = cast $ the (List (Vect 1 Nat)) [[1], [2]]

lvnCast1' : ListVectNat.lvnCast1 = (::) 1 [1] [[2]]
lvnCast1' = Refl

lvnEq0 : decEq (Nil 0) (Nil 0) = Yes ?
lvnEq0 = Refl

lvnEq1 : decEq (Nil 0) ((::) 0 [] []) = No ?
lvnEq1 = Refl

lvnEq2 : decEq ((::) 1 [1] [[2]]) ((::) 1 [1] []) = No ?
lvnEq2 = Refl

lvnEq3 : decEq ((::) 1 [1] [[2]]) ((::) 1 [1] [[2]]) = Yes ?
lvnEq3 = Refl

lvnFinEq0 : (Nil 5 == Nil 5) = True
lvnFinEq0 = Refl

lvnFinEq1 : (Nil 1 == (::) 1 [1] []) = False
lvnFinEq1 = Refl

lvnFinEq2 : ((::) 1 [2] [] == (::) 1 [1] []) = False
lvnFinEq2 = Refl

lvnFinEq3 : ((::) 1 [2] [] == (::) 1 [2] []) = True
lvnFinEq3 = Refl

lvnFinNEq0 : (Nil 5 /= Nil 5) = False
lvnFinNEq0 = Refl

lvnFinNEq1 : (Nil 1 /= (::) 1 [1] []) = True
lvnFinNEq1 = Refl

lvnFinNEq2 : ((::) 1 [2] [] /= (::) 1 [1] []) = True
lvnFinNEq2 = Refl

lvnFinNEq3 : ((::) 1 [2] [] /= (::) 1 [2] []) = False
lvnFinNEq3 = Refl


%runElab logMsg "" 0 $ show $ Nil 10
%runElab logMsg "" 0 $ show $ ListVectNat.(::) 2 [1,2] [[3,4], [5,6]]

