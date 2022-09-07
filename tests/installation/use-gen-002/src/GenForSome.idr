module GenForSome

import Decidable.Equality

import Data.Fuel
import Data.List.Quantifiers
import Data.So

import Test.DepTyCheck.Gen

%default total

public export
Name : Type
Name = String

public export
data Stmt : (definedPre : List Name) -> (definedAfter : List Name) -> Type where
  Define : (new : Name) -> All (\def => So $ def /= new) defined => Stmt defined (new :: defined)
  Use    : (usd : Name) -> Any (\def => So $ def == usd) defined => Stmt defined defined
  Chain  : Stmt pre mid -> Stmt mid post -> Stmt pre post

data Stmt' : (defined : List Name) -> Type where
  Define' : (pre : Stmt' defined) -> (new : Name) -> All (\def => So $ def /= new) defined => Stmt' (new :: defined)
  Use'    : (pre : Stmt' defined) -> (usd : Name) -> Any (\def => So $ def == usd) defined => Stmt' defined

-- So (elem x list) <-> Any (\y => So $ x == y)

x : Stmt [] ["x"]
x = Define "x" `Chain` Use "x"

failing "Can't find an implementation"

  bad : Stmt [] ["x"]
  bad = Use "x" `Chain` Define "x"

--- General generators ---

genSo : (b : Bool) -> Gen $ So b
genSo True  = pure Oh
genSo False = empty

genAllQ : ((x : a) -> Gen (p x)) -> (list : List a) -> Gen $ All p list
genAllQ f []      = [| []                  |]
genAllQ f (x::xs) = [| f x :: genAllQ f xs |]

genAnyQ : ((x : a) -> Gen (p x)) -> (list : List a) -> Gen $ Any p list
genAnyQ f []      = empty
genAnyQ f (x::xs) = oneOf
  $  Here `onForgottenStructure` f x
  :: There `onAlternativesOf` genAnyQ f xs

genName : Gen Name
genName = [| elements (cast <$> ['x', 'y', 'z']) ++ elements (show <$> [1 .. 3]) |]

genNames : Gen (List Name)
genNames = listOf genName

genUniqueName : (existing : List Name) -> Gen (new : Name ** All (\ex => So $ ex /= new) existing)
genUniqueName existing = do
  new <- genName
  all <- genAllQ (\ex => genSo (ex /= new)) existing
  pure (new ** all)

genExisting : Eq a => (existing : List a) -> Gen (res : a ** Any (\ex => So $ ex == res) existing)
genExisting [] = empty
genExisting existing@(x::xs) = oneOf
  $  genAnyQ (\ex => genSo $ ex == x) existing `mapAlternativesWith` (\an => (x ** an))
  ++ genExisting xs `mapAlternativesWith` \(res ** subex) => (res ** There subex)

mutual

  export
  genStmt__ : Fuel -> Gen (definedPre ** definedPost ** Stmt definedPre definedPost)
  genStmt__ fuel = oneOf $
    [ do defined <- genNames
         (new ** prf) <- genUniqueName defined
         pure (defined ** _ ** Define new)

    , do defined <- genNames
         (used ** prf) <- genExisting defined
         pure (defined ** _ ** Use used)
    ] ++ case fuel of
           Dry => empty
           More fuel => [ do (pre ** mid ** left) <- genStmt__ fuel
                             (post ** right) <- genStmtP_ fuel mid
                             pure (_ ** _ ** Chain left right)

                        , do (mid ** post ** right) <- genStmt__ fuel
                             (pre ** left) <- genStmt_P fuel mid
                             pure (_ ** _ ** Chain left right)
                        ]

  export
  genStmtP_ : Fuel -> (definedPre : _) -> Gen (definedPost ** Stmt definedPre definedPost)
  genStmtP_ fuel definedPre = oneOf $
    [ do (new ** prf) <- genUniqueName definedPre
         pure (_ ** Define new)

    , do (used ** prf) <- genExisting definedPre
         pure (_ ** Use used)
    ] ++ case fuel of
           Dry => empty
           More fuel => [ do (mid ** left) <- genStmtP_ fuel definedPre
                             (post ** right) <- genStmtP_ fuel mid
                             pure (_ ** Chain left right)

                        , do (mid ** post ** right) <- genStmt__ fuel
                             left <- genStmtPP fuel definedPre mid
                             pure (_ ** Chain left right)
                        ]

  export
  genStmt_P : Fuel -> (definedPost : _) -> Gen (definedPre ** Stmt definedPre definedPost)
  genStmt_P fuel definedPost = oneOf $
    [ case definedPost of
        []           => empty
        new::defined => do
          all <- genAllQ (\ex => genSo (ex /= new)) defined
          pure (_ ** Define new)

    , do (used ** prf) <- genExisting definedPost
         pure (_ ** Use used)
    ] ++ case fuel of
           Dry => empty
           More fuel => [ do (pre ** mid ** left) <- genStmt__ fuel
                             right <- genStmtPP fuel mid definedPost
                             pure (_ ** Chain left right)

                        , do (mid ** right) <- genStmt_P fuel definedPost
                             (pre ** left) <- genStmt_P fuel mid
                             pure (_ ** Chain left right)
                        ]

  export
  genStmtPP : Fuel -> (definedPre : _) -> (definedPost : _) -> Gen $ Stmt definedPre definedPost
  genStmtPP fuel definedPre definedPost = oneOf $
    [ case definedPost of
        []           => empty
        new::defined => case decEq defined definedPre of
          No _     => empty
          Yes Refl => do
            all <- genAllQ (\ex => genSo (ex /= new)) defined
            pure $ Define new
    ] ++ case fuel of
           Dry => empty
           More fuel => case decEq definedPre definedPost of
             No _     => []
             Yes Refl =>
               [ do (used ** prf) <- genExisting definedPost
                    pure $ Use used

               , do (mid ** left) <- genStmtP_ fuel definedPre
                    right <- genStmtPP fuel mid definedPre
                    pure $ Chain left right

               , do (mid ** right) <- genStmt_P fuel definedPre
                    left <- genStmtPP fuel definedPre mid
                    pure $ Chain left right
               ]
