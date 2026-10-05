module Deriving.SpecialiseData.Unification

import public Data.DPair
import Deriving.SpecialiseData.Task
import Deriving.SpecialiseData.Helpers
import Deriving.SpecialiseData.QuantifiersExt
import public Language.Reflection.Unify

---------------------------
--- CONSTRUCTOR MAPPING ---
---------------------------

||| Unification results for the whole type
public export
UniResults : Type
UniResults = List UnificationVerdict

parameters (t : SpecTask)
  ||| Run monadic operation on all constructors of specialised type
  export
  mapCons :
    (f : (pCon : Con) ->
         (0 _ : ConArgsNamed pCon) =>
         r) ->
    List r
  mapCons f = do
    let adp = pushIn t.polyTy.cons t.polyTyNamed.tyConArgsNamed
    map (\(Element c pc) => f c) adp

  ||| Map over all constructors for which unification succeeded
  export
  mapUCons :
    (f : UnificationResult ->
         (pCon : Con) ->
         (0 _ : ConArgsNamed pCon) =>
         Nat ->
         r) ->
    UniResults ->
    List r
  mapUCons f rs = do
    let adp = pushIn t.polyTy.cons t.polyTyNamed.tyConArgsNamed
    let f' : List (Subset Con ConArgsNamed) -> UniResults -> Nat -> List r
        f' (Element con _ :: xs) (Success res :: ys) n = f res con n :: f' xs ys (S n)
        f' (_ :: xs)             (_ :: ys)           n = f' xs ys n
        f' _ _ _ = []
    f' adp rs 0

  ||| Run monadic operation on all pairs of specified and polymorphic constructors
  export
  map2UConsN :
    (f : UnificationResult ->
         (mt : TypeInfo) ->
         (0 _ : AllTyArgsNamed mt) =>
         (con : Con) ->
         (0 _ : ConArgsNamed con) =>
         (mcon : Con) ->
         (0 _ : ConArgsNamed mcon) =>
         ConMeta ->
         Nat ->
         r) ->
    UniResults ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    TypeMeta ->
    List r
  map2UConsN f rs mt @{mtp} meta = do
    let p1 = pushIn t.polyTy.cons t.polyTyNamed.tyConArgsNamed
    let p2 = pushIn mt.cons mtp.tyConArgsNamed
    f' 0 p1 p2 rs meta.conMeta
    where
      f' :
        Nat ->
        List (Subset Con ConArgsNamed) ->
        List (Subset Con ConArgsNamed) ->
        UniResults ->
        List ConMeta ->
        List r
      f' n (Element con _ :: xs) (Element mcon _ :: ys) (Success res :: zs) (meta' :: metas) =
        f res mt con mcon meta' n :: f' (S n) xs ys zs metas
      f' n (_             :: xs)                    ys  (_:: zs) ms =
        f' n xs ys zs ms
      f' _ _ _ _ _ = []

-------------------------------
--- CONSTRUCTOR UNIFICATION ---
-------------------------------

||| Run unification for a given polymorphic constructor
export
unifyCon :
  MonadLog m => (unifier : CanUnify m) =>
  (t : SpecTask) -> (con : Con) -> (0 conN : ConArgsNamed con) => m UnificationVerdict
unifyCon t con = logBounds Debug "specialiseData.unifyCon" [t.polyTy, con] $ do
  let Element ca _ = fromListAll con.args @{conArgsNamed}
  let Element ta _ = fromListAll t.tqArgs @{t.tqArgsNamed}
  let uniTask =
    MkUniTask {lfv=_} ca con.type
              {rfv=_} ta t.fullInvocation
  logPoint DetailedDebug "specialiseData.unifyCon" [t.polyTy, con] "Unifier task: \{show uniTask}"
  uniRes <- unify uniTask
  logValue DetailedDebug "specialiseData.unifyCon" [t.polyTy, con] "Unifier output: \{show uniRes}" uniRes
