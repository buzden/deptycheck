module Deriving.SpecialiseData.Codegen.Cast

import Deriving.SpecialiseData.Common
import Deriving.SpecialiseData.Helpers
import Deriving.SpecialiseData.QuantifiersExt
import Deriving.SpecialiseData.Task
import Deriving.SpecialiseData.TaskFormation
import Deriving.SpecialiseData.TypeInfoExt
import Deriving.SpecialiseData.Unification
import Language.Reflection.Compat
import Language.Reflection.Expr
import Language.Reflection.VarSubst

------------------------------------
--- SPEC TO POLY CAST DERIVATION ---
------------------------------------

transMachineVars : TTImp -> TTImp
transMachineVars $ IVar fc n@(MN ns nn) = IVar fc $ fromString "MS^\{show ns}^\{show nn}"
transMachineVars $ IBindVar fc n@(MN ns nn) = IBindVar fc $ fromString "MS^\{show ns}^\{show nn}"
transMachineVars t = t

parameters (t : SpecTask)
  ||| Generate specialised to polymorphic type conversion function clause
  ||| for given constructor
  mkMToPImplClause :
    UnificationResult ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    (pCon : Con) ->
    (0 _ : ConArgsNamed pCon) =>
    (mCon : Con) ->
    (0 _ : ConArgsNamed mCon) =>
    ConMeta ->
    Nat ->
    Clause
  mkMToPImplClause ur _ con mcon meta _ =
    mapClause transMachineVars $
      var "mToPImpl" .$
        mcon.apply bindVar
          (substituteVariables
            (fromList $ argsToBindMap mcon.args) <$> ur.fullResult)
      .= (substituteVariables meta.mToPRenames $ con.apply var ur.fullResult)

  ||| Generate specialised to polymorphic type conversion function declarations
  export
  mkMToPImplDecls :
    UniResults ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    TypeMeta ->
    List Decl
  mkMToPImplDecls urs mt meta = do
    let clauses = map2UConsN t mkMToPImplClause urs mt meta
    [ def "mToPImpl" clauses
    ]

  ||| Generate specialised to polymorphic cast signature
  export
  mkMToPSig : (mt : TypeInfo) -> (0 _ : AllTyArgsNamed mt) => TTImp
  mkMToPSig mt = forallMTArgs t `(Cast ~(t.specInvocation) ~(t.fullInvocation))

  ||| Generate specialised to polymorphic cast declarations
  export
  mkMToPDecls : (mt : TypeInfo) -> (0 _ : AllTyArgsNamed mt) => List Decl
  mkMToPDecls mt =
    [ def "mToP" [ (var "mToP") .= `(MkCast mToPImpl)]
    ]

  -----------------------------------
  --- CAST INJECTIVITY DERIVATION ---
  -----------------------------------

||| A tuple value of multiple repeating expressions
tupleOfN : Nat -> TTImp -> TTImp
tupleOfN 0 _ = `(MkUnit)
tupleOfN 1 t = t
tupleOfN (S n) t = `(MkPair ~t ~(tupleOfN n t))

||| Assemble a TTImp of a tuple from a list of `TTImp`s
tupleOf : List TTImp -> TTImp
tupleOf [] = `(MkUnit)
tupleOf [x] = x
tupleOf (x :: xs) = `(MkPair ~x ~(tupleOf xs))

parameters (t : SpecTask)
  ||| Emit a recursive call to castInjImpl constructing the proof from given names
  recCastInj : Name -> Name -> TTImp
  recCastInj p1 p2 = `(~(var $ inGenNS t $ "castInjImpl") $ trans ~(var p1) $ sym ~(var p2))

  ||| Generate a with-clause corresponding to a single recursive argument
  mkArgWithClause : Name -> TTImp -> Clause -> Clause
  mkArgWithClause argName existingLhs inner = do
    let mToPImpl = var $ inGenNS t "mToPImpl"
    let lhsArg = var $ fromString "lhs^\{argName}"
    let rhsArg = var $ fromString "rhs^\{argName}"
    let p1 = Just (MW, fromString "\{argName}^p1")
    let p2 = Just (MW, fromString "\{argName}^p2")
    withClause existingLhs MW `(~mToPImpl ~lhsArg) p1 [] [
      withClause `(~existingLhs | _) MW `(~mToPImpl ~rhsArg) p2 [] [inner]
    ]

  ||| Wrap a term into a number of `IAppWith`s with underscores
  withManyUnders : Nat -> TTImp -> TTImp
  withManyUnders 0 x = x
  withManyUnders (S n) x = withManyUnders n `(~x | _)

  ||| Generate a final with-clause that matches all equality proofs to `Refl`s
  mkFinalClause : (con : Con) -> (0 _ : ConArgsNamed con) => ConMeta -> Clause
  mkFinalClause con meta = do
    let emptyCon = con.apply (\_ => `(_)) empty
    let recArgAmount = countRecursiveArgs meta
    let initialLhs = withManyUnders (2 * recArgAmount) $
      var "castInjImpl" .! ("castInj^x", emptyCon) .! ("castInj^y", emptyCon) .$ var "Refl"
    let recNames = recursiveArgNames con meta
    let recFns = (\n => recCastInj (fromString "\{n}^p1") (fromString "\{n}^p2")) <$> recNames
    withClause initialLhs MW (tupleOf recFns) Nothing [] [
      `(~initialLhs | ~(tupleOfN recArgAmount `(Refl))) .= `(Refl)
    ]

  ||| Generate a left-hand-side for recursive argument with-clauses
  mkInitialLhs : Con -> ConMeta -> TTImp
  mkInitialLhs con meta = do
    let lhsCon = bindConRecArgsAliased con meta $ prependS "lhs^"
    let rhsCon = bindConRecArgsAliased con meta $ prependS "rhs^"
    var "castInjImpl" .! ("castInj^x", lhsCon) .! ("castInj^y", rhsCon) .$ bindVar "prf"

  ||| Wrap a clause in with-clauses for all given names
  mkRecArgClauses : List Name -> TTImp -> Clause -> Clause
  mkRecArgClauses [] exLhs inner = inner
  mkRecArgClauses (x :: xs) exLhs inner = mkArgWithClause x exLhs $ mkRecArgClauses xs `(~exLhs | _ | _) inner

  ||| Derive a single cast injectivity clause
  mkCastInjClause :
    UnificationResult ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    (con : Con) ->
    (0 cn : ConArgsNamed con) =>
    (mcon : Con) ->
    (0 mcn : ConArgsNamed mcon) =>
    ConMeta ->
    Nat ->
    Clause
  mkCastInjClause ur mt _ con meta n = do
    if not (hasRecursiveArgs meta)
      then do
        let emptyCon = con.apply (\_ => `(_)) empty
        (var "castInjImpl") .! ("castInj^x", emptyCon) .! ("castInj^y", emptyCon) .$ `(Refl) .= `(Refl)
      else do
        let finalClause = mkFinalClause con meta
        let recNames = recursiveArgNames con meta
        let initLhs = mkInitialLhs con meta
        mkRecArgClauses recNames initLhs finalClause

  ||| Derive cast injectivity proof
  export
  mkCastInjDecls :
    UniResults ->
    (mt : TypeInfo) ->
    (0 mtp : AllTyArgsNamed mt) =>
    TypeMeta ->
    List Decl
  mkCastInjDecls ur ti meta = do
    let xVar = "castInj^x"
    let yVar = "castInj^y"
    let mToPVar = var $ inGenNS t "mToP"
    let mToPImplVar = applyMTArgs t $ var $ inGenNS t "mToPImpl"
    let arg1 = MkArg MW ImplicitArg (Just xVar) $
                ti.apply var empty
    let arg2 = MkArg MW ImplicitArg (Just yVar) $
                ti.apply var empty
    let eqs =
      `((~(mToPImplVar .$ var xVar)
          ~=~
          ~(mToPImplVar .$ var yVar)) ->
          ~(var xVar) ~=~ ~(var yVar))
    let castInjImplClauses = map2UConsN t mkCastInjClause ur ti meta
    [ claim M0 Public [] "castInjImpl" $ forallMTArgs t $ pi arg1 $ pi arg2 $ eqs
    , def "castInjImpl" castInjImplClauses
    , claim M0 Public [Hint False] "castInj" $ forallMTArgs t $
        `(Injective ~(mToPImplVar))
    , def "castInj" $ singleton $
        `(castInj) .= `(MkInjective castInjImpl)
    ]


------------------------------------
--- POLY TO SPEC CAST DERIVATION ---
------------------------------------

parameters (t : SpecTask)
  ||| Generate specialised to polymorphic type conversion function signature
  export
  mkPToMImplSig :
    UniResults ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    TTImp
  mkPToMImplSig _ mt =
    forallMTArgs t $ arg t.fullInvocation .-> t.specInvocation

  ||| Generate specialised to polymorphic type conversion function clause
  ||| for given constructor
  mkPToMImplClause :
    UnificationResult ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    (pCon : Con) ->
    (0 _ : ConArgsNamed pCon) =>
    (mCon : Con) ->
    (0 _ : ConArgsNamed mCon) =>
    ConMeta ->
    Nat ->
    Clause
  mkPToMImplClause ur _ con mcon meta _ =
    mapClause transMachineVars $
      var "pToMImpl" .$ con.apply bindVar
        (substituteVariables
          (fromList $ argsToBindMap $ con.args) <$> ur.fullResult)
      .= (substituteVariables meta.pToMRenames $ mcon.apply var ur.fullResult)

  ||| Generate specialised to polymorphic type conversion function declarations
  export
  mkPToMImplDecls :
    UniResults ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    TypeMeta ->
    List Decl
  mkPToMImplDecls urs mt meta = do
    let clauses = map2UConsN t mkPToMImplClause urs mt meta
    [ def "pToMImpl" clauses
    ]

  ||| Generate specialised to polymorphic cast signature
  export
  mkPToMSig : (mt : TypeInfo) -> (0 _ : AllTyArgsNamed mt) => TTImp
  mkPToMSig mt = do
    forallMTArgs t $ `(Cast ~(t.fullInvocation) ~(t.specInvocation))

  ||| Generate specialised to polymorphic cast declarations
  export
  mkPToMDecls : (mt : TypeInfo) -> (0 _ : AllTyArgsNamed mt) => List Decl
  mkPToMDecls mt =
    [ def "pToM" [ (var "pToM") .= `(MkCast pToMImpl)]
    ]
