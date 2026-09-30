module Deriving.SpecialiseData.Codegen.Type

import public Data.DPair
import Data.Fin
import Data.SnocList
import Data.SnocList.Quantifiers
import Deriving.SpecialiseData.Codegen
import public Deriving.SpecialiseData.Codegen.Cast
import public Deriving.SpecialiseData.Codegen.Claims
import public Deriving.SpecialiseData.Codegen.InterfaceImpls
import Deriving.SpecialiseData.Common
import Deriving.SpecialiseData.Helpers
import Deriving.SpecialiseData.QuantifiersExt
import Deriving.SpecialiseData.Task
import Deriving.SpecialiseData.TaskFormation
import Deriving.SpecialiseData.TypeInfoExt
import Deriving.SpecialiseData.Unification
import Language.Reflection.Compat
import Language.Reflection.Expr
import Language.Reflection.Unify
import Language.Reflection.VarSubst

  ------------------------------------
  --- SPECIALISED TYPE DECLARATION ---
  ------------------------------------

(.declNoNS) : TypeInfo -> Decl
(.declNoNS) ti =
  iData Public tyName tySig [] conITys
  where
    tyName = snd $ unNS ti.name
    tySig = piAll type ti.args
    conITys = (.iTy) <$> ti.cons

export
mkSpecTySig : SpecTask -> Decl
mkSpecTySig t = iDataLater Public t.resultName (piAll type t.ttArgs)

||| Generate declarations for given task, unification results, and specialised type
export
specDecls :
  MonadLog m => SpecTask -> UniResults -> (mt : TypeInfo) -> (0 _ : AllTyArgsNamed mt) => TypeMeta -> m $ List Decl
specDecls t uniResults specTy specMeta = do
  let specTySig = mkSpecTySig t
  let specTyDecl = specTy.declNoNS
  logPoint DetailedDebug "specialiseData.specDecls.specTy.sig" [specTy] $ show specTySig
  logPoint DetailedDebug "specialiseData.specDecls.specTy" [specTy] $ show specTyDecl
  let mToPImplClaim = mkMToPImplClaim t
  let mToPImplDecls = mkMToPImplDecls t uniResults specTy specMeta
  logPoint DetailedDebug "specialiseData.specDecls.mToPImpl.sig" [specTy] $ show mToPImplClaim
  logPoint DetailedDebug "specialiseData.specDecls.mToPImpl" [specTy] $ show mToPImplDecls
  let mToPClaim = mkMToPClaim t
  let mToPDecls = mkMToPDecls t specTy
  logPoint DetailedDebug "specialiseData.specDecls.mToP.sig" [specTy] $ show mToPClaim
  logPoint DetailedDebug "specialiseData.specDecls.mToP" [specTy] $ show mToPDecls
  let castInjDecls = mkCastInjDecls t uniResults specTy specMeta
  logPoint DetailedDebug "specialiseData.specDecls.castInj" [specTy] $ show castInjDecls
  let decEqClaims : List Decl = [ mkDecEqImplClaim t, mkDecEqClaim t ]
  let decEqDecls = mkDecEqDecls t uniResults specTy
  logPoint DetailedDebug "specialiseData.specDecls.decEq.sig" [specTy] $ show decEqClaims
  logPoint DetailedDebug "specialiseData.specDecls.decEq" [specTy] $ show decEqDecls
  let showClaims = mkShowClaims t
  let showDecls = mkShowDecls t uniResults specTy
  logPoint DetailedDebug "specialiseData.specDecls.show.sig" [specTy] $ show showClaims
  logPoint DetailedDebug "specialiseData.specDecls.show" [specTy] $ show showDecls
  let eqClaims = mkEqClaims t
  let eqDecls = mkEqDecls t uniResults specTy
  logPoint DetailedDebug "specialiseData.specDecls.eq.sig" [specTy] $ show eqClaims
  logPoint DetailedDebug "specialiseData.specDecls.eq" [specTy] $ show eqDecls
  let pToMImplClaim = mkPToMImplClaim t
  let pToMImplDecls = mkPToMImplDecls t uniResults specTy specMeta
  logPoint DetailedDebug "specialiseData.specDecls.pToMImpl.sig" [specTy] $ show pToMImplClaim
  logPoint DetailedDebug "specialiseData.specDecls.pToMImpl" [specTy] $ show pToMImplDecls
  let pToMClaim = mkPToMClaim t
  let pToMDecls = mkPToMDecls t specTy
  logPoint DetailedDebug "specialiseData.specDecls.pToM.sig" [specTy] $ show pToMClaim
  logPoint DetailedDebug "specialiseData.specDecls.pToM" [specTy] $ show pToMDecls
  let fromStringClaims = mkFromStringClaims t
  let fromStringDecls = mkFromStringDecls t specTy
  logPoint DetailedDebug "specialiseData.specDecls.fromString.sig" [specTy] $ show fromStringClaims
  logPoint DetailedDebug "specialiseData.specDecls.fromString" [specTy] $ show fromStringDecls
  let numClaims = mkNumClaims t
  let numDecls = mkNumDecls t specTy
  logPoint DetailedDebug "specialiseData.specDecls.num.sig" [specTy] $ show numClaims
  logPoint DetailedDebug "specialiseData.specDecls.num" [specTy] $ show numDecls
  let anyUndecided = any isUndecided uniResults
  let sClaims =
      [ mToPImplClaim
      , mToPClaim
      ] ++ join
        [ decEqClaims
        , showClaims
        , eqClaims
        ]
  let dClaims =
      [ pToMImplClaim
      , pToMClaim
      ] ++ join
        [ fromStringClaims
        , numClaims
        ]
  let claims = sClaims ++ if anyUndecided then [] else dClaims
  logPoint DetailedDebug "specialiseData.specDecls.claims" [specTy] $ show claims
  let decidedDecls =
    [ pToMImplDecls
    , pToMDecls
    , fromStringDecls
    , numDecls
    ]
  let onFull : List Decl =
    if anyUndecided
        then []
        else join decidedDecls

  pure $ singleton $ INamespace EmptyFC (MkNS [ show t.resultName ]) $
    join
      [ [ specTySig ]
      , claims
      , [ specTyDecl ]
      , mToPImplDecls
      , mToPDecls
      , castInjDecls
      , decEqDecls
      , showDecls
      , eqDecls
      , onFull
      ]

