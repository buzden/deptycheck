module Deriving.SpecialiseData.Codegen.InterfaceImpls

import Deriving.SpecialiseData.Common
import Deriving.SpecialiseData.Helpers
import Deriving.SpecialiseData.QuantifiersExt
import Deriving.SpecialiseData.Task
import Deriving.SpecialiseData.TaskFormation
import Deriving.SpecialiseData.TypeInfoExt
import Deriving.SpecialiseData.Unification
import Language.Reflection.Compat
import Language.Reflection.Expr

-------------------------------------
--- DECIDABLE EQUALITY DERIVATION ---
-------------------------------------

parameters (t : SpecTask)
  ||| Decidable equality clause
  mkDecEqImplClause : Clause
  mkDecEqImplClause =
    let mToPImpl = var $ inGenNS t "mToPImpl"
    in `(decEqImpl x1 x2)
        .=
        `(decEqInj {f = ~mToPImpl} $
          let x1' : ~(t.fullInvocation);
              x1' = (~mToPImpl x1);
              x2' : ~(t.fullInvocation);
              x2' = (~mToPImpl x2);
          in decEq x1' x2')

  ||| Derive decidable equality
  export
  mkDecEqDecls :
    UniResults ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    List Decl
  mkDecEqDecls _ ti = do
    [ def "decEqImpl" [ mkDecEqImplClause ]
    , def "decEq'"
      [ `(decEq') .= `((Mk DecEq) ~(var $ inGenNS t "decEqImpl")) ]
    ]

-----------------------
--- SHOW DERIVATION ---
-----------------------

parameters (t : SpecTask)
  ||| Derive Show implementation via cast
  export
  mkShowDecls :
    UniResults ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    List Decl
  mkShowDecls _ ti = do
    let mToPImpl = var $ inGenNS t "mToPImpl"
    [ def "showImpl" [ `(showImpl x) .= `(show $ ~mToPImpl x) ]
    , def "showPrecImpl"
      [ `(showPrecImpl p x) .= `(showPrec p $ ~mToPImpl x) ]
    , def "show'" [ `(show') .= `(MkShow showImpl showPrecImpl) ]
    ]

---------------------
--- EQ DERIVATION ---
---------------------

parameters (t : SpecTask)
  ||| Derive Eq implementation via cast
  export
  mkEqDecls :
    UniResults ->
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    List Decl
  mkEqDecls _ ti = do
    let mToPImpl = var $ inGenNS t "mToPImpl"
    [ def "eqImpl" [ `(eqImpl x y) .= `((~mToPImpl x) == (~mToPImpl y)) ]
    , def "neqImpl" [ `(neqImpl x y) .= `((~mToPImpl x) /= (~mToPImpl y)) ]
    , def "eq'" [ `(eq') .= `(MkEq eqImpl neqImpl) ]
    ]


-----------------------------
--- FROMSTRING DERIVATION ---
-----------------------------

parameters (t : SpecTask)
  export
  mkFromStringDecls :
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    List Decl
  mkFromStringDecls ti = do
    let pToMImpl = var $ inGenNS t "pToMImpl"
    [ def "fromStringImpl"
      [ `(fromStringImpl @{fs} s) .= `(~pToMImpl $ fromString @{fs} s) ]
    , def "fromString'"
        [ `(fromString' @{fs}) .= `(MkFromString $ ~(var $ inGenNS t "fromStringImpl") @{fs}) ]
    ]

----------------------
--- NUM DERIVATION ---
----------------------

parameters (t : SpecTask)
  export
  mkNumDecls :
    (mt : TypeInfo) ->
    (0 _ : AllTyArgsNamed mt) =>
    List Decl
  mkNumDecls ti = do
    let pToMImpl = var $ inGenNS t "pToMImpl"
    let mToPImpl = var $ inGenNS t "mToPImpl"
    [ def "numImpl"
      [ `(numImpl @{fs} s) .= `(~pToMImpl $ Num.fromInteger @{fs} s) ]
    , def "plusImpl"
        [ `(plusImpl @{fs} a b ) .= `(~pToMImpl $ (+) @{fs} (~mToPImpl a) (~mToPImpl b)) ]
    , def "starImpl"
        [ `(starImpl @{fs} a b ) .= `(~pToMImpl $ (*) @{fs} (~mToPImpl a) (~mToPImpl b)) ]
    , def "num'"
        [ `(num' @{fs}) .=
            `(MkNum
              (~(var $ inGenNS t "plusImpl") @{fs})
              (~(var $ inGenNS t "starImpl") @{fs})
              (~(var $ inGenNS t "numImpl") @{fs}))
        ]
    ]
