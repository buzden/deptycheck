module Deriving.SpecialiseData.Codegen.Claims

import Deriving.SpecialiseData.Common
import Deriving.SpecialiseData.Helpers
import Deriving.SpecialiseData.QuantifiersExt
import Deriving.SpecialiseData.Task
import Deriving.SpecialiseData.TaskFormation
import Deriving.SpecialiseData.TypeInfoExt
import Deriving.SpecialiseData.Unification
import Language.Reflection.Compat
import Language.Reflection.Expr

------------------------
--- CLAIM DERIVATION ---
------------------------

parameters (t : SpecTask)
  ||| Generate specialised to polimorphic type conversion function signature
  export
  mkMToPImplClaim : Decl
  mkMToPImplClaim = public' "mToPImpl" $ forallMTArgs t $ arg t.specInvocation .-> t.fullInvocation

  ||| Generate specialised to polimorphic cast signature
  export
  mkMToPClaim : Decl
  mkMToPClaim = interfaceHint Public "mToP" $ forallMTArgs t $ `(Cast ~(t.specInvocation) ~(t.fullInvocation))

  ||| Decidable equality signatures
  export
  mkDecEqImplClaim : Decl
  mkDecEqImplClaim =
    let tInv = t.specInvocation
    in public' "decEqImpl" $ forallMTArgs t $
      piAll
        `(Dec (Equal {a = ~tInv} {b = ~tInv} x1 x2))
        [ MkArg MW AutoImplicit Nothing `(DecEq ~(t.fullInvocation))
        , MkArg MW ExplicitArg (Just "x1") tInv
        , MkArg MW ExplicitArg (Just "x2") tInv
        ]

  export
  mkDecEqClaim : Decl
  mkDecEqClaim = interfaceHint Public "decEq'" $ forallMTArgs t `(DecEq ~(t.fullInvocation) => DecEq ~(t.specInvocation))

  export
  mkShowClaims : List Decl
  mkShowClaims =
    [ public' "showImpl" $
      forallMTArgs t
        `(Show ~(t.fullInvocation) => ~(t.specInvocation) -> String)
    , public' "showPrecImpl" $
      forallMTArgs t
        `(Show ~(t.fullInvocation) => Prec -> ~(t.specInvocation) -> String)
    , interfaceHint Public "show'" $ forallMTArgs t $
      `(Show ~(t.fullInvocation) => Show ~(t.specInvocation))
    ]

  export
  mkEqClaims : List Decl
  mkEqClaims = do
    let tInv = t.specInvocation
    [ public' "eqImpl" $ forallMTArgs t
        `(Eq ~(t.fullInvocation) => ~tInv -> ~tInv -> Bool)
    , public' "neqImpl" $ forallMTArgs t
        `(Eq ~(t.fullInvocation) => ~tInv -> ~tInv -> Bool)
    , interfaceHint Public "eq'" $ forallMTArgs t $
        `(Eq ~(t.fullInvocation) => Eq ~tInv)
    ]

  ||| Generate specialised to polymorphic type conversion function signature
  export
  mkPToMImplClaim : Decl
  mkPToMImplClaim = public' "pToMImpl" $ forallMTArgs t $ arg t.fullInvocation .-> t.specInvocation

  ||| Generate specialised to polimorphic cast signature
  export
  mkPToMClaim : Decl
  mkPToMClaim =
    interfaceHint Public "pToM" $ forallMTArgs t $ `(Cast ~(t.fullInvocation) ~(t.specInvocation))

  export
  mkFromStringClaims : List Decl
  mkFromStringClaims = do
    let tInv = t.specInvocation
    [ public' "fromStringImpl" $
        forallMTArgs t
          `(FromString ~(t.fullInvocation) => String -> ~tInv)
    , interfaceHint Public "fromString'" $
        forallMTArgs t `(FromString ~(t.fullInvocation) => FromString ~tInv)
    ]

  export
  mkNumClaims : List Decl
  mkNumClaims = do
    let tInv = t.specInvocation
    [ public' "numImpl" $
        forallMTArgs t
          `(Num ~(t.fullInvocation) => Integer -> ~tInv)
    , public' "plusImpl" $
        forallMTArgs t
          `(Num ~(t.fullInvocation) => ~tInv -> ~tInv -> ~tInv)
    , public' "starImpl" $
        forallMTArgs t
          `(Num ~(t.fullInvocation) => ~tInv -> ~tInv -> ~tInv)
    , interfaceHint Public "num'" $
        forallMTArgs t `(Num ~(t.fullInvocation) => Num ~tInv)
    ]

  export
  standardClaims : List Decl
  standardClaims =
    [ mkMToPImplClaim
    , mkMToPClaim
    , mkDecEqImplClaim
    , mkDecEqClaim
    ] ++ join
      [ mkShowClaims
      , mkEqClaims
      ]

  export
  decidedClaims : List Decl
  decidedClaims =
    [ mkPToMImplClaim
    , mkPToMClaim
    ] ++ join
      [ mkFromStringClaims
      , mkNumClaims
      ]
