module TypesAndInvolved

import Language.Reflection.Compat

%default total

-- Two mutually recursive types
mutual
  data X a b = MkX a (Y a b)
  data Y a b = Nil | MkY a (X a b)

public export
typesAndInvolved : List (Name, Count, List Name)
typesAndInvolved =
  [ ("X", M0, ["X", "Y"])
  , ("TTImp", M0,
    [ "AltType"
    , "BindMode"
    , "BuiltinType"
    , "Clause"
    , "Constant"
    , "Count"
    , "Data"
    , "DataOpt"
    , "Decl"
    , "DotReason"
    , "FC"
    , "FnOpt"
    , "IClaimData"
    , "IField"
    , "IFieldUpdate"
    , "ITy"
    , "LazyReason"
    , "ModuleIdent"
    , "Name"
    , "Namespace"
    , "OriginDesc"
    , "PiInfo"
    , "PrimType"
    , "Record"
    , "TTImp"
    , "TotalReq"
    , "UseSide"
    , "UserName"
    , "VirtualIdent"
    , "Visibility"
    , "WithFC"
    , "WithFlag"
    , "Bool"
    , "List"
    , "Maybe"
    , "Nat"
    , "Pair"
    , "WithDefault"
    ])
  ]
