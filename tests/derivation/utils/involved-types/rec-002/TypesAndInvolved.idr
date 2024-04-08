module TypesAndInvolved

import public Data.List.Alternating

import Language.Reflection.Compat

%default total

public export
typesAndInvolved : List (Name, Count, List Name)
typesAndInvolved =
  [ ("Odd", M0, ["Odd", "Even"])
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
    , "WithFlag"
    , "Bool"
    , "List"
    , "Maybe"
    , "Nat"
    , "Pair"
    , "WithDefault"
    ])
  ]
