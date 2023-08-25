module TypesAndInvolved

import public Data.List.Alternating

import Language.Reflection
import Language.Reflection.Syntax

%default total

public export
typesAndInvolved : List (Name, List Name)
typesAndInvolved =
  [ ("Odd", ["Odd", "Even"])
  , ("TTImp",
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
    ])
  ]
