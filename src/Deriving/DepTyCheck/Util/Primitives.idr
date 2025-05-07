module Deriving.DepTyCheck.Util.Primitives

import public Language.Reflection.Compat

%default total

---------------------------------------------------
--- Working around primitive and special values ---
---------------------------------------------------

primTypeInfo : String -> TypeInfo
primTypeInfo s = MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic s) [] []

export
typeInfoForPrimType : PrimType -> TypeInfo
typeInfoForPrimType IntType     = primTypeInfo "Int"
typeInfoForPrimType IntegerType = primTypeInfo "Integer"
typeInfoForPrimType Int8Type    = primTypeInfo "Int8"
typeInfoForPrimType Int16Type   = primTypeInfo "Int16"
typeInfoForPrimType Int32Type   = primTypeInfo "Int32"
typeInfoForPrimType Int64Type   = primTypeInfo "Int64"
typeInfoForPrimType Bits8Type   = primTypeInfo "Bits8"
typeInfoForPrimType Bits16Type  = primTypeInfo "Bits16"
typeInfoForPrimType Bits32Type  = primTypeInfo "Bits32"
typeInfoForPrimType Bits64Type  = primTypeInfo "Bits64"
typeInfoForPrimType StringType  = primTypeInfo "String"
typeInfoForPrimType CharType    = primTypeInfo "Char"
typeInfoForPrimType DoubleType  = primTypeInfo "Double"
typeInfoForPrimType WorldType   = primTypeInfo "%World"

export
typeInfoForTypeOfTypes : TypeInfo
typeInfoForTypeOfTypes = primTypeInfo "Type"

export
extractTargetTyExpr : TypeInfo -> TTImp
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Int"    ) [] [] = primVal $ PrT IntType
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Integer") [] [] = primVal $ PrT IntegerType
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Int8"   ) [] [] = primVal $ PrT Int8Type
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Int16"  ) [] [] = primVal $ PrT Int16Type
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Int32"  ) [] [] = primVal $ PrT Int32Type
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Int64"  ) [] [] = primVal $ PrT Int64Type
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Bits8"  ) [] [] = primVal $ PrT Bits8Type
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Bits16" ) [] [] = primVal $ PrT Bits16Type
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Bits32" ) [] [] = primVal $ PrT Bits32Type
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Bits64" ) [] [] = primVal $ PrT Bits64Type
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "String" ) [] [] = primVal $ PrT StringType
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Char"   ) [] [] = primVal $ PrT CharType
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Double" ) [] [] = primVal $ PrT DoubleType
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "%World" ) [] [] = primVal $ PrT WorldType
extractTargetTyExpr $ MkTypeInfo (NS (MkNS ["^prim^"]) $ UN $ Basic "Type"   ) [] [] = type
extractTargetTyExpr ti = var ti.name
