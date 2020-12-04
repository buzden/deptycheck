module Example.Pil.Lang.ShowC

import Data.String.Extra

import public Example.Pil.Lang

export
Show Name where
  show (MkName n) = n

looksLikeInfixOperator : String -> Bool
looksLikeInfixOperator =
  flip elem ["+", "-", "*", "/", "%", "==", "!=", "<", ">", ">=", "<=", "&&", "||", "&", "|", "^", "<<", ">>"]

makeFuncName : String -> String
makeFuncName = pack . map (\k => if isAlphaNum k then k else '_') . unpack

export
Show (Expression ctx a) where
  show (C {ty=Bool'}   x) = show x
  show (C {ty=Int'}    x) = show x
  show (C {ty=String'} x) = show x
  show (V n)              = show n
  show (U {opName} _ e)   = opName ++ "(" ++ show e ++ ")"
  show (B {opName} _ l r) = if looksLikeInfixOperator opName
      then wr l ++ " " ++ opName ++ " " ++ wr r
      else makeFuncName opName ++ "(" ++ show l ++ ", " ++ show r ++ ")"
    where
    wr : Expression ctx x -> String
    wr e@(B _ _ _) = "(" ++ show e ++ ")"
    wr e           = show e

export
Show Type' where
  show Bool'   = "bool"
  show Int'    = "int"
  show String' = "char *"

isNopDeeply : Statement pre post -> Bool
isNopDeeply Example.Pil.Lang.nop = True
isNopDeeply (x *> y)             = isNopDeeply x && isNopDeeply y
isNopDeeply _                    = False

||| Next identation
n : Nat -> Nat
n = (+ 2)

showInd : (indent : Nat) -> Statement pre post -> String
showInd i Example.Pil.Lang.nop = ""
showInd i (ty . n) = indent i $ show ty ++ " " ++ show n ++ ";"
showInd i (Example.Pil.Lang.(#=) n v) = indent i $ show n ++ " = " ++ show v ++ ";"
showInd i (for init cond upd body) = if isNopDeeply init -- TODO to add a situation when we can use normal C's `for`
  then showWhile i
  else indent i "{\n" ++
         showInd (n i) init ++ "\n" ++
         showWhile (n i) ++ "\n" ++
       indent i "}"
  where
    showWhile : Nat -> String
    showWhile i =
      indent i ("while (" ++ show cond ++ ") {\n") ++
        showInd (n i) body ++ "\n" ++
        (if isNopDeeply upd then ""
          else showInd (n i) upd ++ "\n") ++
      indent i "}"
showInd i (if__ cond x y) = indent i "if (" ++ show cond ++ ") {\n" ++
                              showInd (n i) x ++ "\n" ++
                            indent i "}" ++ if isNopDeeply y then ""
                              else " else {\n" ++
                                showInd (n i) y ++ "\n" ++
                                indent i "}"
showInd i (x *> y) = if isNopDeeply x then showInd i y
                       else showInd i x ++ if isNopDeeply y then "" else "\n" ++ showInd i y
showInd i (block x) = indent i "{\n" ++ showInd (n i) x ++ "\n" ++ indent i "}"
showInd i (print x) = indent i $ "puts(" ++ show x ++ ");"

export
Show (Statement pre post) where
  show = showInd 0
