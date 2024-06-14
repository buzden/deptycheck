module Syntax.IHateParens.Function

%default total

----------------------------
--- Function composition ---
----------------------------

export infixl 0 .|

||| Instead of `f (a b) $ c d` or `f (a b) (c d)` you can write `f .| a b .| c d`
public export %inline
(.|) : (a -> b) -> a -> b
(.|) = id
