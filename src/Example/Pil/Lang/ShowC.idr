module Example.Pil.Lang.ShowC

import public Example.Pil.Lang

export
Show Name where
  show (MkName n) = n

public export
0 allShows : Expression ctx a -> Type
allShows (C _) = Show $ idrTypeOf a
allShows (V n) = ()
allShows (U _ e) = allShows e
allShows (B _ e1 e2) = (allShows e1, allShows e2)

export
show : (ex : Expression ctx a) -> (shows : allShows ex) => String
show (C x) = show x
show (V n) = show n
show (U f e) = "?(" ++ show e ++ ")"
show (B f e1 e2) = with Example.Pil.Lang.ShowC.show "(" ++ show e1 {shows = fst shows} ++ ") ?? (" ++ show e2 {shows = snd shows} ++ ")"
