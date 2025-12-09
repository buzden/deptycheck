module Shared

import public Control.Monad.Writer
import public Control.Monad.Either
import public Deriving.DepTyCheck.Util.Specialisation
import public Language.Reflection.Unify

%language ElabReflection

public export
record CallGen where
  constructor MkCallGen
  sig : GenSignature
  fuel : TTImp
  givens : Vect sig.givenParams.size TTImp

export
[PrintDC]
Monad m => Elaboration m => NamesInfoInTypes => DerivationClosure m where
  needWeightFun ti = do
    logMsg "" 0 "needWeightFun \{show ti}"
    pure ()
  callGen sig fuel params = do
    logPoint Warning "deptycheck.test.utils.specialise" [sig] "CallGen params: \{show params}"
    pure (`(_), Nothing)

export
[WriterDC]
Monad m => Elaboration m => MonadWriter (Maybe CallGen) m => NamesInfoInTypes => DerivationClosure m where
  needWeightFun ti = pure ()
  callGen sig fuel params = do
    tell $ Just $ MkCallGen sig fuel params
    pure (`(?dc_return), Nothing)

export
queryVar : Elaboration m => TTImp -> m TTImp
queryVar t@(IVar fc n) = do
  getType n >>= pure . \case
    (n, _) :: [] => IVar fc n
    _            => t
queryVar t = pure t

export
expandNames : Elaboration m => TTImp -> m TTImp
expandNames = mapMTTImp queryVar

export
runSIN : Elaboration m => Maybe NamesInfoInTypes -> Bool -> TTImp -> m ()
runSIN namesInfo declareSpec e = do
  e <- expandNames e
  logPoint Warning "deptycheck.test.utils.specialise" [] "Expanded e: \{show e}"
  MkNS nsNames <- provideNS

  let modName : Name -> Name
      modName n = NS (MkNS $ show n :: nsNames) n

  namesInfo : NamesInfoInTypes <-
    case namesInfo of
      Nothing    => getNamesInfoInTypes' e
      Just nInfo => getNamesInfoInTypes' e <&> (<+> nInfo)
  -- logPoint Warning "deptycheck.test.utils.specialise" [] "Types in namesInfo: \{show $ keys knownTypes}"

  let (IVar _ tn, rs) = unAppAny e
    | _ => fail "Failed to extract type name from invocation"
  let Just ti = lookupType tn
    | _ => fail "Failed to get type info"
  let Yes atin = areAllTyArgsNamed ti
    | No _ => fail "Type info has unnamed arguments"
  let True = length ti.args == length rs
    | _ => fail "Not all arguments have been given parameters"
  let filtered = filter ((`(_) /=) . snd) $ zip (withIndex ti.args) $ map getExpr rs
  let givenSet = SortedSet.fromList $ (fst . fst) <$> filtered
  let givenVals = formGivenVals (Vect.fromList (Prelude.toList givenSet)) $ snd <$> filtered
  let dc = PrintDC @{%search}

  r <- specialiseIfNeeded (MkGenSignature ti givenSet) `(?fuel) givenVals
  case r of
    Nothing => logMsg "" 0 "sIN returned nothing."
    Just (sdecls, stype, retExpr) => do
      if declareSpec then declare sdecls else pure ()

export
runSIN' :
  Elaboration m =>
  MonadWriter (Maybe CallGen) m =>
  Maybe NamesInfoInTypes -> Bool -> TTImp -> m $ Maybe TTImp
runSIN' namesInfo declareSpec e = do
  e <- expandNames e
  logPoint Warning "deptycheck.test.utils.specialise" [] "Expanded e: \{show e}"
  MkNS nsNames <- provideNS

  let modName : Name -> Name
      modName n = NS (MkNS $ show n :: nsNames) n

  namesInfo : NamesInfoInTypes <-
    case namesInfo of
      Nothing    => getNamesInfoInTypes' e
      Just nInfo => getNamesInfoInTypes' e <&> (<+> nInfo)

  let (IVar _ tn, rs) = unApp e
    | _ => fail "Failed to extract type name from invocation"
  let Just ti = lookupType tn
    | _ => fail "Failed to get type info"
  let Yes atin = areAllTyArgsNamed ti
    | No _ => fail "Type info has unnamed arguments"
  let filtered = filter ((`(_) /=) . snd) $ zip (withIndex ti.args) rs
  let givenSet = SortedSet.fromList $ (fst . fst) <$> filtered
  let givenVals = formGivenVals (Vect.fromList (Prelude.toList givenSet)) $ snd <$> filtered
  let dc = WriterDC @{%search}

  r <- specialiseIfNeeded (MkGenSignature ti givenSet) `(?fuel) givenVals
  case r of
    Nothing => pure Nothing
    Just (sdecls, stype, retExpr) => do
      when declareSpec $ declare sdecls
      pure $ Just retExpr


export
runSIN'' :
  Elaboration m =>
  Maybe NamesInfoInTypes -> Bool -> TTImp -> m (Maybe TTImp, Maybe CallGen)
runSIN'' namesInfo declareSpec e =
  runWriterT {w=Maybe CallGen} {m} $ runSIN' namesInfo declareSpec e
