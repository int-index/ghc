{-# LANGUAGE StrictData #-}

-- TODO (int-index): test case for each parsing failure.
--                   leave comments near them, e.g. "Tested by epf_001"

{-

TEST="T10358"

--------------------------------------------------------------
    data T a b = a :! b

    fn ! !(!a :! !b) = (a,b)

should parse as

    fn (! (! ( (!a) :! (!b) )) = (a,b)

-}

module ExpPatFrame (
    ExpPatFrame(..),
    LExpPatFrame,
    pprPrefixEPF,
    pprInfixEPF,
    TupArgFrame(..),
    LTupArgFrame,
    LFrameInfixEl,
    FrameInfixEl(..),
    checkExpr,
    checkPat,
    checkFunPatBind,
    checkSigVar,
    placeHolderPunRhs,
    mkRecConstrOrUpdate,
    mkFrameSCC,
    mkFrameTickPragma,
    mkFrameCoreAnn,
    starOpSym,
    mkBangPat,
    mkLazyPat
  ) where

import GhcPrelude
import FastString
import ApiAnnotation
import Outputable
import SrcLoc
import Name
import RdrName
import BasicTypes
import HsSyn
import Lexer
import qualified DynFlags
import qualified GHC.LanguageExtensions as LangExt
import Control.Monad
import Data.Foldable

{- NOTE [Expression/pattern frame]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

There are places in the grammar where we do not know whether we are parsing an
expression or a pattern without infinite lookahead (which we do not have in
'happy'):

1. View patterns:

     f (Con a b     ) = ...  -- 'Con a b' is a pattern
     f (Con a b -> x) = ...  -- 'Con a b' is an expression

2. do-notation:

     do { Con a b <- x } -- 'Con a b' is a pattern
     do { Con a b }      -- 'Con a b' is an expression

3. Guards:

     x | True <- p && q = ...  -- 'True' is a pattern
     x | True           = ...  -- 'True' is an expression

4. Top-level value/function declarations (FunBind/PatBind):

     f !a         -- TH splice
     f !a = ...   -- function declaration

   Until we encounter the = sign, we don't know if it's a top-level
   TemplateHaskell splice where ! is an infix operator, or if it's a function
   declaration where ! is a strictness annotation.

The approach GHC used before was to parse patterns as expressions and rejig
later. This turned out to be suboptimal:

  * We could not handle corner cases. For instance, the following function
    declaration LHS is not a valid expression (see Trac #1087):

      !a + !b = ...

  * There were points in the pipeline where the representation was awfully
    incorrect. For instance,

      f !a b !c = ...

    used to be first parsed as

      (f ! a b) ! c = ...

  * We had to extend HsExpr with pattern-specific constructs: EAsPat, EViewPat,
    ELazyPat, etc. It wasn't particularly elegant and we don't want such
    constructors to show up in GHC API.

One might think we could avoid this issue by using a backtracking parser, but
it runs deeper: there can be patterns inside expressions (e.g. via 'case' or
'let') and expressions inside patterns (e.g. view patterns), so naive
backtracking would be devastating to performance (asymptotically).

Now we follow a more principled approach: we can identify common syntactic
elements of expressions and patterns (e.g. both of them must have balanced
parentheses) and create an intermediate data type: 'ExpPatFrame'. When we parsed
far enough to decide whether it is an expression or a pattern, we do the
conversion.

In the future we might want to extend 'ExpPatFrame' (expression/pattern frame)
to 'ExpPatTyFrame' (expression/pattern/type frame), because with
DependentHaskell (and even smaller features, such as visible dependent
quantification in terms) we will have types inside expressions and expressions
inside types.

-}

type LExpPatFrame = Located ExpPatFrame

data ExpPatFrame
  = FrameVar RdrName
    -- ^ Identifier: Just, map, BS.length
  | FrameIPVar HsIPName
    -- ^ Implicit parameter: ?x
  | FrameOverLabel FastString
    -- ^ Overloaded label: #label
  | FrameLit (HsLit GhcPs)
    -- ^ Non-overloaded literal: 'c', "str"
  | FrameOverLit (HsOverLit GhcPs)
    -- ^ Overloaded literal: 15, 2.4
  | FramePar (SrcSpan, SrcSpan) LExpPatFrame
    -- ^ Parentheses
  | FrameSum ConTag Arity LExpPatFrame Boxity
    -- ^ Sum: (a||), (|a|), (||a)
  | FrameTuple [LTupArgFrame] Boxity
    -- ^ Tuple (section): (a,b) (a,b,c) (a,,) (,a,)
  | FrameList [LExpPatFrame]
    -- ^ List: [1, 2, 3]
  | FrameComp (HsStmtContext Name) [ExprLStmt GhcPs] (LHsExpr GhcPs)
    -- ^ List/monad comprehension: [ a | x <- f n, p, q ]
  | FrameArithSeq (ArithSeqInfo GhcPs)
    -- ^ Arithmetic sequence: [1..], [1,2..], [1..5]
  | FrameWild
    -- ^ Wildcard: _
  | FrameSplice (HsSplice GhcPs)
    -- ^ TH splice: $a, $(expr), $$(expr), [quasi| ... |]
  | FrameBracket (HsBracket GhcPs)
    -- ^ TH bracket: [|expr|], [p|pat|], 'x, ''T
  | FrameArrForm (LHsExpr GhcPs) [LHsCmdTop GhcPs]
    -- ^ Command formation (arrows): (| e cmd1 cmd2 cmd3 |)
  | FrameRecordUpd LExpPatFrame [LFrameRecUpdField]
    -- ^ Record update: (f x) { a = z }
  | FrameRecordCon (Located RdrName) FrameRecordBinds
    -- ^ Record constructor: D { x, y = f t, .. }
  | FrameAsPat LExpPatFrame LExpPatFrame
    -- ^ As-pattern: x@(D a b)
  | FrameLam (MatchGroup GhcPs (LHsExpr GhcPs))
    -- ^ Lambda-expression: \x -> e
  | FrameLet (LHsLocalBinds GhcPs) (LHsExpr GhcPs)
    -- ^ Let-expression: let p = t in e
  | FrameLamCase (MatchGroup GhcPs (LHsExpr GhcPs))
    -- ^ Lambda-expression: \x -> e
  | FrameIf (LHsExpr GhcPs) (LHsExpr GhcPs) (LHsExpr GhcPs)
    -- ^ If-expression: if p then x else y
  | FrameMultiIf [LGRHS GhcPs (LHsExpr GhcPs)]
    -- ^ Multi-way if-expression: if | p = x \n | q = x
  | FrameCase (LHsExpr GhcPs) (MatchGroup GhcPs (LHsExpr GhcPs))
    -- ^ Case-expression: case x of { p1 -> e1; p2 -> e2 }
  | FrameDo (HsStmtContext Name) [ExprLStmt GhcPs]
    -- ^ Do-expression: do { s1; a <- s2; s3 }
  | FrameProc (LPat GhcPs) (LHsCmdTop GhcPs)
    -- ^ Proc-expression: proc p -> cmd
  | FrameViewPat LExpPatFrame LExpPatFrame
    -- ^ View pattern: e -> p
  | FrameTySig LExpPatFrame (LHsSigWcType GhcPs)
    -- ^ Type signature: x :: ty
  | FrameArrApp LExpPatFrame LExpPatFrame HsArrAppType Bool
    -- ^ Arrow application: f -< arg, f -<< arg, arg >- f, arg >>- f
  | FrameSCC SourceText StringLiteral LExpPatFrame
    -- ^ SCC annotation: {-# SCC .. #-} e
  | FrameTickPragma
     SourceText
     (StringLiteral,(Int,Int),(Int,Int))
     ((SourceText,SourceText),(SourceText,SourceText))
     LExpPatFrame
    -- ^ Tick pragma: {-# GENERATED .. #-} e
  | FrameCoreAnn SourceText StringLiteral LExpPatFrame
    -- ^ Core annotation: {-# CORE .. #-} e
  | FrameInfix [LFrameInfixEl] -- reversed
    -- ^ A sequence with infix elements: a + f x y +, !a + !b

-- TODO (int-index): remove EWildPat from HsExpr
-- TODO (int-index): remove ELazyPat from HsExpr
-- TODO (int-index): remove EAsPat from HsExpr
-- TODO (int-index): remove EViewPat from HsExpr
-- TODO (int-index): remove HsArrApp/HsArrForm from HsExpr

type LFrameInfixEl = Located FrameInfixEl

data FrameInfixEl
  = FrameOpr ExpPatFrame
  | FrameOpd ExpPatFrame
  | FrameVisTy SrcSpan (LHsWcType GhcPs)
  | FrameMinus
  | FrameTilde
  | FrameBang
  | FrameDot
  | FrameStar Bool -- isUnicode
  | FrameStatic

starOpSym :: Bool -> String
starOpSym isUni = if isUni then "\x2605" else "*"

frameInfixElOpName :: FrameInfixEl -> Maybe RdrName
frameInfixElOpName el =
  case el of
    FrameOpr (FrameVar op) -> Just op
    FrameOpr{} -> Nothing
    FrameOpd{} -> Nothing
    FrameVisTy{} -> Nothing
    FrameMinus -> Just (mkOp "-")
    FrameTilde -> Nothing -- See Note [Tilde operator]
    FrameBang -> Just (mkOp "!")
    FrameDot -> Just (mkOp ".")
    FrameStar isUni -> Just (mkOp (starOpSym isUni))
    FrameStatic -> Nothing
  where
    mkOp s = mkUnqual varName (fsLit s)

frameInfixElOp :: FrameInfixEl -> Maybe ExpPatFrame
frameInfixElOp (FrameOpr op) = Just op
frameInfixElOp el = FrameVar <$> frameInfixElOpName el

{- Note [Tilde operator]
~~~~~~~~~~~~~~~~~~~~~~~~

In types, (~) is a valid operator. Surprisingly, this is not the case in terms.
There's no fundamental reason for this.

However, in order to allow (~) in terms, we would first have to make it less
magical in types, where it doesn't need to be imported and always refers to
eqTyCon_RDR. Otherwise, we wouldn't be able to assign a fixity to its
term-level counterpart because a fixity declaration for (~) always refers to
eqTyCon_RDR.

-}

type FrameRecordBinds = HsRecFields GhcPs LExpPatFrame
type FrameRecUpdField = HsRecField' (AmbiguousFieldOcc GhcPs) LExpPatFrame
type LFrameRecUpdField = Located FrameRecUpdField

type LTupArgFrame = Located TupArgFrame

data TupArgFrame
  = TupArgFramePresent LExpPatFrame
  | TupArgFrameMissing

checkExpr :: LExpPatFrame -> P (LHsExpr GhcPs)
checkExpr (L l epf) = L l <$> case epf of
  FrameVar name -> return (HsVar noExt (L l name))
  FrameIPVar ipname -> return (HsIPVar noExt ipname)
  FrameOverLabel str -> return (HsOverLabel noExt Nothing str)
  FrameLit lit ->
    -- TODO (int-index): handle -XOverloadedStrings
    return (HsLit noExt lit)
  FrameOverLit lit -> return (HsOverLit noExt lit)
  FrameInfix els -> mergeInfixExp l False els
  FramePar _ (L _ (FrameInfix [L l' el]))
    | Just op <- frameInfixElOpName el
    -> return (HsVar noExt (L l op))
    | FrameOpr op <- el -- this handles (`_`)
    -> do { op' <- checkExpr (L l' op)
          ; return (HsPar noExt op') }
  FramePar _ (L l' (FrameInfix els)) -> do
    -- TODO (int-index): remove the check that SectionL/SectionR
    -- is inside parentheses from the renamer
    e' <- mergeInfixExp l' True els
    return (HsPar noExt (L l' e'))
  FramePar _ e -> do
    e' <- checkExpr e
    return (HsPar noExt e')
  FrameSum alt arity e boxity -> do
    checkSumBoxity l alt arity (unLoc e) boxity
    e' <- checkExpr e
    return (ExplicitSum noExt alt arity e')
  FrameTuple args boxity -> do
    let
      checkArg (L l' (TupArgFramePresent e)) =
        do { e' <- checkExpr e
           ; return (L l' (Present noExt e')) }
      checkArg (L l' TupArgFrameMissing) =
        return (L l' (Missing noExt))
    args' <- traverse checkArg args
    return (ExplicitTuple noExt args' boxity)
  FrameList xs -> do
    xs' <- traverse checkExpr xs
    return (ExplicitList noExt Nothing xs')
  FrameComp ctxt quals e -> return (mkHsComp ctxt quals e)
  FrameArithSeq a -> return (ArithSeq noExt Nothing a)
  FrameWild -> return hsHoleExpr
  FrameSplice splice -> return (HsSpliceE noExt splice)
  FrameBracket br -> return (HsBracket noExt br)
  FrameArrForm op cmds ->
    -- TODO (int-index): remove HsArrForm - this can be replaced
    -- with a proper checkCmd
    return (HsArrForm noExt op Nothing cmds)
  FrameRecordUpd exp flds -> do
    exp' <- checkExpr exp
    flds' <- (traverse.traverse.traverse) checkExpr flds
    return (RecordUpd noExt exp' flds')
  FrameRecordCon con flds -> do
    flds' <- traverse checkExpr flds
    return (RecordCon noExt con flds')
  FrameAsPat{} -> do
    pState <- getPState
    let hint | extopt LangExt.TypeApplications (options pState)
             = text "Type application syntax requires a space before '@'"
             | otherwise
             = text "Did you mean to enable TypeApplications?"
    expSynIllegal hint l epf "@-pattern"
  FrameLam matches -> return (HsLam noExt matches)
  FrameLet binds expr -> return (HsLet noExt binds expr)
  FrameLamCase matches -> return (HsLamCase noExt matches)
  FrameIf c a b -> return (mkHsIf c a b)
  FrameMultiIf alts -> return (HsMultiIf noExt alts)
  FrameCase scrut matches -> return (HsCase noExt scrut matches)
  FrameDo ctxt stmts -> return (mkHsDo ctxt stmts)
  FrameProc pat cmd -> return (HsProc noExt pat cmd)
  FrameViewPat{} -> expSynIllegal empty l epf "view-pattern"
  FrameTySig e sig -> do
    e' <- checkExpr e
    return (ExprWithTySig noExt e' sig)
  FrameArrApp f a haat b -> do
    f' <- checkExpr f
    a' <- checkExpr a
    return (HsArrApp noExt f' a' haat b)
  FrameSCC src lbl e -> do
    e' <- checkExpr e
    return (HsSCC noExt src lbl e')
  FrameTickPragma src info srcInfo e -> do
    e' <- checkExpr e
    return (HsTickPragma noExt src info srcInfo e')
  FrameCoreAnn src lbl e -> do
    e' <- checkExpr e
    return (HsCoreAnn noExt src lbl e')

hsHoleExpr :: HsExpr (GhcPass id)
hsHoleExpr = HsUnboundVar noExt (TrueExprHole (mkVarOcc "_"))

expSynIllegal :: SDoc -> SrcSpan -> ExpPatFrame -> String -> P a
expSynIllegal hint l epf s = failSpanMsgP l (baseMsg $$ hint)
  where
    baseMsg =
      text "Illegal" <+> text s <+> text "in expression:" $$
      nest 2 (pprPrefixEPF epf)

data HsArgPs
  = HsValArgPs (LHsExpr GhcPs)
  | HsTypeArgPs (Located (SrcSpan, LHsWcType GhcPs))

mergeHsArgsPs
  :: LHsExpr GhcPs
  -> [HsArgPs]
  -> (P (), LHsExpr GhcPs)
mergeHsArgsPs f = foldl' go (pure (), f)
  where
    go (addAnns, f) (HsValArgPs a) = (addAnns, mkHsApp f a)
    go (addAnns, f) (HsTypeArgPs (L l (l_at, t))) =
      (addAnnotation l AnnAt l_at >> addAnns,
       L l (HsAppType noExt f t))

-- | Merge a /reversed/ and /non-empty/ soup of operators and operands
--   into a type.
--
-- User input: @F x y + G a b * X@
-- Input to 'mergeOps': [X, *, b, a, G, +, y, x, F]
-- Output corresponds to what the user wrote assuming all operators are of the
-- same fixity and left-associative.
--
-- It's a bit silly that we're doing it at all, as the renamer will have to
-- rearrange this, and it'd be easier to keep things separate.
mergeInfixExp :: SrcSpan -> Bool -> [LFrameInfixEl] -> P (HsExpr GhcPs)
mergeInfixExp loc_all sectionCtx all_xs =
  do { (mLeadingOp, e) <- go [] [] all_xs'
     ; case (mLeadingOp, mTrailingOp) of
         (Nothing, Nothing) -> return (unLoc e)
         (Just op, Nothing) ->
           do { op' <- checkExpr op
              ; return (SectionR noExt op' e) }
         (Nothing, Just op) ->
           do { op' <- checkExpr op
              ; return (SectionL noExt e op') }
         (Just op1, Just op2) ->
           failSpanMsgP loc_all $
             text "Operator sections on both sides of an infix expression:" $$
             nest 2 (pprInfixEPF (unLoc op1) <+> ppr e
                                             <+> pprInfixEPF (unLoc op2)) }
  where
    (all_xs', mTrailingOp) =
      case all_xs of
        L l x:xs
          | sectionCtx, Just op <- frameInfixElOp x
          -> (xs, Just (L l op))
        _ -> (all_xs, Nothing)

    go :: [HsArgPs]
       -> [(LExpPatFrame, LHsExpr GhcPs)]
       -> [LFrameInfixEl]
       -> P (Maybe LExpPatFrame, LHsExpr GhcPs)

    go acc ops_acc (L op_l FrameMinus : xs)
      | beforeUnary xs
      = do { a <- if null acc
                  then failSpanMsgP op_l $ -- triggered by:  - + 1
                       text "Unary minus is missing an argument"
                  else mergeAcc acc
           ; let loc = combineSrcSpans op_l (getLoc a)
                 n = NegApp noExt a noSyntaxExpr
           ; addAnnotation loc AnnMinus op_l
           ; go [HsValArgPs (L loc n)] ops_acc xs }

    -- NB. This case comes after handling prefix minus,
    -- so that (-x) is treated as NegApp, not SectionR.
    go acc ops_acc [L l x]
      | sectionCtx, Just op <- frameInfixElOp x
      = goLast acc ops_acc (Just (L l op))

    go acc ops_acc (L l (FrameOpr op):xs)
      | null acc = missingRhsErr (L l op) xs
      | otherwise =
          do { a <- mergeAcc acc
             ; go [] ((L l op, a):ops_acc) xs }

    go acc ops_acc (L l FrameMinus:xs) =
      go acc ops_acc ((L l (mkFrameOpr "-")):xs)
    go acc ops_acc (L l FrameBang:xs) =
      go acc ops_acc ((L l (mkFrameOpr "!")):xs)
    go acc ops_acc (L l FrameDot:xs) =
      go acc ops_acc ((L l (mkFrameOpr ".")):xs)
    go acc ops_acc (L l (FrameStar isUni):xs) =
      go acc ops_acc ((L l (mkFrameOpr (starOpSym isUni))):xs)

    go _ _ (L l FrameTilde : _) =
      -- See Note [Tilde operator]
      failSpanMsgP l $
        text "(~) is not a valid operator in terms."

    go acc ops_acc (L l (FrameOpd a):xs) =
      do { a' <- checkExpr (L l a)
         ; go (HsValArgPs a':acc) ops_acc xs }

    go acc ops_acc (L l (FrameVisTy l_at t):xs) =
      go (HsTypeArgPs (L l (l_at, t)):acc) ops_acc xs

    go acc ops_acc (L loc_static FrameStatic : xs)
      | beforeUnary xs
      = do { a <- mergeAcc acc
           ; let loc = combineSrcSpans loc_static (getLoc a)
                 n = HsStatic noExt a
           ; addAnnotation loc AnnStatic loc_static
           ; go [HsValArgPs (L loc n)] ops_acc xs }
      | otherwise =
        failSpanMsgP loc_static $
          text "Static expression must be parenthesized" <+>
          text "when used as a function argument."

    go acc ops_acc [] = goLast acc ops_acc Nothing

    goLast acc ops_acc mLeadingOp
      | null acc
      = case ops_acc of
          (op, _):_ -> missingLhsErr op
          _ ->
            -- Triggered by things like (+ +)
            failSpanMsgP loc_all $
              text "What are you trying to achieve, break the parser?"
      | otherwise
      = do { a <- mergeAcc acc
           ; e <- mergeOpsAcc a ops_acc
           ; return (mLeadingOp, e) }

    mergeAcc :: [HsArgPs] -> P (LHsExpr GhcPs)
    mergeAcc [] = panic "mergeInfixExp.mergeAcc: empty input"
    mergeAcc (HsTypeArgPs (L l (_, t)) : _) =
      failSpanMsgP l $
        text "Type application must be preceded by an identifier:" $$
        nest 2 (text "@" <> ppr t)
    mergeAcc (HsValArgPs f : args) = do
      traverse_ checkBlockArguments [x | HsValArgPs x <- args]
      let (addAnns, e) = mergeHsArgsPs f args
      addAnns
      return e

    mergeOpsAcc = foldM (\a (op, b) ->
      do { op' <- checkExpr op
         ; let e = mkLOpApp a op' b
         ; addAnnotation (getLoc e) AnnVal (getLoc op')
         ; return e })

beforeUnary :: [LFrameInfixEl] -> Bool
beforeUnary (L _ (FrameOpd{}):_) = False
beforeUnary (L _ (FrameVisTy{}):_) = False
beforeUnary (L _ _ : _) = True
beforeUnary [] = True

mkLOpApp :: LHsExpr GhcPs -> LHsExpr GhcPs -> LHsExpr GhcPs -> LHsExpr GhcPs
mkLOpApp x op y =
  let loc = getLoc x `combineSrcSpans` getLoc op `combineSrcSpans` getLoc y
  in L loc (OpApp noExt x op y)

mkFrameOpr :: String -> FrameInfixEl
mkFrameOpr s = FrameOpr (FrameVar (mkUnqual varName (fsLit s)))

checkSumBoxity :: SrcSpan -> ConTag -> Arity -> ExpPatFrame -> Boxity -> P ()
checkSumBoxity _ _ _ _ Unboxed = return ()
checkSumBoxity l alt arity e Boxed =
  failSpanMsgP l $
    hang (text "Boxed sums not supported:") 2 ppr_boxed_sum
  where
    ppr_boxed_sum =
          text "(" <+> ppr_bars (alt - 1) <+> pprPrefixEPF e
                   <+> ppr_bars (arity - alt) <+> text ")"
    ppr_bars n = hsep (replicate n (Outputable.char '|'))

pPatVar :: ExpPatFrame -> Maybe RdrName
pPatVar epf = case epf of
  FrameVar n@(Unqual occ) | isVarOcc occ -> Just n
  FramePar _ (L _ (FrameInfix [L _ el])) -> frameInfixElOpName el
  _ -> Nothing

checkSigVar :: LExpPatFrame -> P (Located RdrName)
checkSigVar (L l epf) = case pPatVar epf of
  Just n -> return (L l n)
  Nothing -> failSpanMsgP l $
    text "Comma-separated entities in a type signature" $$
    text "must be variables."

checkAsPatVar :: LExpPatFrame -> P (Located RdrName)
checkAsPatVar (L l epf) = case pPatVar epf of
  Just n -> return (L l n)
  Nothing -> failSpanMsgP l $
    text "@-pattern must bind a variable."

mkRecConstrOrUpdate
  :: LExpPatFrame
  -> SrcSpan
  -> ([LHsRecField GhcPs LExpPatFrame], Bool)
  -> P ExpPatFrame
mkRecConstrOrUpdate (L l (FrameVar c)) _ (fs,dd)
  | isRdrDataCon c
  = return (FrameRecordCon (L l c) (mk_rec_fields fs dd))
mkRecConstrOrUpdate exp@(L l _) _ (fs,dd)
  | dd        = failSpanMsgP l (text "You cannot use `..' in a record update")
  | otherwise = return (FrameRecordUpd exp (map (fmap mk_rec_upd_field) fs))

mk_rec_fields :: [LHsRecField id arg] -> Bool -> HsRecFields id arg
mk_rec_fields fs False =
  HsRecFields { rec_flds = fs, rec_dotdot = Nothing }
mk_rec_fields fs True  =
  HsRecFields { rec_flds = fs, rec_dotdot = Just (length fs) }

mk_rec_upd_field :: HsRecField GhcPs LExpPatFrame -> FrameRecUpdField
mk_rec_upd_field (HsRecField (L loc (FieldOcc _ rdr)) arg pun)
  = HsRecField (L loc (Unambiguous noExt rdr)) arg pun
mk_rec_upd_field (HsRecField (L _ (XFieldOcc _)) _ _)
  = panic "mk_rec_upd_field"

placeHolderPunRhs :: LExpPatFrame
-- The RHS of a punned record field will be filled in by the renamer It's
-- better not to make it an error, in case we want to print it when debugging
placeHolderPunRhs = noLoc (FrameVar pun_RDR)

pun_RDR :: RdrName
pun_RDR = mkUnqual varName (fsLit "pun-right-hand-side")

mkFrameSCC :: Located (([AddAnn],SourceText),StringLiteral)
        -> LExpPatFrame
        -> P LExpPatFrame
mkFrameSCC (L scc_loc scc_ann) expr@(L expr_loc _) = do
  let loc = combineSrcSpans scc_loc expr_loc
  addAnnsAt loc (fst $ fst scc_ann)
  return $ L loc $
    FrameSCC
      (snd $ fst scc_ann)
      (snd scc_ann)
      expr

mkFrameTickPragma :: Located ((([AddAnn],SourceText),
                            (StringLiteral,(Int,Int),(Int,Int))),
                           ((SourceText,SourceText),
                            (SourceText,SourceText)))
               -> LExpPatFrame
               -> P LExpPatFrame
mkFrameTickPragma (L tick_loc tick_ann) expr@(L expr_loc _) = do
  let loc = combineSrcSpans tick_loc expr_loc
  addAnnsAt loc (fst $ fst $ fst tick_ann)
  return $ L loc $
    FrameTickPragma
      (snd $ fst $ fst tick_ann)
      (snd $ fst tick_ann)
      (snd $ tick_ann)
      expr

mkFrameCoreAnn :: Located (([AddAnn],SourceText),StringLiteral)
            -> LExpPatFrame
            -> P LExpPatFrame
mkFrameCoreAnn (L core_loc core_ann) expr@(L expr_loc _) = do
  let loc = combineSrcSpans core_loc expr_loc
  addAnnsAt loc (fst $ fst core_ann)
  return $ L loc $
    FrameCoreAnn
      (snd $ fst core_ann)
      (snd core_ann)
      expr

-- | Yield a parse error if we have a function applied directly to a do block
-- etc. and BlockArguments is not enabled.
checkBlockArguments :: LHsExpr GhcPs -> P ()
checkBlockArguments expr = case unLoc expr of
    HsDo _ DoExpr _ -> check "do block"
    HsDo _ MDoExpr _ -> check "mdo block"
    HsLam {} -> check "lambda expression"
    HsCase {} -> check "case expression"
    HsLamCase {} -> check "lambda-case expression"
    HsLet {} -> check "let expression"
    HsIf {} -> check "if expression"
    HsProc {} -> check "proc expression"
    _ -> return ()
  where
    check element = do
      pState <- getPState
      unless (extopt LangExt.BlockArguments (options pState)) $
        failSpanMsgP (getLoc expr) $
          text "Unexpected " <> text element <> text " in function application:"
           $$ nest 4 (ppr expr)
           $$ text "You could write it with parentheses"
           $$ text "Or perhaps you meant to enable BlockArguments?"

pprInfixEPF :: ExpPatFrame -> SDoc
pprInfixEPF epf = case epf of
  FrameVar name -> pprInfixOcc name
  FramePar _ (L _ (FrameInfix [L _ el]))
    | Just e <- frameInfixElOp el
    -> pprInfixEPF e
  _ -> char '`' <> pprPrefixEPF epf <> char '`'

pprPrefixEPF :: ExpPatFrame -> SDoc
pprPrefixEPF epf = case epf of
  FrameVar name -> pprPrefixOcc name
  FrameIPVar ipname -> ppr ipname
  FrameOverLabel str -> char '#' <> ppr str
  FrameLit lit -> ppr lit
  FrameOverLit lit -> ppr lit
  FramePar _ (L _ (FrameInfix [L _ el]))
    | Just e <- frameInfixElOp el
    -> pprPrefixEPF e
  FramePar _ (L _ e) -> parens (pprPrefixEPF e)
  FrameSum alt arity (L _ expr) boxity ->
    let
      ppr_bars n = hsep (replicate n (char '|'))
      (lpar, rpar) = case boxity of
        Boxed   -> ("(", ")")
        Unboxed -> ("(#", "#)")
    in
      text lpar <+> ppr_bars (alt - 1)
                <+> pprPrefixEPF expr
                <+> ppr_bars (arity - alt)
                <+> text rpar
  FrameTuple args boxity ->
    let
      (lpar, rpar) = case boxity of
        Boxed   -> ("(", ")")
        Unboxed -> ("(#", "#)")
      ppr_tup_args [] = []
      ppr_tup_args (L _ (TupArgFramePresent (L _ e)) : es) =
        (pprPrefixEPF e <> punc es) : ppr_tup_args es
      ppr_tup_args (L _ TupArgFrameMissing : es) =
        punc es : ppr_tup_args es
      punc (L _ TupArgFramePresent{} : _) = comma <> space
      punc (L _ TupArgFrameMissing{} : _) = comma
      punc [] = empty
    in
      text lpar <+> fcat (ppr_tup_args args)
                <+> text rpar
  FrameList xs ->
    let xdocs = map (pprPrefixEPF . unLoc) xs
    in brackets (pprDeeperList fsep (punctuate comma xdocs))
  -- FrameComp (HsStmtContext Name) [ExprLStmt GhcPs] (LHsExpr GhcPs)
  FrameComp{} -> text "TODO (int-index): pprExpPatFrame FrameComp"
  -- FrameArithSeq (ArithSeqInfo GhcPs)
  FrameArithSeq{} -> text "TODO (int-index): pprExpPatFrame FrameArithSeq"
  FrameWild -> text "_"
  -- FrameSplice (HsSplice GhcPs)
  FrameSplice{} -> text "TODO (int-index): pprExpPatFrame FrameSplice"
  -- FrameBracket (HsBracket GhcPs)
  FrameBracket{} -> text "TODO (int-index): pprExpPatFrame FrameBracket"
  -- FrameArrForm (LHsExpr GhcPs) [LHsCmdTop GhcPs]
  FrameArrForm{} -> text "TODO (int-index): pprExpPatFrame FrameArrForm"
  FrameRecordUpd e flds ->
    hang (ppr e) 2 (braces (fsep (punctuate comma (map ppr flds))))
  FrameRecordCon con flds -> hang (ppr con) 2 (ppr flds)
  FrameAsPat n p -> ppr n <> char '@' <> ppr p
  FrameLam matches -> pprMatches matches
  -- special case: let ... in let ...
  FrameLet (L _ binds) expr@(L _ (HsLet _ _ _)) ->
    sep [hang (text "let") 2 (hsep [pprBinds binds, ptext (sLit "in")]),
         ppr_lexpr expr]
  FrameLet (L _ binds) expr ->
    sep [hang (text "let") 2 (pprBinds binds),
         hang (text "in")  2 (ppr expr)]
  FrameLamCase matches ->
    sep [ sep [text "\\case"],
          nest 2 (pprMatches matches) ]
  -- FrameIf (LHsExpr GhcPs) (LHsExpr GhcPs) (LHsExpr GhcPs)
  FrameIf{} -> text "TODO (int-index): pprExpPatFrame FrameIf"
  -- FrameMultiIf [LGRHS GhcPs (LHsExpr GhcPs)]
  FrameMultiIf{} -> text "TODO (int-index): pprExpPatFrame FrameMultiIf"
  FrameCase scrut matches ->
    case matches of
      MG { mg_alts = L _ [_] } ->
        sep [ sep [text "case",
                   nest 4 (ppr scrut),
                   text "of {"],
              nest 2 (pprMatches matches) <+> char '}']
      _ ->
        sep [ sep [text "case",
                   nest 4 (ppr scrut),
                   text "of"],
              nest 2 (pprMatches matches) ]
  FrameDo do_or_list_comp stmts ->
    pprDo do_or_list_comp stmts
  -- FrameProc (LPat GhcPs) (LHsCmdTop GhcPs)
  FrameProc{} -> text "TODO (int-index): pprExpPatFrame FrameProc"
  FrameViewPat e p -> ppr e <+> text "->" <+> ppr p
  -- FrameTySig LExpPatFrame (LHsSigWcType GhcPs)
  FrameTySig{} -> text "TODO (int-index): pprExpPatFrame FrameTySig"
  -- FrameArrApp LExpPatFrame LExpPatFrame HsArrAppType Bool
  FrameArrApp{} -> text "TODO (int-index): pprExpPatFrame FrameArrApp"
  -- FrameSCC SourceText StringLiteral LExpPatFrame
  FrameSCC{} -> text "TODO (int-index): pprExpPatFrame FrameSCC"
  -- FrameTickPragma
   -- SourceText
   -- (StringLiteral,(Int,Int),(Int,Int))
   -- ((SourceText,SourceText),(SourceText,SourceText))
   -- LExpPatFrame
  FrameTickPragma{} -> text "TODO (int-index): pprExpPatFrame FrameTickPragma"
  -- FrameCoreAnn SourceText StringLiteral LExpPatFrame
  FrameCoreAnn{} -> text "TODO (int-index): pprExpPatFrame FrameCoreAnn"
  FrameInfix els -> hsep (map ppr els)

instance Outputable ExpPatFrame where
  ppr = pprPrefixEPF

instance Outputable FrameInfixEl where
  ppr el = case el of
    FrameOpr a -> pprInfixEPF a
    FrameOpd a -> pprPrefixEPF a
    FrameVisTy _ t -> char '@' <> ppr t
    FrameMinus -> char '-'
    FrameTilde -> char '~'
    FrameBang  -> char '!'
    FrameDot   -> char '.'
    FrameStar isUni -> text (starOpSym isUni)
    FrameStatic -> text "static"

data PatFunFrame
  = PatFrame (LPat GhcPs) -- includes variables: x, !x
  | FunFrame
      [AddAnn]          -- annotations
      Bool              -- in parens? TODO (int-index): newtype
      (Located RdrName) -- function name: f, +
      LexicalFixity     -- infix or prefix?
      [LPat GhcPs]      -- args (len >= 1)

checkPatVar :: Located RdrName -> Pat GhcPs
checkPatVar (L l name)
  | isRdrDataCon name = ConPatIn (L l name) (PrefixCon [])
  | otherwise = VarPat noExt (L l name)

checkPatFun :: SDoc -> LExpPatFrame -> P PatFunFrame
checkPatFun msg (L l epf) = getPState >>= \pState -> case epf of
  FrameVar name -> return (PatFrame (L l (checkPatVar (L l name))))
  FrameIPVar{} -> patSynIllegal msg l epf "implicit parameter"
  FrameOverLabel{} -> patSynIllegal msg l epf "overloaded label"
  FrameLit HsStringPrim{} ->
    -- See Trac #13260
    patSynIllegal msg l epf "unboxed string literal"
  FrameLit lit -> return (PatFrame (L l (LitPat noExt lit)))
  FrameOverLit lit -> return (PatFrame (L l (mkNPat (L l lit) Nothing)))
  FrameInfix els  -- See Note [Parsing n+k patterns]
    | extopt LangExt.NPlusKPatterns (options pState),
      Just p <- pNPlusK els
    -> return (PatFrame p)
  FrameInfix els -> mergeInfixPat msg els
  FramePar _ (L _ (FrameInfix [L _ el]))
    | Just op <- frameInfixElOpName el
    -> return (PatFrame (L l (checkPatVar (L l op))))
  FramePar (l_open, l_close) pf -> do
    pf' <- checkPatFun msg pf
    case pf' of
      PatFrame p -> return (PatFrame (L l (ParPat noExt p)))
      FunFrame ffAnns _ name fixity args ->
        let ffAnns' = (\loc -> addAnnotation loc AnnOpenP l_open) :
                      (\loc -> addAnnotation loc AnnCloseP l_close) :
                      ffAnns
        in return (FunFrame ffAnns' True name fixity args)
  FrameSum alt arity p boxity -> do
    checkSumBoxity l alt arity (unLoc p) boxity
    p' <- checkPat msg p
    return (PatFrame (L l (SumPat noExt p' alt arity)))
  FrameTuple args boxity -> do
    let
      checkArg (L _ (TupArgFramePresent p)) =
        checkPat msg p
      checkArg (L l' TupArgFrameMissing) =
        patSynIllegal msg l' epf "tuple section"
    args' <- traverse checkArg args
    return (PatFrame (L l (TuplePat noExt args' boxity)))
  FrameList xs -> do
    xs' <- traverse (checkPat msg) xs
    return (PatFrame (L l (ListPat noExt xs')))
  FrameComp{} -> patSynIllegal msg l epf "list comprehension"
  FrameArithSeq{} -> patSynIllegal msg l epf "arithmetic sequence"
  FrameWild -> return (PatFrame (L l (WildPat noExt)))
  FrameSplice splice ->
    if isTypedSplice splice
      then patSynIllegal msg l epf "typed splice"
      else return (PatFrame (L l (SplicePat noExt splice)))
  FrameBracket{} -> patSynIllegal msg l epf "TemplateHaskell syntax"
  FrameArrForm{} -> patSynIllegal msg l epf "arrow formation"
  FrameRecordUpd{} -> patSynIllegal msg l epf "record update"
  FrameRecordCon con flds -> do
    flds' <- traverse (checkPat msg) flds
    return (PatFrame (L l (ConPatIn con (RecCon flds'))))
  FrameAsPat n p -> do
    n' <- checkAsPatVar n
    p' <- checkPat msg p
    return (PatFrame (L l (AsPat noExt n' p')))
  FrameLam{} -> patSynIllegal msg l epf "lambda"
  FrameLet{} -> patSynIllegal msg l epf "let-binding"
  FrameLamCase{} -> patSynIllegal msg l epf "lambda-case"
  FrameIf{} -> patSynIllegal msg l epf "if-expression"
  FrameMultiIf{} -> patSynIllegal msg l epf "multi-way if-expression"
  FrameCase{} -> patSynIllegal msg l epf "case-expression"
  FrameDo{} -> patSynIllegal msg l epf "do-notation"
  FrameProc{} -> patSynIllegal msg l epf "proc-notation"
  FrameViewPat e p -> do
    e' <- checkExpr e
    p' <- checkPat msg p
    return (PatFrame (L l (ViewPat noExt e' p')))
  FrameTySig e sig -> do
    e' <- checkPat msg e
    return (PatFrame (L l (SigPat noExt e' sig)))
  FrameArrApp{} -> patSynIllegal msg l epf "arrow application"
  FrameSCC{} -> patSynIllegal msg l epf "pragma"
  FrameTickPragma{} -> patSynIllegal msg l epf "pragma"
  FrameCoreAnn{} -> patSynIllegal msg l epf "pragma"

{- Note [Parsing n+k patterns]

Even when NPlusKPatterns are enabled, we want to parse this
as a function declaration (FunBind) for (+):

n+1 = ...    -- now (+) is defined

Parentheses turn this into a PatBind:

(n+1) = 5    -- now n=4 is defined

The first case is handled by 'checkFunPatBind', which relies on 'mergeInfixPat'
to put together [1, +, n]. Therefore, it is important that we check for n+k
patterns outside 'mergeInfixPat'.

The second case is handled by 'checkPatFun', which seems to be the right place
to put the check.

-}

matchPatFrame :: SDoc -> PatFunFrame -> P (LPat GhcPs)
matchPatFrame _ (PatFrame p) = return p
matchPatFrame other_hint (FunFrame _ _ (L l1 name) _ _) =
    failSpanMsgP l1 (baseMsg $$ hint)
  where
    hint
      | name == mkUnqual varName (fsLit "rec") = recDoHint
      | otherwise = other_hint
    baseMsg = text "Illegal function binding in pattern:" <+>
              ppr name
    recDoHint = text "Perhaps you intended to use RecursiveDo?"

checkPat :: SDoc -> LExpPatFrame -> P (LPat GhcPs)
checkPat msg a = checkPatFun msg a >>= matchPatFrame msg

patSynIllegal :: SDoc -> SrcSpan -> ExpPatFrame -> String -> P a
patSynIllegal hint l epf s = failSpanMsgP l (baseMsg $$ hint)
  where
    baseMsg =
      text "Illegal" <+> text s <+> text "in pattern:" $$
      nest 2 (pprPrefixEPF epf)

-- TODO (int-index): test case    ~ !(f a) x = ()
funBindStrIllegal :: [SrcStrictness] -> Located RdrName -> P a
funBindStrIllegal ss (L l name) =
  failSpanMsgP l $
    text "Illegal strictness annotation" <+>
    text "in a function binding:" $$
    nest 2 (hsep (map ppr ss) <> pprPrefixOcc name)

-- Extract laziness/strictness annotations for patterns.
pPatBangTilde
  :: Bool            -- BangPatterns enabled?
  -> [LFrameInfixEl] -- reversed elements
  -> ( LPat GhcPs -> P (LPat GhcPs), {- transform a pattern and add annotations -}
       [SrcStrictness], {- strictness annotations -}
       [LFrameInfixEl] {- remaining reversed elements -} )
pPatBangTilde bang_on = go [] return
  where
    go ss f (L l FrameBang : xs)
      | bang_on || beforeUnary xs -- See Note [Parsing BangPatterns]
      = go (SrcStrict:ss) (f >=> mkBangPat l) xs
    go ss f (L l FrameTilde : xs)
      = go (SrcLazy:ss) (f >=> mkLazyPat l) xs
    go ss f xs = (f, ss, xs)

mkBangPat, mkLazyPat :: SrcSpan -> LPat GhcPs -> P (LPat GhcPs)
mkBangPat l p = do
  let l' = combineSrcSpans l (getLoc p)
  addAnnotation l' AnnBang l
  return (L l' (BangPat noExt p))
mkLazyPat l p = do
  let l' = combineSrcSpans l (getLoc p)
  addAnnotation l' AnnTilde l
  return (L l' (LazyPat noExt p))

-- TODO (int-index): Should we handle (C ! a) now?
-- It used to be accepted without BangPatterns
-- before this patch (?). Must document the change.

{- Note [Parsing BangPatterns]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

There are definitions that can be parsed differently depending on whether
BangPatterns are enabled:

          f ! a = ...
  means   (!) f a = ...   without -XBangPatterns
  but     f (!a)  = ...   with    -XBangPatterns

At the same time, there are definitions that are unambiguously bang patterns
regardless of -XBangPatterns:

  !x = ...
  !a + !b = ...

We can achieve superior error messages if we reject them in the renamer.

-}

pNPlusK :: [LFrameInfixEl] -> Maybe (LPat GhcPs)
pNPlusK [L y_loc y, L op_loc op, L x_loc x]
  | FrameOpr (FrameVar plus) <- op,
    plus == mkUnqual varName (fsLit "+"),
    FrameOpd x_opd <- x,
    Just n <- pPatVar x_opd,
    FrameOpd (FrameOverLit k) <- y,
    OverLit {ol_val = HsIntegral{}} <- k
  = let loc = x_loc `combineSrcSpans` op_loc `combineSrcSpans` y_loc
    in Just (L loc (mkNPlusKPat (L x_loc n) (L y_loc k)))
pNPlusK _ = Nothing

mergeInfixPat :: SDoc -> [LFrameInfixEl] -> P PatFunFrame
mergeInfixPat msg all_xs = go [] [] [] all_xs
  where
    go :: [PatFunFrame]
       -> [(Located RdrName, LPat GhcPs)]
       -> [(Located RdrName, LPat GhcPs)]
       -> [LFrameInfixEl]
       -> P PatFunFrame

    go acc con_ops_acc ops_acc [] = goEnd acc con_ops_acc ops_acc

    go acc con_ops_acc ops_acc (L l (FrameOpd a):xs) =
      do { pf <- checkPatFun msg (L l a)
         ; bang_on <- extension bangPatEnabled
         ; let (addBangTilde, ss, xs') = pPatBangTilde bang_on xs
         ; pf' <- case pf of
             PatFrame p -> PatFrame <$> addBangTilde p
             ff@(FunFrame _ _ name _ _) ->
               if null ss then return ff
                          else funBindStrIllegal ss name
         ; go (pf':acc) con_ops_acc ops_acc xs' }

    go acc con_ops_acc ops_acc (L l (FrameOpr op):xs)
      | null acc = missingRhsErr (L l op) xs
      | otherwise =
          do { a <- mergeAcc acc
             ; case op of
                FrameVar name | isRdrDataCon name ->
                  go [] ((L l name, a):con_ops_acc) ops_acc xs
                FrameVar name ->
                  let b = mergeConOpsAcc a con_ops_acc
                  in go [] [] ((L l name, b):ops_acc) xs
                _ ->
                  failSpanMsgP l $
                    text "Not an infix constructor name:" $$
                    nest 2 (pprPrefixEPF op) }

    go _ _ _ (L l (FrameVisTy _ t):_) =
      failSpanMsgP l $
        text "Type applications in patterns are not implemented:" $$
        nest 2 (text "@" <> ppr t)

    go acc con_ops_acc ops_acc (L op_l FrameMinus:xs)
      | beforeUnary xs
      = do { L l pos_lit <- case acc of
               [PatFrame (L l (NPat _ lit Nothing _))] ->
                 return (L l lit)
               _ -> failSpanMsgP op_l $
                 text "Unary minus in patterns can only be used" <+>
                 text "with numeric literals."
           ; let loc = combineSrcSpans op_l l
                 npat = mkNPat pos_lit (Just noSyntaxExpr)
           ; addAnnotation loc AnnMinus op_l
           ; go [PatFrame (L loc npat)] con_ops_acc ops_acc xs }

    go acc con_ops_acc ops_acc (L l FrameMinus:xs) =
      go acc con_ops_acc ops_acc ((L l (mkFrameOpr "-")):xs)

    go acc con_ops_acc ops_acc (L l FrameDot:xs) =
      go acc con_ops_acc ops_acc ((L l (mkFrameOpr ".")):xs)

    go acc con_ops_acc ops_acc (L l (FrameStar isUni):xs) =
      go acc con_ops_acc ops_acc ((L l (mkFrameOpr (starOpSym isUni))):xs)

    go acc con_ops_acc ops_acc (L l FrameBang : xs) = do
      bang_on <- extension bangPatEnabled
      if bang_on
        then failSpanMsgP l $
             text "Strictness annotation in an invalid position."
        else do
          case acc of
            PatFrame (L l_acc _):_ | srcSpanEnd l == srcSpanStart l_acc
              -> warnSpaceAfterBang l
            _ -> return ()
          go acc con_ops_acc ops_acc ((L l (mkFrameOpr "!")):xs)

    go _ _ _ (L l FrameTilde : _) = do
      -- See Note [Tilde operator]
      failSpanMsgP l $
        text "Laziness annotation in an invalid position."

    go _ _ _ (L l FrameStatic:_) = do
      failSpanMsgP l $
        text "Static pointer syntax cannot be used in patterns."

    goEnd [] [] [] = panic "mergeInfixPat.goEnd: empty input"
    goEnd (FunFrame ffAnns par name fixity argsx : args) [] [] = do
      args' <- traverse (matchPatFrame msg) args
      return (FunFrame ffAnns (par && null args) name fixity (argsx ++ args'))
    goEnd (PatFrame (L l1 p1):args) [] []
      | null args = return (PatFrame (L l1 p1))
      | VarPat _ name <- p1 = do
          args' <- traverse (matchPatFrame msg) args
          return (FunFrame [] False name Prefix args')
      | ConPatIn name (PrefixCon []) <- p1 = do
          args' <- traverse (matchPatFrame msg) args
          return (PatFrame (mkConPat name args'))
      | otherwise =
          failSpanMsgP l1 $
            text "Not a function or constructor name:" $$
            nest 2 (ppr p1)
    goEnd acc con_ops_acc@((L l con_op,_):_) [] =
      do { when (null acc) $ missingLhsErr (L l (FrameVar con_op))
         ; a <- mergeAcc acc
         ; return (PatFrame (mergeConOpsAcc a con_ops_acc)) }
    goEnd acc con_ops_acc ops_acc@((op,y):xs)
      | null xs =
          do { when (null acc) $
                 missingLhsErr (mapLoc FrameVar
                               (case con_ops_acc of
                                    (con_op, _):_ -> con_op
                                    _ -> op))
             ; a <- mergeAcc acc
             ; let x = mergeConOpsAcc a con_ops_acc
             ; return (FunFrame [] False op Infix [x, y]) }
      | otherwise = multipleOperatorsErr (map fst ops_acc)

    multipleOperatorsErr ops =
      failSpanMsgP loc $
        text "Multiple infix operators in a single declaration:" $$
        nest 2 (hsep (map ppr ops))
      where
        loc = foldr combineSrcSpans noSrcSpan (map getLoc all_xs)

    mergeAcc :: [PatFunFrame] -> P (LPat GhcPs)
    mergeAcc [] = panic "mergeInfixPat.mergeAcc: empty input"
    mergeAcc [p] = matchPatFrame msg p
    mergeAcc (f : args) = do
      L l1 p1 <- matchPatFrame msg f
      args' <- traverse (matchPatFrame msg) args
      case p1 of
        ConPatIn name (PrefixCon []) ->
          return (mkConPat name args')
        _ ->
          failSpanMsgP l1 $
            text "Not a constructor name:" $$
            nest 2 (ppr p1)

    mergeConOpsAcc = foldl' (\a (op, b) -> mkLConOp a op b)

missingLhsErr :: LExpPatFrame -> P a
missingLhsErr (L l op) = failSpanMsgP l (baseMsg $$ hint)
  where
    baseMsg =
      text "Operator is missing a left-hand side argument:" <+>
      pprInfixEPF op
    hint
      | FrameVar opname <- op,
        opname == mkUnqual varName (fsLit "$")
      = text "Perhaps you intended to use TemplateHaskell?"
      | otherwise = empty


missingRhsErr :: LExpPatFrame -> [LFrameInfixEl] -> P a
missingRhsErr (L l op) xs = failSpanMsgP l (baseMsg $$ hint)
  where
    baseMsg =
      text "Operator is missing a right-hand side argument:" <+>
      pprInfixEPF op
    hint
      | FrameVar opname <- op,
        opname == mkUnqual varName (fsLit "#"),
        L lnext (FrameOpd (FrameVar (Unqual _))):_ <- xs,
        srcSpanEnd lnext == srcSpanStart l
      = text "Perhaps you meant to enable MagicHash?"
      | otherwise = empty

mkConPat :: Located RdrName -> [LPat GhcPs] -> LPat GhcPs
mkConPat name@(L l1 _) args =
  let loc = foldl' combineSrcSpans l1 (map getLoc args)
  in L loc (ConPatIn name (PrefixCon args))

matchVarPat :: LPat GhcPs -> Maybe (SrcStrictness, Located RdrName)
matchVarPat (L _ (LazyPat _ (L _ (VarPat _ name)))) = Just (SrcLazy, name)
matchVarPat (L _ (BangPat _ (L _ (VarPat _ name)))) = Just (SrcStrict, name)
matchVarPat (L _ (VarPat _ name)) = Just (NoSrcStrict, name)
matchVarPat _ = Nothing

mkLConOp :: LPat GhcPs -> Located RdrName -> LPat GhcPs -> LPat GhcPs
mkLConOp x op y =
  let loc = getLoc x `combineSrcSpans` getLoc op `combineSrcSpans` getLoc y
  in L loc (ConPatIn op (InfixCon x y))

checkFunPatBind
  :: LExpPatFrame
  -> ([AddAnn], Maybe (LHsType GhcPs))
  -> Located ([AddAnn],GRHSs GhcPs (LHsExpr GhcPs))
  -> P (HsBind GhcPs)
checkFunPatBind (L lhs_loc lhs_epf)
                (_sigAnns, Nothing)
                (L rhs_loc (rhsAnns, grhss))
  = do { pff <- mergeInfixPat empty (assumeFrameInfix lhs_epf)
          -- See Note [Parsing n+k patterns]
       ; let loc = combineSrcSpans lhs_loc rhs_loc
       ; addAnnsAt loc rhsAnns -- sigAnns == []
       ; case pff of
           FunFrame ffAnns par name fixity args -> do
             addAnnsAt loc ffAnns
             when par $
               -- This restriction is tested by 'readFail022'. We only
               -- have the 'par' flag in FunFrame for this check.
               failSpanMsgP (getLoc name) $
                 text "Function binding for" <+> pprPrefixOcc (unLoc name) <+>
                 text "is parenthesized," $$
                 text "but there are no more parameters" <+>
                 text "after the closing parenthesis." $$
                 text "This is disallowed."
             addAnnotation loc AnnFunId (getLoc name)
             return $
               let ctxt = FunRhs name fixity NoSrcStrict
                   match = Match noExt ctxt args grhss
               in makeFunBind name [L loc match]
           PatFrame p ->
             case matchVarPat p of
               Just (strictness, name) -> do
                 addAnnotation loc AnnFunId (getLoc name)
                 return $
                   let ctxt = FunRhs name Prefix strictness
                       match = Match noExt ctxt [] grhss
                   in makeFunBind name [L loc match]
               Nothing ->
                 return $ PatBind noExt p grhss ([], []) }
  where
    assumeFrameInfix (FrameInfix xs) = xs
    assumeFrameInfix _ = panic "checkFunPatBind: lhs not FrameInfix"

checkFunPatBind lhs
                (sigAnns, Just sig)
                (L rhs_loc (rhsAnns, grhss))
  = do { let lhs' = FrameTySig lhs (mkLHsSigWcType sig)
             loc_p = combineSrcSpans (getLoc lhs) (getLoc sig)
             loc = combineSrcSpans loc_p rhs_loc
       ; addAnnsAt loc_p sigAnns
       ; addAnnsAt loc rhsAnns
       ; p <- checkPat empty (L loc_p lhs')
       ; return (PatBind noExt p grhss ([], [])) }

-- | Warn about missing space after bang
warnSpaceAfterBang :: SrcSpan -> P ()
warnSpaceAfterBang span =
  addWarning DynFlags.Opt_WarnSpaceAfterBang span $
    text "Did you forget to enable BangPatterns?" $$
    text "If you mean to bind (!) then perhaps you want" $$
    text "to add a space after the bang for clarity."

{- Note [Infix operators at the start of do statements]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Before ExpPatFrame, we used to accept this code:

  do fmap ModuleRenaming parseRns
     <++ parseHidingRenaming
     <++ return DefaultRenaming

(taken from Cabal sources)

In this example, we shift and parse it as

  do (fmap ModuleRenaming parseRns
     <++ parseHidingRenaming
     <++ return DefaultRenaming)

rather than

  do (fmap ModuleRenaming parseRns)
     (<++ parseHidingRenaming)
     (<++ return DefaultRenaming)

However, this behavior is hard to support. Consider these similar examples:

  (a)    main = do putStrLn
                   $"Hello, World"

  (b)    (!) = ($)
         main = do putStrLn
                   !"Hello, World"

In (a), we shift in the same manner and it is a successful parse.
In (b), however, we parse don't shift (because the bang has special treatment)
and fail.

This is even with BangPatterns disabled.

With ExpPatFrame, we never shift, so none of the examples above are allowed.
-}
