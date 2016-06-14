module StrictCore.Syntax where

--------------------------------------------------------------------------------

-- Explicitly import CoreSyn stuff as we re-define some of the stuff defined
import           CoreSyn    (AltCon, AltCon (..), CoreBind, CoreBndr, CoreExpr)
import qualified CoreSyn
import qualified CoreUtils

import           BasicTypes
import           Coercion   (coercionKind, coercionType)
import           DataCon
import           Literal
import           Outputable hiding (panic)
import           Pair       (pSnd)
import           TyCon
import           TyCoRep
import           Type
import           TysWiredIn
import           Var
import           VarSet

import           Data.Maybe (isJust)

--------------------------------------------------------------------------------
-- * Terms

-- | Non-ANF terms.
data Expr
  = MultiVal [Expr]
      -- ^ Return multiple values. (singleton list is OK)

  | Lit Literal

  | Var Id

  | Let Bndrs Expr Expr
      -- ^ Evaluation.

  | ValRec [Bind] Expr
      -- ^ Allocation.

  | App Expr [Expr]
      -- ^ Application.

  | Lam Bndrs Expr
      -- ^ Lambda takes multiple arguments now.

  | Case Expr [Alt]
      -- TODO: Do we need a binder here to bind the scrutinee?

  | Type Type

  | Cast Expr Coercion

  | Coercion Coercion
    -- TODO: Is this needed?

type Bndr  = CoreBndr
type Bndrs = [CoreBndr]

type Bind  = (Bndr, Expr)

-- NOTE: We use GHC's AltCon but we need to translate DataCons of DataAlt!
-- (translate field types so that they become thunks -- except the
-- bang-patterned ones)
type Alt = (AltCon, Bndrs, Expr)

--------------------------------------------------------------------------------
-- * Translating Haskell types
--
-- For now we assume no unlifted types, and use unboxed tuple syntax for
-- multi-arity values. Empty unboxed tuple is used in thunks. e.g. the thunk
-- syntax in the paper:
--
--     {a}
--
-- is actually a syntactic sugar for:
--
--     <> -> a (Figure 2, bottom row)
--
-- which becomes
--
--     (# #) -> a
--
-- in original Core's type syntax. When translating original Core types, we just
-- make everything thunks. Only exception is when we see a bang pattern in a
-- DataCon.

translateType :: Type -> Type

-- base types become thunks
translateType ty@(TyConApp _ [])
  = mkFunTy (mkTupleTy Unboxed []) ty

-- the rest is just traversal.

translateType ty@(TyVarTy _)
  = ty

translateType (AppTy t1 t2)
  = AppTy (translateType t1) (translateType t2)

translateType (TyConApp tc args)
  = TyConApp tc (map translateType args)

translateType (ForAllTy bndr ty)
  = ForAllTy bndr (translateType ty)

translateType ty@(LitTy _)
  = ty

translateType (CastTy ty co)
  = CastTy (translateType ty) co

translateType (CoercionTy co)
  = CoercionTy co -- FIXME: I think we need to translate coercions too...

--------------------------------------------------------------------------------
-- * Compiling Haskell terms

-- TODO: Need to translate binder types to be able to type check.

translateTerm :: CoreExpr -> Expr
translateTerm (CoreSyn.Var v)
  = Var v

translateTerm (CoreSyn.Lit l)
  = mkThunkTerm (Lit l)

translateTerm e0@(CoreSyn.App _ _)
  = let
      (e1, es) = CoreSyn.collectArgs e0

      -- Hmm... So e1 and es become thunks...
      e1' = translateTerm e1
      es' = map translateTerm es
    in
      -- Returned term should also be a thunk. When forced, it should apply es
      -- to e1. So we get this:
      mkThunkTerm $
        App (mkForceTerm e1') (map mkForceTerm es')

translateTerm e0@(CoreSyn.Lam _ _)
  = let
      (bndrs, e) = CoreSyn.collectBinders e0
      -- TODO: Some of the binders are type binders...
    in
      mkThunkTerm $
        Lam bndrs (translateTerm e)

translateTerm (CoreSyn.Let bind e)
  = ValRec (translateBind bind) (translateTerm e)
      -- TODO: Should we wrap this with a thunk?

translateTerm (CoreSyn.Case scrt _scrt_bndr _ty alts)
  = -- TODO: ignoring scrutinee binder and type for now
    mkThunkTerm $
      Case (translateTerm scrt) (translateAlts alts)

translateTerm (CoreSyn.Cast e co)
  = Cast (translateTerm e) co

translateTerm CoreSyn.Tick{}
  = panic "translateTerm" (text "Tick is not supported")
      -- I don't want to think about this right now ...

translateTerm (CoreSyn.Type ty)
  = Type ty

translateTerm (CoreSyn.Coercion co)
  = Coercion co

translateBind :: CoreBind -> [Bind]
-- Q: Why not remove NonRec in GHC and use a singleton list instead?
translateBind (CoreSyn.NonRec b rhs)
  = [(b, translateTerm rhs)]
translateBind (CoreSyn.Rec bs)
  = map (\(b, rhs) -> (b, translateTerm rhs)) bs

translateAlts :: [CoreSyn.CoreAlt] -> [Alt]
translateAlts = map translateAlt

translateAlt :: CoreSyn.CoreAlt -> Alt
translateAlt (DataAlt con, bndrs, rhs)
  = let
      bndr_strs = zipEqual (text "translateAlt") bndrs (dataConRepStrictness con)
      strict_bndrs = mkVarSet $ map fst $ filter (isMarkedStrict . snd) bndr_strs
    in
      (DataAlt con, bndrs, translateTerm rhs)
        -- TODO: need to update con (for argument info) and bndrs
        -- TODO: strict bndrs shouldn't become thunks in the RHS

translateAlt (lhs, bndrs, rhs)
  = (lhs, bndrs, translateTerm rhs) -- TODO: need to translate bndrs types

--------------------------------------------------------------------------------
-- Building thunks and multi-values. If we change representation of
-- StrictCore-specific things we only change these.
--
-- - Multi-values are just unboxed tuples. In StrictCore we have a term for
--   these, but when we type check we give unboxed tuple types to multi-values.
--
-- - Thunks are just lambdas with empty argument list. When we type check those
--   terms we give them type `(# #) -> a` since there's no explicit thunk type
--   (or nullary lambda) in the original Core type system.

-- | A thunk type in original Core type system is `(# #) -> a`.
mkThunkType :: Type -> Type
mkThunkType = mkFunTy (mkTupleTy Unboxed [])

-- | Check if the type is `(# #) -> a` for some `a`.
isThunkType_maybe :: Type -> Maybe Type
isThunkType_maybe ty
  | Just (arg_ty, ret_ty) <- splitFunTy_maybe ty
  , Just (tc, tc_args)    <- splitTyConApp_maybe arg_ty
  , isUnboxedTupleTyCon tc
  , null (dropRuntimeRepArgs tc_args)
  = Just ret_ty

  | otherwise
  = Nothing

isThunkType :: Type -> Bool
isThunkType = isJust . isThunkType_maybe

-- | We need to explicitly build thunks in StrictCore. A thunk is just a nullary
-- lambda.
mkThunkTerm :: Expr -> Expr
mkThunkTerm = Lam []

-- | Multi-arity is just unboxed tuple in the original Core. Note that unboxed
-- tuples are the only unlifted types we allow for now.
mkMultiArityType :: [Type] -> Type
mkMultiArityType = mkTupleTy Unboxed

-- | Generate term that forces a given thunk. Forcing means just applying the
-- function. (remember that thunks are just nullary lambdas)
mkForceTerm :: Expr -> Expr
mkForceTerm e
  = assert "mkForceTerm" (text "Term is not a thunk:" <+> ppr e) (isThunkType (exprType e)) $
    App e []

--------------------------------------------------------------------------------
-- * Type checking StrictCore

exprType :: Expr -> Type

-- Multi-values are expressed as unboxed tuples in the original Core type system
exprType (MultiVal es)
  = mkTupleTy Unboxed (map exprType es)

exprType (Lit lit)
  = CoreUtils.exprType (CoreSyn.Lit lit)

exprType (Var v)
  = varType v

exprType (Let _ _ _)
  = undefined

exprType (ValRec _ _)
  = undefined

exprType (App fn []) -- Thunk evaluation
  | Just ty <- isThunkType_maybe (exprType fn)
  = ty

exprType (App _ _)
  = undefined

exprType (Lam [] body) -- Thunk
  = mkThunkType (exprType body)

exprType (Lam _ _)
  = undefined

exprType (Case _ _)
  = undefined

exprType ty@Type{}
  = panic "exprType" (text "Found Type:" <+> ppr ty)

exprType (Cast _ co)
  = pSnd (coercionKind co) -- TODO: Shouldn't we check type of the expression here?

exprType (Coercion co)
  = coercionType co

--------------------------------------------------------------------------------
-- * Printing StrictCore

instance Outputable Expr where
  ppr = pprExpr noParens

noParens :: SDoc -> SDoc
noParens = id

pprExpr :: (SDoc -> SDoc) -> Expr -> SDoc

pprExpr _ (MultiVal es)
  = angleBrackets (sep (map (pprExpr parens) es))

pprExpr add_par (Lit lit)
  = pprLiteral add_par lit

pprExpr _ (Var v)
  = ppr v

pprExpr _ (Let _ _ _)
  = undefined

pprExpr _ (ValRec _ _)
  = undefined

pprExpr _ (App e []) -- thunk evaluation
  = char '~' <> pprExpr parens e
      -- there isn't any syntactic sugar for this in the paper,
      -- so making up one.

pprExpr _ (App _ _)
  = undefined

pprExpr _ (Lam [] e) -- thunk
  = braces (pprExpr noParens e)

pprExpr add_par (Lam as e)
  = add_par $ hang (text "\\" <+> sep (map ppr as) <+> arrow)
                   2 (pprExpr noParens e)

pprExpr _ (Case _ _)
  = undefined

pprExpr add_par (Type ty)
  = add_par (text "TYPE:" <+> ppr ty)

pprExpr add_par (Coercion co)
  = add_par (text "CO:" <+> ppr co)

pprExpr add_par (Cast e co)
  = add_par (sep [pprExpr parens e, text "`cast`" <+> pprCo co])

pprCo :: Coercion -> SDoc
pprCo co = parens (sep [ppr co, dcolon <+> ppr (coercionType co)])

--------------------------------------------------------------------------------
-- * Utils

assert :: String -> SDoc -> Bool -> a -> a
assert str msg False _ = pprPanic str msg
assert _   _   True  r = r

panic :: String -> SDoc -> a
panic = pprPanic

zipEqual :: SDoc -> [a] -> [b] -> [(a,b)]
zipEqual _   []     []     = []
zipEqual doc (a:as) (b:bs) = (a,b) : zipEqual doc as bs
zipEqual doc _      _      = panic "zipEqual" (text "unequal lists:" <+> doc)
