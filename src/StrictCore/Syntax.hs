module StrictCore.Syntax where

--------------------------------------------------------------------------------

-- Explicitly import CoreSyn stuff as we re-define some of the stuff defined
import           CoreSyn    (AltCon, CoreBind, CoreBndr, CoreExpr)
import qualified CoreSyn

import           BasicTypes
import           Literal
import           MkCore
import           Outputable hiding (panic)
import           TyCon
import           TyCoRep
import           Type
import           TysWiredIn
import           Var

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
type Alt = (AltCon, Bndrs, Expr)

--------------------------------------------------------------------------------
-- * Compiling Haskell types

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
-- in our type syntax.

translateType :: Type -> Type
translateType ty
  | Just (tc, tc_args) <- splitTyConApp_maybe ty
  , isUnboxedTupleTyCon tc
  = let
      tc_args' = dropRuntimeRepArgs tc_args
    in
      -- We ban unlifted types except tuples
      assert "translateType"
             (text "unlifted unboxed tuple args:" <+> ppr ty)
             (not (any isUnliftedType tc_args')) $
        tc `mkTyConApp` map translateType tc_args

-- No other unlifted type is allowed
translateType ty
  | isUnliftedType ty
  = panic "translateType" (text "Found unlifted type" <+> ppr ty)

translateType ty
  | Just (tc, tc_args) <- splitTyConApp_maybe ty
  = tc `mkTyConApp` map translateType tc_args

-- All other types become thunks
translateType ty
  = mkThunkType ty

--------------------------------------------------------------------------------
-- * Compiling Haskell terms

-- TODO: Need to translate binder types to be able to type check.

translateTerm :: CoreExpr -> Expr
translateTerm (CoreSyn.Var v)
  = mkThunkTerm (Var v)

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
translateAlt (con, bndrs, rhs)
  = (con, bndrs, translateTerm rhs)
      -- TODO: need to update con (for argument info) and bndrs
      -- TODO: strict bndrs shouldn't become thunks in the RHS

--------------------------------------------------------------------------------
-- Building thunks and multi-values. Should we change representation of
-- StrictCore-specific things we only change these.

mkThunkType :: Type -> Type
mkThunkType = mkFunTy (mkTupleTy Unboxed [])

mkThunkTerm :: Expr -> Expr
mkThunkTerm = Lam []

mkForceTerm :: Expr -> Expr
mkForceTerm e = App e []

mkMultiArityType :: [Type] -> Type
mkMultiArityType = mkTupleTy Unboxed

--------------------------------------------------------------------------------
-- * Utils

assert :: String -> SDoc -> Bool -> a -> a
assert str msg False _ = pprPanic str msg
assert _   _   True  r = r

panic :: String -> SDoc -> a
panic = pprPanic
