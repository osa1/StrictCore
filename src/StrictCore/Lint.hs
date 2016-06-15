-- FIXME: This module needs some extra exports from CoreLint

module StrictCore.Lint where

--------------------------------------------------------------------------------

import           Bag
import           BasicTypes
import           CoreLint          hiding (lintExpr)
import           DataCon
import           DynFlags
import           ErrUtils
import           Id
import           Literal           (literalType)
import           Outputable
import           TyCoRep
import           Type
import           TysWiredIn        (mkTupleTy)

import           StrictCore.Syntax

import           Control.Monad     (mapM_)

--------------------------------------------------------------------------------

-- | Returns (warnings, errors).
lintCoreProgram :: DynFlags -> [Var] -> [Bind] -> (Bag MsgDoc, Bag MsgDoc)
lintCoreProgram dflags in_scope binds
  = initL dflags (error "LintFlags should not be used!") $
    addLoc TopLevelBindings $
    addInScopeVars in_scope $
    addInScopeVars (bindersOfBinds binds) $
    mapM_ lintBind binds

lintBind :: Bind -> LintM ()
lintBind (NonRec bndr rhs) = lintSingleBind bndr rhs
lintBind (Rec bs)          = mapM_ (uncurry lintSingleBind) bs

lintSingleBind :: Bndr -> Value -> LintM ()
lintSingleBind bndr rhs
  = addLoc (RhsOf bndr) $ do
    rhs_ty <- lintValue rhs
    binder_ty <- applySubstTy (idType bndr)
    ensureEqTys binder_ty rhs_ty (mkRhsMsg bndr (text "RHS") rhs_ty)

--------------------------------------------------------------------------------

lintValue :: Value -> LintM Type

lintValue (Lam as body)
  = addLoc (BodyOfLetRec as) $ -- FIXME: LambdaBodyOf wants an Id so can't use it here
    lintBinders as $ \as' -> do
      body_ty <- lintExpr body
      return (mkPiTypes as' body_ty)

lintValue (Con con as)
  = do con_ty <- lintCon con
       -- FIXME: Can't addLoc here... We need more Loc types
       lintConApp con_ty as

lintValue (Lit lit)
  = return (literalType lit)

--------------------------------------------------------------------------------

lintExpr :: Expr -> LintM Type
lintExpr = undefined

--------------------------------------------------------------------------------

lintAtom :: Atom -> LintM Type

lintAtom (AVar id)
  = return (idType id)

lintAtom (ALit lit)
  = return (literalType lit)

--------------------------------------------------------------------------------

lintCon :: DataCon -> LintM Type
lintCon =
  -- TODO: This is probably wrong... Don't we at least need to instantiate TyCon
  -- ty args?
  return . idType . dataConWorkId

lintConApp :: Type -> [Atom] -> LintM Type
lintConApp con_ty as
  = do as_tys <- mapM lintAtom as
       lintApp con_ty as_tys

lintApp :: Type -> [Type] -> LintM Type
lintApp fun_ty args
  | Just (arg, res) <- splitFunTy_maybe fun_ty
  = do ensureEqTys arg (mkTupleTy Unboxed args) -- multi-arity is expressed using unboxed tuples
                   undefined -- TODO
       return res
