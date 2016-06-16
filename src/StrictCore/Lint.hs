-- FIXME: This module needs some extra exports from CoreLint

module StrictCore.Lint where

--------------------------------------------------------------------------------

import Bag
import BasicTypes
import CoAxiom (Role (..))
import CoreLint hiding (lintExpr)
import qualified CoreSyn
import DataCon
import DynFlags
import ErrUtils
import Id
import Kind (classifiesTypeWithValues)
import Literal (literalType)
import Outputable
import TyCoRep
import Type
import TysWiredIn (mkTupleTy)

import StrictCore.Syntax

import Control.Monad (mapM_)
import Prelude hiding (id)

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
  = addLoc (BodyOfLetRec (lamBndrBndrs as)) $ -- FIXME: LambdaBodyOf wants an Id so can't use it here
    lintBinders (lamBndrBndrs as) $ \as' -> do
      body_ty <- lintExpr body
      return (mkPiTypes as' body_ty)

lintValue (Con con as)
  = do con_ty  <- lintCon con
       arg_tys <- mapM lintAtom as
       -- TODO: Make sure application is saturated
       lintAtomApp con_ty (zip arg_tys as)

lintValue (Lit lit)
  = return (literalType lit)

--------------------------------------------------------------------------------

lintExpr :: Expr -> LintM Type

lintExpr (MultiVal es)
  = mkTupleTy Unboxed <$> mapM lintExpr es

lintExpr (Value val)
  = lintValue val

lintExpr (Var var)
  = do var' <- lookupIdInScope var
       return (idType var')

lintExpr (Eval _bndrs _rhs _body)
  = undefined

lintExpr (Let _bind _body)
  = undefined

lintExpr (Case _scrt _alts)
  = undefined

lintExpr (App fn args)
  = do fun_ty   <- lintExpr fn
       args_tys <- mapM lintExpr args
       lintApp fun_ty (zip args_tys args)

lintExpr (Type ty)
  = -- TODO: Not sure if this invariant still holds...
    failWithL (text "Type found as expression" <+> ppr ty)

-- Copied from CoreLint with one line of change
lintExpr (Cast expr co)
  = do expr_ty <- lintExpr expr
       co' <- applySubstCo co
       (_, k2, from_ty, to_ty, r) <- lintCoercion co'
       lintL (classifiesTypeWithValues k2)
             (text "Target of cast not # or *:" <+> ppr co)
       lintRole co' Representational r
       ensureEqTys from_ty expr_ty (mkCastErr expr co' from_ty expr_ty)
       return to_ty

lintExpr (Coercion co)
  = lintCoreExpr (CoreSyn.Coercion co)

--------------------------------------------------------------------------------

lintApp :: Type -> [(Type, Expr)] -> LintM Type

lintApp fun_ty [(_, Type ty)]
  = lintCoreArg fun_ty (CoreSyn.Type ty)

lintApp fun_ty [(arg_ty, arg)]
  = lintValApp arg fun_ty arg_ty

lintApp fun_ty args
  = do -- TODO: Make sure `args` doesn't have Type
       lintValApp args fun_ty (mkTupleTy Unboxed (map fst args))

lintAtomApp :: Type -> [(Type, Atom)] -> LintM Type
lintAtomApp fun_ty [(_, AType ty)]
  = lintCoreArg fun_ty (CoreSyn.Type ty)

lintAtomApp fun_ty [(arg_ty, arg)]
  = lintValApp arg fun_ty arg_ty

lintAtomApp fun_ty args
  = do -- TODO: Make sure `args` doesn't have Type
       lintValApp args fun_ty (mkTupleTy Unboxed (map fst args))

--------------------------------------------------------------------------------

lintAtom :: Atom -> LintM Type

lintAtom (AVar id)
  = return (idType id)

lintAtom (ALit lit)
  = return (literalType lit)

lintAtom (AApp a ty)
  = do fun_ty <- lintAtom a
       ty'    <- applySubstTy ty
       lintTyApp fun_ty ty'

-- Copied from CoreLint
lintAtom (ACast a co)
  = do atom_ty <- lintAtom a
       co' <- applySubstCo co
       (_, k2, from_ty, to_ty, r) <- lintCoercion co'
       lintL (classifiesTypeWithValues k2)
             (text "Target of cast not # or *:" <+> ppr co)
       lintRole co' Representational r
       ensureEqTys from_ty atom_ty (mkCastErr a co' from_ty atom_ty)
       return to_ty

lintAtom (AType ty)
  = lintCoreExpr (CoreSyn.Type ty)

--------------------------------------------------------------------------------

lintCon :: DataCon -> LintM Type
lintCon =
  -- TODO: This is probably wrong... Don't we at least need to instantiate TyCon
  -- ty args?
  return . idType . dataConWorkId
