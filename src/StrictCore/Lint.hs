-- FIXME: This module needs some extra exports from CoreLint

module StrictCore.Lint
  ( lintCoreProgram
  ) where

--------------------------------------------------------------------------------

import Bag
import BasicTypes
import CoAxiom (Role (..))
import CoreLint hiding (lintExpr, lintSingleBinding, mkBadAltMsg, mkCaseAltMsg,
                 mkNewTyDataConAltMsg)
import qualified CoreSyn
import DataCon
import DynFlags
import ErrUtils
import Id
import Kind (classifiesTypeWithValues)
import Literal (literalType)
import Outputable
import TyCon
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
  = initL dflags defaultLintFlags $
    addLoc TopLevelBindings $
    addInScopeVars in_scope $
    addInScopeVars (bindersOfBinds binds) $
    mapM_ lintBind binds

lintBind :: Bind -> LintM ()
lintBind (NonRec bndr rhs) = lintSingleBind bndr rhs
lintBind (Rec bs)          = mapM_ (uncurry lintSingleBind) bs

--------------------------------------------------------------------------------

lintExpr :: Expr -> LintM Type

lintExpr (Var var)
  = do var' <- lookupIdInScope var
       return (idType var')

lintExpr (Lit lit)
  = return (literalType lit)

lintExpr (MultiVal es)
  = mkTupleTy Unboxed <$> mapM lintExpr es

lintExpr (Lam (ValBndrs as) body)
  = addLoc (BodyOfLetRec as) $ -- FIXME: LambdaBodyOf wants an Id so can't use it here
    lintBinders as $ \as' -> do
      body_ty <- lintExpr body
      return (FunTy (mkMultiValTy (map idType as')) body_ty)

lintExpr (Lam (TyBndr ty_var) body)
  = addLoc (LambdaBodyOf ty_var) $
    lintBinder ty_var $ \ty_var' -> do
      body_ty <- lintExpr body
      return (mkLamType ty_var' body_ty)

lintExpr (App fn args)
  = do fun_ty <- lintExpr fn
       lintApp fun_ty args

lintExpr (Eval bndrs rhs body)
  = do rhs_ty <- lintExpr rhs
       lintAndScopeIds bndrs $ \bndrs' -> do
         let bndr_tys = mkMultiValTy (map idType bndrs')
         ensureEqTys bndr_tys rhs_ty (mkEvalBndrsMsg bndr_tys rhs_ty bndrs rhs)
         lintExpr body

lintExpr (Let (NonRec bndr rhs) body)
  = do lintSingleBind bndr rhs
       lintAndScopeId bndr $ \_ -> lintExpr body

lintExpr (Let (Rec binds) body)
  = lintAndScopeIds (map fst binds) $ \_ -> do
      mapM_ (uncurry lintSingleBind) binds
      lintExpr body

lintExpr (Case scrt alt_ty alts)
  = do scrt_ty      <- lintAtom scrt
       (alt_ty', _) <- lintInTy alt_ty

       -- TODO: Run the tests if alts is empty.

       -- Check the alternatives
       mapM_ (lintAlt scrt_ty alt_ty') alts
       return alt_ty'

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

lintSingleBind :: Id -> Expr -> LintM ()
lintSingleBind bndr val
  = do ty <- lintValue val
       lintIdBndr bndr (\_ -> return ()) -- Check match to RHS type
       binder_ty <- applySubstTy (idType bndr)
       ensureEqTys binder_ty ty (mkRhsMsg bndr (text "RHS") ty)

lintValue :: Expr -> LintM Type
lintValue = lintExpr -- TODO: check if expr is really a value

mkEvalBndrsMsg :: Type -> Type -> [Id] -> Expr -> MsgDoc
mkEvalBndrsMsg bndrs_ty expr_ty bndrs expr
  = vcat [ text "Eval LHS and RHS types don't match",
           text "LHS type:" <+> ppr bndrs_ty,
           text "RHS type:" <+> ppr expr_ty,
           text "Binders:" <+> ppr bndrs,
           text "RHS:" <+> ppr expr ]

--------------------------------------------------------------------------------

lintAlt :: Type -> Type -> Alt -> LintM ()

lintAlt _ alt_ty (CoreSyn.DEFAULT, args, rhs)
  = addLoc (RhsOf (head args)) $ do
      lintL (null args) (mkDefaultArgsMsg args)
      lintAltRhs alt_ty rhs

lintAlt scrt_ty alt_ty (CoreSyn.LitAlt lit, args, rhs)
  = addLoc (BodyOfLetRec args) $ do
      lintL (null args) (mkDefaultArgsMsg args)
      let lit_ty = literalType lit
      ensureEqTys lit_ty scrt_ty (mkBadPatMsg lit_ty scrt_ty)
      lintAltRhs alt_ty rhs

lintAlt scrt_ty alt_ty alt@(CoreSyn.DataAlt con, args, rhs)
  | isNewTyCon (dataConTyCon con)
  = addErrL (mkNewTyDataConAltMsg scrt_ty alt)
  | Just (tycon, tycon_arg_tys) <- splitTyConApp_maybe scrt_ty
  = addLoc (BodyOfLetRec args) $ do
      -- First instantiate the universally quantified
      -- type variables of the data constructor we've already check
      lintL (tycon == dataConTyCon con) (mkBadConMsg tycon con)
      let con_payload_ty = piResultTys (dataConRepType con) tycon_arg_tys

      -- And now bring the new binders into scope
      lintBinders args $ \ args' -> do
        -- FIXME: This line won't work, we need to translate DataCons to update
        -- argument types.
        -- lintAltBinders scrt_ty con_payload_ty args'
        lintAltRhs alt_ty rhs

  | otherwise   -- Scrut-ty is wrong shape
  = addErrL (mkBadAltMsg scrt_ty alt)

lintAltRhs :: Type -> Expr -> LintM ()
lintAltRhs ann_ty expr
  = do actual_ty <- lintExpr expr
       ensureEqTys actual_ty ann_ty (mkCaseAltMsg expr actual_ty ann_ty)

mkNewTyDataConAltMsg :: Type -> Alt -> MsgDoc
mkNewTyDataConAltMsg scrt_ty alt
  = vcat [ text "Data alternative for newtype datacon",
           text "Scrutinee type:" <+> ppr scrt_ty,
           text "Alternative:" <+> pprAlt alt ]

mkBadAltMsg :: Type -> Alt -> MsgDoc
mkBadAltMsg scrt_ty alt
  = vcat [ text "Data alternative when scrutinee is not a tycon application",
           text "Scrutinee type:" <+> ppr scrt_ty,
           text "Alternative:" <+> pprAlt alt ]

mkCaseAltMsg :: Expr -> Type -> Type -> MsgDoc
mkCaseAltMsg e ty1 ty2
  = hang (text "Type of case alternatives not the same as the annotation on case:")
         4 (vcat [ text "Actual type:" <+> ppr ty1,
                   text "Annotation on case:" <+> ppr ty2,
                   text "Alt Rhs:" <+> ppr e ])

--------------------------------------------------------------------------------

lintApp :: Type -> [Expr] -> LintM Type

lintApp fun_ty [Type ty]
  = lintCoreArg fun_ty (CoreSyn.Type ty)

lintApp fun_ty [arg]
  = do arg_ty <- lintExpr arg
       lintValApp arg fun_ty arg_ty

lintApp fun_ty args
  = do -- TODO: Make sure `args` doesn't have Type
       arg_tys <- mapM lintExpr args
       lintValApp args fun_ty (mkTupleTy Unboxed arg_tys)

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

mkMultiValTy :: [Type] -> Type
mkMultiValTy [ty] = ty
mkMultiValTy tys  = mkTupleTy Unboxed tys -- empty list OK
