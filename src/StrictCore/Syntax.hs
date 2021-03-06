{-# LANGUAGE TupleSections #-}

module StrictCore.Syntax where

--------------------------------------------------------------------------------

-- Explicitly import CoreSyn stuff as we re-define some of the stuff defined
import CoreSyn (AltCon, AltCon (..), CoreBind, CoreBndr, CoreExpr)
import qualified CoreSyn
import CoreUtils ()

import BasicTypes
import Coercion (coercionType)
import DataCon
import FastString
import Id
import Literal
import Outputable hiding (panic)
import TyCon
import TyCoRep
import Type
import TysWiredIn
import UniqSupply
import VarEnv

import Data.Bifunctor (first)
import Data.Maybe (isJust)

import Prelude hiding (id)

--------------------------------------------------------------------------------
-- * Terms

-- | Non-ANF terms.
data Expr
  = Var Id

  | Lit Literal

  | MultiVal [Expr]
      -- ^ Return multiple values. INVARIANT: Not a singleton list.
      -- Empty list is OK: Forces a thunk.

  | Lam LamBndr Expr
      -- ^ There's no difference between curried and uncurried type arguments,
      -- so we have a special type `LamBndr` that forces us to uncurry type
      -- arguments.

  | App Expr [Expr]
      -- ^ Application.

  | Eval Bndrs Expr Expr
      -- ^ Evaluation.  ToDo: comments!

  | Let Bind Expr
      -- ^ Allocation.

  | Case Atom Type [Alt]
      -- ^ Case doesn't do evaluation anymore, so we have `Atom` as scrutinee.
      -- TODO: Do we need a binder here to bind the scrutinee?

  | Type Type

  | Cast Expr Coercion

  | Coercion Coercion
      -- TODO: Is this needed?

-- | INVARIANT: RHSs are all values. See `isValue`.
data Bind
  = NonRec CoreBndr Expr
  | Rec [(CoreBndr, Expr)]

bindersOf :: Bind -> [CoreBndr]
bindersOf (NonRec b _) = [b]
bindersOf (Rec bs)     = map fst bs

bindersOfBinds :: [Bind] -> [CoreBndr]
bindersOfBinds = concatMap bindersOf

--------------------------------------------------------------------------------

-- | It's always work-safe to duplicate a value; you might duplicate code but
-- never work. Moreover a value is always a head-normal form; seq'ing it is a
-- no-op. Let expressions bind things to values.
--
-- Very conservative, syntactic check.
isValue :: Expr -> Bool
isValue (Lit _) = True

isValue (Lam (TyBndr _) e)   = isValue e
isValue (Lam (ValBndrs _) _) = True

-- saturated constructor applications are values when arguments are values
isValue (App (Var id) args)
  | Just dc <- isDataConWorkId_maybe id
  , all isValue args
  , dataConRepArity dc == length args
  = True

isValue _ = False

--------------------------------------------------------------------------------

-- | Lambda binders. Type binders need to be curried.
data LamBndr
  = TyBndr CoreBndr
  | ValBndrs [CoreBndr]

-- | Atoms are not allocated, and also work-safe.
data Atom
  = AVar Id

  | ALit Literal

  | AApp Atom Type
      -- ^ This appears in e.g. f (g @ Int)
      --                          ^^^^^^^^^

  | ACast Atom Coercion
      -- ^ Similar to the `AApp` case: f (g |> co)
      --                                 ^^^^^^^^^

  | AType Type

type Bndr  = CoreBndr
type Bndrs = [CoreBndr]

-- NOTE: We use GHC's AltCon but we need to translate DataCons of DataAlt!
-- (translate field types so that they become thunks -- except the
-- bang-patterned ones)
type Alt = (AltCon, Bndrs, Expr)

--------------------------------------------------------------------------------
-- * Translating Core types
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
--
-- TODO: We should allow unlifted types, but treat unboxed tuples specially.
-- We should do "unarise" pass here and generate multi-value returns and
-- multi-arity lambdas in places where unboxed tuples are used.

-- This just makes function arguments thunks. Figure 9 in the paper.
translateType :: Type -> Type

translateType (FunTy arg_ty ret_ty)
  = mkFunTy (mkThunkType (translateType arg_ty)) (translateType ret_ty)

-- rest is just traversal

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
-- * Translating Core terms

-- | Mapping from original binders to binders with updated types. We could just
-- update every identifier's type manually, but we'd lose sharing. (does not
-- effect correctness, but may make things less efficient)
type SCVars = VarEnv Var

initSCVars :: SCVars
initSCVars = emptyVarEnv

translateTerm :: SCVars -> CoreExpr -> UniqSM Expr

translateTerm env (CoreSyn.Var v)
  | isTyVar v
  = return (Var v)

  | Just v' <- lookupVarEnv env v
  = return (forceTerm (Var v'))

  | isDataConWorkId v
    -- DataCons are not thunked
  , let v' = v `setIdType` translateType (idType v)
  = return (Var v')

  | otherwise
  = -- FIXME: For libraries...
    return (forceTerm (Var (translateBndr v)))

translateTerm _ (CoreSyn.Lit l)
  = return (Lit l)

translateTerm env (CoreSyn.App e1 e2)
  | CoreSyn.isTypeArg e2
  = do e1' <- translateTerm env e1
       e2' <- translateTerm env e2
       return (App e1' [ e2' ])

  | otherwise
  = do e1' <- translateTerm env e1
       e2' <- translateTerm env e2
       return (App e1' [ mkThunk e2' ])

translateTerm env (CoreSyn.Lam arg body)
  | isTyVar arg
  = do body' <- translateTerm env body
       return (Lam (TyBndr arg) body')

  | otherwise
  = do let arg' = translateBndr arg
           env' = extendVarEnv env arg arg'
       body' <- translateTerm env' body
       return (Lam (ValBndrs [ arg' ]) body')

translateTerm env (CoreSyn.Let bind e)
  = do (env', bind') <- translateBind env bind
       e' <- translateTerm env' e
       return (Let bind' e')

translateTerm env (CoreSyn.Case scrt scrt_bndr alt_ty alts)
  = do -- case doesn't evaluate anymore, so we first evaluate the scrutinee and
       -- bind it to its new binder.
       let
         scrt_bndr' = translateBndr scrt_bndr
         env'       = extendVarEnv env scrt_bndr scrt_bndr'
         alt_ty'    = translateType alt_ty

       scrt' <- translateTerm env scrt -- using original env
       evald_scrt_bndr <- mkSysLocalOrCoVarM (fsLit "scrt") (translateType (idType scrt_bndr))
       alts' <- translateAlts env' alts

       return $
         Let (NonRec scrt_bndr' (mkThunk scrt')) $
           Eval [evald_scrt_bndr] (forceTerm (Var scrt_bndr')) $
             Case (AVar evald_scrt_bndr) alt_ty' alts'

translateTerm env (CoreSyn.Cast e co)
  = do e' <- translateTerm env e
       return (Cast e' co)

translateTerm _ CoreSyn.Tick{}
  = panic "translateTerm" (text "Tick is not supported")
      -- I don't want to think about this right now ...

translateTerm _ (CoreSyn.Type ty)
  = return (Type ty)

translateTerm _ (CoreSyn.Coercion co)
  = return (Coercion co)

translateBind :: SCVars -> CoreBind -> UniqSM (SCVars, Bind)

translateBind env (CoreSyn.NonRec b rhs)
  = do rhs' <- translateTerm env rhs
       let b' = translateBndr b
       return ( extendVarEnv env b b', NonRec b' (Lam (ValBndrs []) rhs') )

translateBind env (CoreSyn.Rec bs)
  = do let
         bs'  = map (first translateBndr) bs
         env' = extendVarEnvList env (zipWith (,) (map fst bs) (map fst bs'))

         translateRhs (bndr, rhs) = (bndr,) . mkThunk <$> translateTerm env' rhs

       bs'' <- mapM translateRhs bs'
       return (env', Rec bs'')

translateAlts :: SCVars -> [CoreSyn.CoreAlt] -> UniqSM [Alt]
translateAlts env alts = mapM (translateAlt env) alts

translateAlt :: SCVars -> CoreSyn.CoreAlt -> UniqSM Alt
translateAlt env (lhs, bndrs, rhs)
  = (lhs, bndrs',) <$> translateTerm env' rhs
  where
    bndrs' = map translateBndr bndrs
    env'   = extendVarEnvList env (zip bndrs bndrs')

--------------------------------------------------------------------------------

translateBndr :: Id -> Id
translateBndr id
  = id `setIdType` mkThunkType (translateType (idType id))
  -- = let
  --     (tyvars, ty) = splitForAllTyVarBndrs (idType id)
  --   in
  --     id `setIdType` mkForAllTys tyvars (mkThunkType ty)

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
mkThunk :: Expr -> Expr
mkThunk (App e []) = e
mkThunk e = Lam (ValBndrs []) e

-- | Multi-arity is just unboxed tuple in the original Core. Note that unboxed
-- tuples are the only unlifted types we allow for now.
mkMultiArityType :: [Type] -> Type
mkMultiArityType = mkTupleTy Unboxed

-- | Generate term that forces a given thunk. Forcing means just applying the
-- function. (remember that thunks are just nullary lambdas)
forceTerm :: Expr -> Expr
forceTerm e@(Var v)
  | isThunkType (idType v) = App e []
  | otherwise = pprPanic "forceTerm" (text "Id isn't a thunk:" <+> ppr v <+> ppr (idType v))
forceTerm e = App e []

--------------------------------------------------------------------------------
-- * Printing StrictCore

instance Outputable Expr where
  ppr = pprExpr noParens

instance Outputable Bind where
  ppr = pprBind

instance Outputable Atom where
  ppr = pprAtom noParens

instance Outputable LamBndr where
  ppr = pprLamBndr

noParens :: SDoc -> SDoc
noParens d = d

pprExpr :: (SDoc -> SDoc) -> Expr -> SDoc

pprExpr _ (Var v)
  = ppr v

pprExpr add_par (Lit lit)
  = pprLiteral add_par lit

pprExpr _ (MultiVal es)
  = angleBrackets (sep (map (pprExpr parens) es))

pprExpr _ (Lam (ValBndrs []) e) -- thunk
  = braces (pprExpr noParens e)

pprExpr add_par (Lam as e)
  = add_par $
    hang (text "\\" <+> ppr as <+> arrow) 2 (pprExpr noParens e)

pprExpr _ (App e []) -- thunk evaluation
  = char '~' <> pprExpr parens e
      -- there isn't any syntactic sugar for this in the paper,
      -- so making up one.

pprExpr add_par (App f as)
  = add_par $ hang (pprExpr parens f) 2 (sep (map pprArg as))

pprExpr add_par (Eval bndrs rhs e)
  = add_par $
    sep [ sep [ hang (text "eval" <+> sep (map ppr bndrs)) 2 (char '=' <+> ppr rhs), text "in" ]
        , pprExpr noParens e ]

pprExpr add_par (Let bind body)
  = add_par $
    sep [ hang kw 2 (pprBind bind <+> text "} in")
        , pprExpr noParens body
        ]
  where
    kw = case bind of
           NonRec _ _ -> text "let {"
           Rec _      -> text "letrec {"

pprExpr add_par (Case scrt _ alts)
  = add_par $
    sep [ sep [ hang (text "case") 2 (pprAtom noParens scrt)
              , text "of" <+> char '{'
              ]
        , nest 2 (vcat (punctuate semi (map pprAlt alts)))
        , char '}'
        ]

pprExpr add_par (Type ty)
  = add_par (text "TYPE:" <+> ppr ty)

pprExpr add_par (Coercion co)
  = add_par (text "CO:" <+> ppr co)

pprExpr add_par (Cast e co)
  = add_par (sep [pprExpr parens e, text "`cast`" <+> pprCo co])

pprAtom :: (SDoc -> SDoc) -> Atom -> SDoc

pprAtom _ (AVar v)
  = ppr v

pprAtom add_par (ALit lit)
  = pprLiteral add_par lit

pprAtom add_par (AApp a ty)
  = add_par $ pprAtom noParens a <+> char '@' <+> ppr ty

pprAtom add_par (ACast a co)
  = add_par $ pprAtom noParens a <+> text "|>" <+> ppr co

pprAtom _ (AType ty)
  = ppr ty

pprAtomArg :: (SDoc -> SDoc) -> Atom -> SDoc

pprAtomArg _ (AType ty)
  = char '@' <+> ppr ty

pprAtomArg add_par a
  = pprAtom add_par a

pprBinds :: [Bind] -> SDoc
pprBinds bs
  = vcat (map pprBind bs)

pprBind :: Bind -> SDoc

pprBind (NonRec bndr val)
  = pprBinding bndr val

pprBind (Rec bs)
  = vcat (map (\(bndr, val) -> pprBinding bndr val <> semi) bs)

pprBinding :: Bndr -> Expr -> SDoc
pprBinding bndr val
  = pprBndr LetBind bndr $$ hang (ppr bndr <+> equals) 2 (pprExpr noParens val)

pprAlt :: Alt -> SDoc
pprAlt (con, args, rhs)
  = hang (ppr con <+> fsep (map ppr args) <+> arrow) 2 (pprExpr noParens rhs)

pprCo :: Coercion -> SDoc
pprCo co = parens (sep [ppr co, dcolon <+> ppr (coercionType co)])

pprArg :: Expr -> SDoc
pprArg (Type ty)
  = char '@' <+> pprParendType ty
pprArg (Coercion co)
  = text "@~" <+> pprCo co
pprArg e
  = pprExpr parens e

pprLamBndr :: LamBndr -> SDoc
pprLamBndr (TyBndr v)    = ppr v
pprLamBndr (ValBndrs vs) = sep (map ppr vs)

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
