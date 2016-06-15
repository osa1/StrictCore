module StrictCore.Syntax where

--------------------------------------------------------------------------------

-- Explicitly import CoreSyn stuff as we re-define some of the stuff defined
import           CoreSyn        (AltCon, AltCon (..), CoreBind, CoreBndr,
                                 CoreExpr)
import qualified CoreSyn
import qualified CoreUtils

import           BasicTypes
import           Coercion       (coercionKind, coercionType)
import           DataCon
import           Id
import           Literal
import           Outputable     hiding (panic)
import           Pair           (pSnd)
import           TyCon
import           TyCoRep
import           Type
import           TysWiredIn
import           VarEnv

import           Data.Bifunctor (first, second)
import           Data.List      (mapAccumL)
import           Data.Maybe     (fromMaybe, isJust)

import           Prelude        hiding (id)

--------------------------------------------------------------------------------
-- * Terms

-- | Non-ANF terms.
data Expr
  = MultiVal [Expr]
      -- ^ Return multiple values. (singleton list is OK)

  | Value Value

  | Var Id

  | Eval Bndrs Expr Expr
      -- ^ Evaluation.

  | Let Bind Expr
      -- ^ Allocation.

  | Case Atom [Alt]
      -- ^ Case doesn't do evaluation anymore, so we have `Atom` as scrutinee.
      -- TODO: Do we need a binder here to bind the scrutinee?

  | App Expr [Expr]
      -- ^ Application.

  | Type Type

  | Cast Expr Coercion

  | Coercion Coercion
      -- TODO: Is this needed?

data Bind
  = NonRec CoreBndr Value
  | Rec [(CoreBndr, Value)]

-- | It's always work-safe to duplicate a value; you might duplicate code but
-- never work.
data Value
  = Lam [CoreBndr] Expr
      -- ^ Lambda takes multiple arguments now.
  | Con DataCon [Atom]
  | Lit Literal

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

-- This just makes function arguments thunks.
translateType :: Type -> Type

translateType ty
  | Just (arg_ty, ret_ty) <- splitFunTy_maybe ty
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

translateTerm :: SCVars -> CoreExpr -> Expr

translateTerm env (CoreSyn.Var v)
  | isDataConWorkId v
  = -- FIXME: We need to replace these with new functions... (section 4.3)
    Var v

{-
  | otherwise
  = forceTerm (Var (fromMaybe err (lookupVarEnv env v)))
  where
    err = panic "translateTerm" (text "Can't find var in env:" <+> ppr v $$ ppr env)
-}

  | Just v' <- lookupVarEnv env v
  = forceTerm (Var v')

  -- FIXME: For libraries...
  | otherwise
  = Var v

translateTerm _ (CoreSyn.Lit l)
  = Value (Lit l)

translateTerm env (CoreSyn.App e1 e2)
  | CoreSyn.isTypeArg e2
  = App (translateTerm env e1) [ translateTerm env e2 ]
  | otherwise
  = App (translateTerm env e1) [ mkThunk (translateTerm env e2) ]

translateTerm env (CoreSyn.Lam arg body)
  = Value (Lam [arg'] (translateTerm env' body))
  where
    arg' = translateBndr arg
    env' = extendVarEnv env arg arg'

translateTerm env (CoreSyn.Let bind e)
  = Let bind' (translateTerm env' e)
  where
    (env', bind') = translateBind env bind

translateTerm env (CoreSyn.Case scrt scrt_bndr _scrt_ty alts)
  = -- case doesn't evaluate anymore, so we first evaluate the scrutinee and
    -- bind it to its new binder.
    let
      scrt_bndr' = translateBndr scrt_bndr
      env'       = extendVarEnv env scrt_bndr scrt_bndr'
      scrt'      = translateTerm env scrt -- using original env
    in
      Eval [scrt_bndr'] scrt' $
        Case (AVar scrt_bndr') (translateAlts env' alts)

translateTerm env (CoreSyn.Cast e co)
  = Cast (translateTerm env e) co

translateTerm _ CoreSyn.Tick{}
  = panic "translateTerm" (text "Tick is not supported")
      -- I don't want to think about this right now ...

translateTerm _ (CoreSyn.Type ty)
  = Type ty

translateTerm _ (CoreSyn.Coercion co)
  = Coercion co

translateBind :: SCVars -> CoreBind -> (SCVars, Bind)

translateBind env (CoreSyn.NonRec b rhs)
  = ( extendVarEnv env b b'
    , NonRec b' (Lam [] (translateTerm env rhs)) )
  where
    b' = translateBndr b

translateBind env (CoreSyn.Rec bs)
  = ( env', Rec bs'' )
  where
    bs'  = map (first translateBndr) bs
    env' = extendVarEnvList env (zipWith (,) (map fst bs) (map fst bs'))
    bs'' = map (second (Lam [] . translateTerm env')) bs'

translateAlts :: SCVars -> [CoreSyn.CoreAlt] -> [Alt]
translateAlts env alts = map (translateAlt env) alts

translateAlt :: SCVars -> CoreSyn.CoreAlt -> Alt
translateAlt env (lhs, bndrs, rhs)
  = (lhs, bndrs', translateTerm env' rhs)
  where
    bndrs' = map translateBndr bndrs
    env'   = extendVarEnvList env (zip bndrs bndrs')

--------------------------------------------------------------------------------

translateBndr :: Id -> Id
translateBndr id = id `setIdType` mkThunkType (translateType (idType id))

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
mkThunk = Value . Lam []

-- | Multi-arity is just unboxed tuple in the original Core. Note that unboxed
-- tuples are the only unlifted types we allow for now.
mkMultiArityType :: [Type] -> Type
mkMultiArityType = mkTupleTy Unboxed

-- | Generate term that forces a given thunk. Forcing means just applying the
-- function. (remember that thunks are just nullary lambdas)
forceTerm :: Expr -> Expr
forceTerm e
  = -- assert "forceTerm" (text "Term is not a thunk:" <+> ppr e) (isThunkType (exprType e)) $
    App e []

--------------------------------------------------------------------------------
-- * Type checking StrictCore

exprType :: Expr -> Type
-- Multi-values are expressed as unboxed tuples in the original Core type system
exprType (MultiVal es)
  = mkTupleTy Unboxed (map exprType es)

exprType (Value val)
  = valType val

exprType (Var v)
  = idType v

exprType (Eval _ _ _)
  = undefined

valType :: Value -> Type

valType (Lam [] e) -- thunk
  = mkFunTy (mkTupleTy Unboxed []) (exprType e)

valType (Lam bndrs e)
  = foldr (\bndr ty -> mkFunTy (idType bndr) ty) (exprType e) bndrs

valType (Con _ _)
  = undefined

valType (Lit lit)
  = CoreUtils.exprType (CoreSyn.Lit lit)

{-
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
-}

--------------------------------------------------------------------------------
-- * Printing StrictCore

instance Outputable Expr where
  ppr = pprExpr noParens

instance Outputable Bind where
  ppr = pprBind

noParens :: SDoc -> SDoc
noParens d = d

pprExpr :: (SDoc -> SDoc) -> Expr -> SDoc

pprExpr _ (MultiVal es)
  = angleBrackets (sep (map (pprExpr parens) es))

pprExpr add_par (Value val)
  = pprVal add_par val

pprExpr _ (Var v)
  = ppr v

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

pprExpr _ (App e []) -- thunk evaluation
  = char '~' <> pprExpr parens e
      -- there isn't any syntactic sugar for this in the paper,
      -- so making up one.

pprExpr add_par (App f as)
  = add_par $ hang (pprExpr parens f) 2 (sep (map pprArg as))

pprExpr add_par (Case scrt alts)
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

pprVal :: (SDoc -> SDoc) -> Value -> SDoc

pprVal _ (Lam [] e) -- thunk
  = braces (pprExpr noParens e)

pprVal add_par (Lam as e)
  = add_par $
    hang (text "\\" <+> sep (map ppr as) <+> arrow) 2 (pprExpr noParens e)

pprVal add_par (Con con as)
  = add_par $
    sep (ppr con : map (pprAtomArg parens) as)

pprVal add_par (Lit lit)
  = pprLiteral add_par lit

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

pprBinding :: Bndr -> Value -> SDoc
pprBinding bndr val
  = pprBndr LetBind bndr $$ hang (ppr bndr <+> equals) 2 (pprVal noParens val)

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
