-- This is where we experiment with program transformation ideas.

module StrictCore.Simplify
  ( simplifyPgm
  , initSimplEnv
  ) where

--------------------------------------------------------------------------------

import Coercion
import Id
import Outputable
import Type hiding (substTy)
import VarEnv

import StrictCore.Syntax

import Data.Bifunctor (second)

import Prelude hiding (id)

--------------------------------------------------------------------------------

data SimplEnv = SimplEnv
  { seTvSubst   :: TyVarEnv Type
  , seCvSubst   :: CoVarEnv Coercion
  , seExprSubst :: IdEnv Expr
  , seAtomSubst :: IdEnv Atom
  , seInScope   :: InScopeSet
  }

initSimplEnv :: SimplEnv
initSimplEnv
  = SimplEnv { seTvSubst   = emptyVarEnv
             , seCvSubst   = emptyVarEnv
             , seExprSubst = emptyVarEnv
             , seAtomSubst = emptyVarEnv
             , seInScope   = emptyInScopeSet
             }

--------------------------------------------------------------------------------

simplifyPgm :: SimplEnv -> [Bind] -> [Bind]
simplifyPgm env0 bind0 = map simplifyBind bind0

simplifyBind :: Bind -> Bind
simplifyBind (NonRec bndr val)
  = NonRec bndr (simplifyVal val)
simplifyBind (Rec bndrs)
  = Rec (map (second simplifyVal) bndrs)

simplifyVal :: Value -> Value
simplifyVal (Lam args body)
  = Lam args (simplifyExpr body)
simplifyVal (Con con as)
  = Con con (map simplifyAtom as)
simplifyVal val@(Lit _)
  = val

simplifyAtom :: Atom -> Atom
simplifyAtom a = a -- not sure what to do here

simplifyExpr :: Expr -> Expr

simplifyExpr (MultiVal es)
  = MultiVal (map simplifyExpr es)

simplifyExpr (Value val)
  = case simplifyVal val of
      Lam (ValBndrs []) (App thunk []) ->
        -- pprTrace "simplifyExpr" (text "removing a thunk")
        thunk

      val' ->
        Value val'

simplifyExpr (Var id)
  = Var id

simplifyExpr (Eval bndrs rhs body)
  = Eval bndrs (simplifyExpr rhs) (simplifyExpr body)

simplifyExpr (Let bind body)
  = Let (simplifyBind bind) (simplifyExpr body)

simplifyExpr (Case scrt alt_ty alts)
  = Case (simplifyAtom scrt) alt_ty (simplifyAlts alts)

simplifyExpr (App fun args)
  = case ( simplifyExpr fun, map simplifyExpr args ) of
      ( Value (Lam (ValBndrs []) body), [] ) ->
        -- pprTrace "simplifyExpr" (text "forcing a thunk") $
        body -- force the thunk

      ( Value (Lam (TyBndr tyv) body), [Type ty_arg] ) ->
        simplifyExpr (substTy tyv ty_arg body)

      ( Value (Lam (ValBndrs bndrs) body), args' ) ->
        assert "simplifyExpr" (text "Lambda arity is different than arguments applied." $$
                               ppr bndrs $$ ppr args') (length bndrs == length args') $

        let
          asgns        = zip bndrs args'
          val_args     = [ (val_bndr, val) | (val_bndr, Value val) <- asgns ]
          non_val_args = filter (not . isValueExpr . snd) asgns
        in
          mkNonRecLets non_val_args $
            substVals val_args body

      ( fun', args' ) ->
        App fun' args'

simplifyExpr (Type ty)
  = Type ty

simplifyExpr (Cast expr co)
  = Cast (simplifyExpr expr) co

simplifyExpr (Coercion co)
  = Coercion co

simplifyAlts :: [Alt] -> [Alt]
simplifyAlts = map simplifyAlt

simplifyAlt :: Alt -> Alt
simplifyAlt (lhs, bndrs, rhs) = (lhs, bndrs, simplifyExpr rhs)

--------------------------------------------------------------------------------

substTy :: Id -> Type -> Expr -> Expr
substTy tyvar ty expr = undefined

mkNonRecLets :: [(Bndr, Expr)] -> Expr -> Expr
mkNonRecLets = undefined

substVals :: [(Bndr, Value)] -> Expr -> Expr
substVals = undefined
