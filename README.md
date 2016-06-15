# StrictCore

StrictCore aims to improve GHC's Core language by having:

1. Thunk vs. value distinction at the type level.
2. Multi-arity functions and multiple value returns.

These make some program transformations/ optimizations possible:

- Worker/wrapper transformation becomes type-driven

- Specializing higher-order functions based on functional argument's strictness
  becomes possible

- Bang patterns actually reduce evaluations

- Being able to express multi-arity functions makes optimizations like
  arity-raising possible.

- ...

- Better support for strict programs is a good thing ...

- A shared intermediate language for functional languages?
  (Idris, ML family, dynamically typed ones?)

## Syntax

We have an non-ANF syntax to be able to support rewrite rules and make
beta-reduction possible without inlining. However, we will probably need an ANF
syntax at some point...

(Maybe we can even replace STG. As far as I can see, STG is useful because (1)
having an ANF syntax helps the code generation (2) Unarisation pass is easier to
implement in an language that's not type checked. (1) can be done without moving
to a new language (indeed, CorePrep is transforming Core programs to ANF core
programs without moving to another language entirely) (2) can be done in Core
already, without any changes ...)

Current abstract syntax:

```haskell
data Expr
  = MultiVal [Expr]
      -- Return multiple values.
      -- (should singleton or empty lists be OK?)

  | Lit Literal

  | Var Id

  | Let [CoreBndr] Expr Expr
      -- Evaluation. Note that we have a list of binders here, for multi-value
      -- returns.

  | ValRec [([CoreBndr], Expr)] Expr
      -- Allocation. We don't have a NonRec/Rec distinction in this language.
      -- (because I never understood why we need that)

  | App Expr [Expr]
      -- Application. Empty argument list = thunk evaluation. (specially
      -- handled in the code generator). Question: Can we remove Coercion from
      -- the term syntax because we have explicit thunks?

  | Lam [CoreBndr] Expr
      -- ^ Lambda takes multiple arguments now. Empty argument list = thunk.

  | Case Expr [Alt]
      -- Pattern matching. Does not force the scrutinee. (as can also be seen
      -- from the typing rules)
      -- (so operationally, we can just assume the pointer is tagged)
      -- TODO: Do we need a binder here to bind the scrutinee?

  | Type Type
      -- Same as in Core -- for type checking purposes.

  | Cast Expr Coercion
      -- For type checking purposes.

  | Coercion Coercion
      -- TODO: Is this needed?
```

We use Core's `Type` and `Coercion` data types. Multi-value returns and multi-arity functions are
expressed using unboxed tuples. Thunks are expressed as functions that take
nullary unboxed tuple as argument. Unlifted types are currently forbidden.
(unboxed tuples are not used in user programs, we use it internally)

Current concrete syntax (used by the pretty-printer).  ToDo: write down the syntax.

```
<a, b, ...>         -- multi-value

\<a, b> -> ...      -- multi-arity function

{a, b, ...}         -- thunk, syntactic sugar for \<> -> <a, b, ...>
```

Type syntax:

```
<t1, t2, ...>       -- multi-value.
                    -- (# t1, t2, ... #) in Core syntax

<t1, t2, ...> -> t3 -- multi-arity function.
                    -- (# t1, t2, ... #) -> t3 in Core syntax

{t1, t2, ...}       -- thunk, sugar for <> -> <t1, t2, ...>.
                    -- (# #) -> (# t1, t2, ... #) in Core syntax
```

## Translation from Core to StrictCore

We follow Figures 9 and 10 of the paper.
