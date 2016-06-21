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

## Choices

* Do not use ANF.  Small reason: reduce clutter of extra lets.  Main reason:
  RULES. ToDo: elaborate this reasoning

* Do not disinguish values (v) from expressions (e), as is done in the paper.
  We could require that values are always bound with a ValRec, but it's clear
  that much is gained.

* Use unboxed-tuple-type for <>; do Unarise to eliminate user-supplied unboxed
  tuples when creating Strict Core.  After all, unboxed tuples ARE multi-values,
  so it'd be very odd to have an IL that had both unboxed tuples and
  multi-values.


NB: Core's `case` is expressed in Strict Core as `let` (to do evaluation) and a
`case` (to do multi-way branch).

NB: Transformation rules: eval-of-case, eval-of-eval

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
type CoreBndr = Id

data Expr
  = MultiVal [Expr]
      -- Return multiple values.
      -- (should singleton or empty lists be OK?)

  | Lit Literal

  | Var Id

  | Eval  [CoreBndr] Expr Expr
      -- Evaluation; non-recursive.
      -- Note that we have a list of binders here, for multi-value returns.

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

Alternative

```haskell
data Expr = ...

  | Eval  [CoreBndr] Expr Expr
    -- Always non-recursive!  Performs evaluation

  | Let Bind Expr

  | Case Atom  [Alt]

  | Value Value

data Bind = NonRec CoreBndr Value
          | Rec [(CoreBndr, Value)]

data Value = Lam [CoreBndr] Expr
           | Con DataCon [Atom]
           | Lit Literal
           -- It's always work-safe to duplicate a value;
           -- you might duplicate code but never work
           -- ToDo: what about big lambdas only

data Atom = AVar Id | ALit Literal | AApp Atom Type | AType Type | ACast Atom Coercion
```

Questions:
* Perhaps make `type Atom` = `Expr`, but a Lint-checked invariant of
  exprIsTrivial?

We use Core's `Type` and `Coercion` data types. Multi-value returns and
multi-arity functions are expressed using unboxed tuples. Thunks are expressed
as functions that take nullary unboxed tuple as argument. Unlifted types are
currently forbidden. (unboxed tuples are not used in user programs, we use it
internally)

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

## How to run

We use Core's linter, but GHC doesn't export its linter API. So you need to
clone my fork of GHC, switch to `strict-core` branch, and install it. Then
install this library, and compile programs:

```
$ ghc Test.hs -fplugin=StrictCore.Plugin
```

It should work like stock GHC, except it should also print StrictCore program.

## Logs

**20/6/2016:** Value syntax needs to change. Here's the current `Value` syntax:

```haskell
-- | It's always work-safe to duplicate a value; you might duplicate code but
-- never work.  Moreover a Value is always a head-normal form; seq'ing it is a
-- no-op.
data Value
  = Lam LamBndr Expr
      -- ^ Lambda takes multiple arguments now.
  | Con DataCon [Atom]
      -- ^ _Saturated_ constructor application.
  | Lit Literal

data LamBndr
  = TyBndr CoreBndr
  | ValBndrs [CoreBndr]
```

Suppose we have:

```
Λa . reverse ([] @ a)
```

Is this a value or not? It certainly isn't a value, but in our syntax it's
considered a value even though our invariants about values don't hold for this
term (it's not work-safe to duplicate this value, it's not in HNF).

Alternatives we considered so far:

(1): Make Λ not erased, instead pass a state token -- a zero-width argument (like RealWorld).

Problem: We lose sharing in some cases. E.g.

```
let f = Λa . reverse ([] @ a) in (f @ Int) ++ (f @ Int)
```

(suppose CSE can't happen) we lose sharing because `f @ Int` becomes a real
function application now.

(2): Add a new invariant: A value `Lam` with only type binders has a value inside.

This makes our example above not a value. So we'd have to thunk it explicitly.
This preserves the sharing.

Problem: What if we had

```
let f = λx . Λa . reverse ([] @ a)
```

The type lambda is not a value anymore as our invariant doesn't hold.

(3): Collapse `Expr` and `Value`, have an invariant that RHS of let bindings are
now values, for this definition of "value":

- A term lambda is a value.
- A type lambda is a value is its body is a value.
- DataCon applications are values. (remember that DataCon applications are
  always saturated)
- Literals are values.

20/6/2016: `LamBndr` type is not going to work. There's no way to express
`f3` in section 3.1:

```
f3 :: <a::*, _::Int, _::a> -> <a, Int>
```

Actually, currently we can't type check this as Core's type system is not
expressive enough for this type. Currently we translate this to an unboxed tuple
which is obviously not going to work as it'd have binders in it.

Simon thinks it may be possible to add one more `Type` constructor to GHC's
`Type`:

```
  | MultiFun [TyBinder] [Type]
```

This leads to questions like, should we remove `FunTy` ? Would `FunTy ty1 ty2`
be equal (as in `eqType`) to `MultiFun [ty1] [ty2]`? In the places where we
pattern match on `Type` we'd have to consider both cases as equal...



Here's another idea that doesn't require any changes in GHC.

When translating from Core to StrictCore, we never have types like these because
Core's unboxed tuples can't have type binders in them. So when when translating
to StrictCore we're never going to have such types.

When generating StrictCore terms, we do this transformation:

- Types:

  ```
  <_ :: Int, a :: *, x :: a>
  ```

  becomes

  ```
  a :: * -> <_ :: Int, x :: a>
  ```

- Terms. We need to consider lambdas and multi-values.

  Lambdas:

  ```
  (\<i x a> -> ...) :: <_ :: Int, a :: *, x :: a>
  ```

  becomes

  ```
  (\x . \<i a> -> ...) :: (a :: *) -> <_ :: Int, x :: a>
  ```

  Multi-values: This is a bit tricky.

  ```
  <1 :: Int, Int :: *, 2 :: Int>
  ```

  In an application position we know that the lambda expects two arguments, so
  we apply two terms: `@Int` and `<1 :: Int, 2 :: Int>`.

  But in a return position things get tricky. Hmm... So maybe this arity
  changing transformation is not going to work either. This is annoying.

  I think CoreLint just rejects when Types appear in non-argument position. So
  maybe we should do the same thing here.

**21/6/2016:** Indeed, we don't expect to see types in multi-value expressions
so we'll go with that solution. Also, I'm merging values and expressions. I'll
implement a lint check that makes sure let only binds to values.

Post-meeting questions:

- Do we need a DataCon application syntax? I think we don't, as at this level
  there's really no difference between a function application and DataCon
  application. In STG it's different because DataCon applications need to be
  saturated, but here we just use multi-arity functions as DataCon workers, and
  wrap them with lambdas in for currying.

- Is there a difference between

  ```
  <Int> -> Int
  ```

  and

  ```
  Int -> Int
  ```

  Similarly in terms:

  ```
  \<x> -> x
  ```

  and

  ```
  \x -> x
  ```

  Operationally there's no difference, and I don't see why would there be any
  difference in the syntax. So I think it makes sense to consider them the same.

  However, it'd be convenient to have a canonical representation. So I'm
  assuming we'll never generate and see a singleton multi-value.

  Remember that nullary multi-values are special -- they're used for forcing
  (when applied) and thunking (when using as argument binder).
