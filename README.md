# An Agda proof of confluence using HOAS
 
This a proof-of-concept development to demonstrate how we can reason about
higher-order abstract syntax (HOAS) in Agda using features that are already
present in the language: the _flat modality_ `♭` and _custom rewrite rules_.

- `Lambda.agda` defines the syntax of the λ-calculus in Agda using a series of
  postulates.

- `Par.agda` defines parallel reduction of terms, and proves that it satisfies
  the diamond property.

- `Flat.agda` defines a data type for simplifying the manipulation of the `♭`
  modality in Agda.
  
## What is HOAS?

_Higher-order abstract syntax_ is the idea of representing variable binding
using functions.  For instance, consider the syntax of the λ-calculus, defined
as a BNF grammar:

```
t := x | t₁ t₂ | λ x. t
```

In Haskell, this might be implemented as follows, using a traditional encoding
where variables are represented with strings:

```
data Term = Var String
          | App Term Term
          | Abs String Term

-- The term "λ x. x x"
id :: Term
id = Abs "x" (App (Var "x") (Var "x"))
```

By contrast, here is a HOAS encoding of the same grammar:

```
data Term = App Term Term
          | Abs (Term -> Term)
          
id :: Term
id = Abs (\x -> App x x)
```

Unlike the more traditional encoding, the HOAS definition does not include a
separate constructor for variables.  It instead uses Haskell variables to
represent variables in the λ-calculus.  A term with a bound variable is
represented using a function of type `Term -> Term`.  The main advantage of this
technique is that we do not need to implement a substitution operator for terms:
we can just use function application.

For example, here is how we can implement an evaluator for the λ-calculus.

```
beta :: Term -> Term -> Term
beta (Abs f) t2 = eval (f t2)
beta t1 t2 = App t1 t2

eval :: Term -> Term
eval (App t1 t2) = beta (eval t1) (eval t2)
eval t = t
```

For comparison, here is an implementation based on the first encoding.  To
define `beta`, we need to implement substitution ourselves.

```
subst :: String -> Term -> Term
subst x (Var y) t
  | x == y = t
  | otherwise = Var y
subst x (App t1 t2) t = App (subst x t1 t) (subst x t2 t)
subst x (Abs y t1) t
  | x == y = Abs y t1
  | otherwise = Abs y (subst x t1 t)

beta :: Term -> Term -> Term
beta (Abs x t1) t2 = eval (subst x t1 t2)
beta t1 t2 = App t1 t2

eval :: Term -> Term
eval (App t1 t2) = beta (eval t1) (eval t2)
eval t = t
```

## Difficulties with HOAS

Despite its obvious appeal, working with HOAS can present a few obstacles.
First, there are some HOAS terms that do not correspond to any λ-term.  For
example:

```
isApp :: Term -> Bool
isApp (App _ _) = True
isApp _ = False

exotic :: Term
exotic = Abs (\x -> if isApp x then x else App x x)
```

Since the syntax of terms does not have `if` expressions, it cannot represent
`exotic`.

The second issue is that it can be tricky to reason about HOAS terms in a type
theory.  Consider the following function, which flips the top-level constructor
of a term.

```
flip :: Term -> Term
flip t
  | isApp t = Abs (\_ -> t)
  | otherwise = App t t
```

Intuitively, `isApp (flip t)` should be equal to `not (isApp t)`, implying that
that `flip t` and `t` cannot be equal.  However, consider the following term:

```
f :: Term -> Term -> Term
f (App t1 t2) = \_ -> App t1 t2
f (Abs g)     = g

t :: Term
t = Abs (\x -> flip (f x x))

paradox :: Term
paradox = f t t
```

What should `paradox` be?  If we unfold `f` and `t`, we find that `paradox` is
equal to `flip paradox`, since

```
paradox
  = f t t
  = (\x -> flip (f x x)) t
  = flip (f t t)
  = flip paradox,
```

which contradicts our intuition above.

## A solution: modal type theory

The two pathological examples above had something in common: both relied on the
ability to do case analysis on terms.  We could rule out these pathological
examples by forbidding case analysis on terms, but this would be too
restrictive.  Fortunately, there is a better way out.  As explained by Martin
Hofmann in his paper "[Semantical analysis of higher-order abstract syntax][1]",
we can still perform case analysis on terms that _do not depend on free
variables_.  We would still be able to write the `isApp`, `flip` and `f`
functions above.  However, it wouldn't be possible to use such functions inside
of `Abs`, like we did when defining `t` or `exotic` above -- intuitively,
because it would require performing case analysis on a term variable introduced
by the argument of `Abs`.  We can make this idea precise by working in a type
theory extended with a modality `♭`.  Intuitively, `♭ T` describes values of
type `T` that do not have free variables of type `Term`. Agda features a
modality that behaves just like we need, so we can soundly postulate the
existence of a type of HOAS terms.  This type comes with a case-analysis
principle that allows us to write functions on HOAS terms and reason about them
by structural induction.  Thanks to Agda's custom rewrite rules, we can describe
the computational behavior of case analysis, thus allowing these functions to
compute inside Agda.


  [1]: https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.122.6636&rep=rep1&type=pdf
