# An proof of confluence in Agda using HOAS
 
This a proof-of-concept development to demonstrate how we can reason about
higher-order abstract syntax (HOAS) in Agda using the _flat modality_ `♭` and
_custom rewrite rules_.

- `Lambda.agda` defines a HOAS encoding of the λ-calculus in Agda using a series
  of postulates.
  
- `DB.agda` proves that the HOAS encoding is isomorphic to a more conventional
  well-scoped dependently typed encoding using de Bruijn indices.

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
selfApp :: Term
selfApp = Abs "x" (App (Var "x") (Var "x"))
```

By contrast, here is a HOAS encoding of the same grammar:

```
data Term = App Term Term
          | Abs (Term -> Term)
          
selfApp :: Term
selfApp = Abs (\x -> App x x)
```

Unlike the more traditional encoding, the HOAS definition does not include a
separate constructor for variables.  It instead uses Haskell variables to
represent variables in the λ-calculus.  A term with a bound variable is just a
function of type `Term -> Term`.  The main advantage of this technique is that
we do not need to implement a substitution operator for terms: we can just use
function application.

For example, here is how we can implement an evaluator for closed terms in the
λ-calculus.

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

While this definition is not too cumbersome, it does sidestep one of the main
issues with binding: variable capture. The definition of `subst x t1 t2` only
works if the bound variables in `t1` do not appear free in `t2`; otherwise, one
of the free variables of `t2` could enter the scope of a bound variable in `t1`,
which wouldn't make sense.  We can make `subst` work on open terms as well by
modifying the `Abs` case to rename the bound variable `y` if a clash occurs.  By
contrast, the HOAS encoding prevents variable capture automatically, because it
is impossible for a function parameter to alias a free variable that occurs
outside its scope.

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
ability to do case analysis on terms.  This suggests that restricting case
analysis might be a solution for making HOAS well behaved.  One such approach is
implemented in [Twelf][2], a HOAS-based framework for specifying programming
languages and logics.  In Twelf, function terms of type `A -> B` cannot perform
case analysis on their arguments, but it is possible to do so when defining
_relations_, as in logic programming.

Another approach is to integrate HOAS in a more conventional type theory, by
controlling which free variables can appear in a term when performing case
analysis.  As explained by Martin Hofmann in his paper "[Semantical analysis of
higher-order abstract syntax][1]", this can be done by extending type theory
with a modality, an idea realized in [contextual modal type theory][3].  In such
a system, we would still be able to write the `isApp`, `flip` and `f` functions
above.  However, it wouldn't be possible to use such functions inside of `Abs`,
like we did when defining `t` or `exotic` above -- intuitively, because it would
require performing case analysis on a term variable introduced by the argument
of `Abs`.

This development shows how this idea can be implemented in Agda, by leveraging
its `♭` modality.  Intuitively, we can use `♭ T` to describe elements of a type
`T` that do not depend on free variables of the object languages we are modeling
(for instance, the λ-calculus defined above).  With this modality, we can
soundly postulate an eliminator for HOAS types, which allows us to perform case
analysis and reason by structural induction. Thanks to Agda's custom rewrite
rules, we can describe the computational behavior of case analysis, thus
allowing these functions to compute inside Agda.


  [1]: https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.122.6636&rep=rep1&type=pdf
  [2]: http://twelf.org
  [3]: https://www.cs.cmu.edu/~fp/papers/tocl07.pdf
