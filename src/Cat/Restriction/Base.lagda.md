<!--
```agda
open import Cat.Prelude
import Cat.Reasoning
```
-->

```agda
module Cat.Restriction.Base where
```


# Restriction Categories

Much of computer science involves the study of partial functions.
Unfortunately, partial functions are somewhat tedious to work with, as
we constantly find ourselves incurring proof obligations, which
immediately grinds any formalization effort to a halt. Furthermore,
we are often interested in *computable* partial functions; this means that
we can not identify partial functions $A \to B$ with total functions
$A \to \rm{Maybe}(B)$. **Restriction categories** aim to ease this burden
by providing an algebraic account of categories of partial maps, which
lets us transform massive termination obligations into slightly less
annoying algebraic manipulations.

We begin our path to generalization by studying the category of sets
and partial functions. The key insight is that every partial function
$f : A \rightharpoonup B$ is defined on some domain $X \subseteq A$;
this yields a partial function $f \downarrow : A \rightharpoonup A$
that maps $x$ to itself if $f(x)$ is defined, and diverges otherwise.

<!-- [TODO: Reed M, 01/08/2023] Add link to partial maps -->

We can generalize this insight to an arbitrary category $\cC$ by equipping
the it with an operation $(-)\downarrow : \cC(x,y) \to \cC(x,x)$.


```agda
record Restriction-category
  {o ℓ} (C : Precategory o ℓ)
  : Type (o ⊔ ℓ) where
  no-eta-equality
  open Cat.Reasoning C
  field
    _↓ : ∀ {x y} → Hom x y → Hom x x

  infix 50 _↓
```

We require that $(-)\downarrow$ satisfies 4 axioms:
- $f \circ f \downarrow = f$
- $f \downarrow \circ g \downarrow = g \downarrow \circ f \downarrow$
- $(g \circ f \downarrow$) \downarrow = g \downarrow \circ f \downarrow$
- $f \downarrow$ \circ g = g \circ (f \circ g) \downarrow$

```agda
  field
    ↓-dom : ∀ {x y} → (f : Hom x y) → f ∘ (f ↓) ≡ f
    ↓-comm : ∀ {x y z} → (f : Hom x z) (g : Hom x y) → f ↓ ∘ g ↓ ≡ g ↓ ∘ f ↓
    ↓-smashr : ∀ {x y z} → (f : Hom x z) (g : Hom x y) → (g ∘ f ↓) ↓ ≡ g ↓ ∘ f ↓
    ↓-swap : ∀ {x y z} → (f : Hom y z) (g : Hom x y) → f ↓ ∘ g ≡ g ∘ (f ∘ g) ↓
```

In order, these correspond to the following facts about the category
of sets and partial maps:
- If $f(x)$ terminates, then $f\downarrow(x)$ does nothing, so
  $f (f\downarrow(x)) = f(x)$. If $f(x)$ diverges, then $f\downarrow(x)$
  also diverges, so $f (f\downarrow(x)) = f(x)$ again!
- It doesn't matter what order we compose restriction maps, as they
  don't modify their arguments; it doesn't matter which order they
  diverge in!
- If we precompose $g$ with a domain map $f \downarrow : A \to A$ and then
  takes its domain of definition, we get to ignore the action of
  $g$, and focus only on its termination.
- If we postcompose $g$ with a domain map $f \downarrow$, then
  we still need to take into account the action of $g$; furthermore, its
  domain of definition needs to be restricted to image of $g$.

