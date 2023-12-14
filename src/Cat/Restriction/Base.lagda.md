<!--
```agda
open import Cat.Prelude
```
-->

```agda
module Cat.Restriction.Base where
```

# Restriction categories

Much of computer science involves the study of partial functions.
Unfortunately, partial functions are somewhat tedious to work with,
as they aren't really functions; they're relations! Furthermore,
we are often interested in *computable* partial functions; this means that
we can not identify partial functions $A \rightharpoonup B$ with total functions
$A \to \rm{Maybe}(B)$[^1]. This leaves us with a few possible approaches.
The most first approach that may come to mind is to encode partial functions
$A \rightharpoonup B$ as total functions from a subobject $X \mono A$.
Alternatively, we could find some construction that classifies
partial maps; this is what the naive `Maybe` approach attempted to do.
We could also just work with functional relations directly, though this
is ill-advised.

<!--[TODO: Reed M, 05/08/2023] Link to approaches once formalized -->

[^1]: We can easily determine if functions into `Maybe` "diverge"
by checking if they return `nothing`. If we identify partial functions
with total functions into `Maybe`, we can decide if a partial function
terminates, which is extremely uncomputable!

Each of these approaches has its own benefits and drawbacks, which
makes choosing one difficult. **Restriction categories** offer an
alternative, algebraic approach to the problem, allowing us to neatly
sidestep any questions about encodings.

Our prototypical restriction category will be $\Par$, the category of
sets and partial functions. The key insight is that every partial function
$f : A \rightharpoonup B$ is defined on some domain $X \subseteq A$;
this yields a partial function $f \downarrow : A \rightharpoonup A$
that maps $x$ to itself iff $f(x)$ is defined. We can generalize this
insight to an arbitrary category $\cC$ by equipping $\cC$ with an operation
$\restrict{(-)} : \cC(x,y) \to \cC(x,x)$.

-- <!-- [TODO: Reed M, 01/08/2023] Add link to partial maps -->


```agda
record Restriction-category
  {o ℓ} (C : Precategory o ℓ)
  : Type (o ⊔ ℓ) where
  no-eta-equality
  open Precategory C
  field
    _↓ : ∀ {x y} → Hom x y → Hom x x

  infix 50 _↓
```

We require that $\restrict{(-)}$ satisfies 4 axioms:
- $f\restrict{f} = f$. In $\Par$, this corresponds to the fact that
$\restrict{f}(x)$ is defined to be $x$ iff $f$ is defined, so
precomposing with it does nothing.

```agda
  field
    ↓-dom : ∀ {x y} → (f : Hom x y) → f ∘ (f ↓) ≡ f
```

- $\restrict{f}\restrict{g} = \restrict{g}\restrict{f}$. In $\Par$,
this falls out of the fact that restriction maps do not modify their
arguments, and it doesn't matter if $f$ diverges first or $g$ does;
all that matters is that it diverges!

```agda
  field
    ↓-comm : ∀ {x y z} → (f : Hom x z) (g : Hom x y) → f ↓ ∘ g ↓ ≡ g ↓ ∘ f ↓
```

- $\restrict{(g\restrict{f})} = \restrict{g}\restrict{f}$. This axiom
holds in the $\Par$, as $\restrict{(g\restrict{f})}(x)$ ignores the
action of $g$ on $x$, and focuses only on its termination.

```agda
  field
    ↓-smashr : ∀ {x y z} → (f : Hom x z) (g : Hom x y) → (g ∘ f ↓) ↓ ≡ g ↓ ∘ f ↓
```

- $\restrict{f} g = g  \restrict{(f g)}$. This is the trickiest of the
bunch to understand in $\Par$. Note that if we postcompose $g$ with a
domain map $\restrict{f}$, then we still need to take into account the
action of $g$; furthermore, its domain of definition needs to be
restricted to image of $g$.

```agda
  field
    ↓-swap : ∀ {x y z} → (f : Hom y z) (g : Hom x y) → f ↓ ∘ g ≡ g ∘ (f ∘ g) ↓
```
