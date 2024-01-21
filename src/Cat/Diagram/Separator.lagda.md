---
description: |
  We define separating objects, and prove some basic properties.
---

<!--
```agda
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Diagram.Coproduct.Copower
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Properties
open import Cat.Instances.Lift
open import Cat.Functor.Dense
open import Cat.Functor.Hom
open import Cat.Prelude


import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Separator {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
open Cat.Reasoning C
```
-->

# Separating objects

One of key property of $\Sets$ is that we can demonstrate the equality of
2 functions $f, g : A \to B$ by proving that they are equal pointwise.
Categorically, this is equivalent to saying that we can determine the
equality of 2 morphisms $A \to B$ in $\Sets$ solely by looking at
global elements $\top \to A$. This is not the case for general categories
equipped with a terminal object: the [[category of groups]] has a terminal
object (the [[zero group]]), yet maps out of the zero group are
unique^[In other words, the zero group is a [[zero object]].]! In light of
this, we can generalize the role that $\top$ plays in $\Sets$ to obtain
the a notion of separating object:

:::{.definition #separating-object alias="separator"}
A **separating object** or **separator** is an object $S : \cC$ that lets
us determine equality of morphisms $f, g : \cC(A,B)$ solely by looking at
the $S$-generalized elements of $A$. Expliclity, $S$ is a separator if:
- For every $f, g : \cC(A, B)$, if $f \circ e = g \circ e$ for every
  $e : \cC(S,A)$, then $f = g$.

In analogy to global elements, we will call morphisms $\cC(S,X)$ out of a
separator $S$ **$S$-global elements**.
:::

```agda
is-separator : Ob → Type _
is-separator s =
  ∀ {x y} {f g : Hom x y}
  → (∀ (e : Hom s x) → f ∘ e ≡ g ∘ e)
  → f ≡ g

record Separator : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    sep      : Ob
    separate : is-separator sep
```

Equivalently, an object $S$ is a separator if the hom functor $\cC(S,-)$
is [[faithful]]. A good way to view this condition is that it is requiring
the $S$-global elements functor to be somewhat well-behaved.

```agda
is-separator→hom-faithful : ∀ {s} → is-separator s → is-faithful (Hom-from C s)
is-separator→hom-faithful sep p = sep (happly p)

hom-faithful→is-separator : ∀ {s} → is-faithful (Hom-from C s) → is-separator s
hom-faithful→is-separator faithful p = faithful (ext p)
```

Intuitively, a separator $S$ gives us an internal version of function
extensionality, with pointwise equality replaced by $S$-wise equality.

## Separators and copowers

Recall that if $\cC$ is [[copowered]], then we can construct an
approximation of any object $X : \cC$ by taking the copower $\cC(A,X) \otimes A$
for some $A : \cC$. Intuitively, this approximation works by adding a copy
of $A$ for every generalized element $\cC(A,X)$. In the category of sets,
$\Sets(\top, X) \otimes X$ is the coproduct of $X$-many copies of $\top$,
which is isomorphic to $X$.

Generalizing from $\Sets$, we can attempt to approximate any object
$X$ by taking the copower $\cC(S,X) \otimes X$, where $S$ is a separating
object. While we don't quite get an isomorphism $\cC(S,X) \otimes X \iso X$,
we can show that the universal map $\cC(S,X) \otimes X \to X$ out of the
copower is an epimorphism.

To see this, let $f, g : \cC(X, Y)$ such that
$f \mathrm{match}(\lambda f. f) = f \circ \mathrm{match}(\lambda f. f)$;
$S$ is a separating object, so it suffices to show that $f \circ e = g \circ e$
for every generalized element $e : \cC(S, X)$. However, $e = \mathrm{match}(\lambda f. f) \circ \iota_e$,
which immediately gives us $f \circ e = g \circ e$ by our hypothesis.

```agda
module _
  (S : Separator)
  (copowers : (I : Set ℓ) → has-coproducts-indexed-by C ∣ I ∣)
  where
  open Separator S
  module copowers (I : Set ℓ) (x : Ob) = Indexed-coproduct (copowers I λ _ → x)

  separator-covers : ∀ x → is-epic (copowers.match (el! (Hom sep x)) sep λ f → f)
  separator-covers x f g p = separate λ e →
    f ∘ e                       ≡⟨ pushr (sym commute) ⟩
    (f ∘ (match λ f → f)) ∘ ι e ≡⟨ p ⟩∘⟨refl ⟩
    (g ∘ (match λ f → f)) ∘ ι e ≡⟨ pullr commute ⟩
    g ∘ e                       ∎
    where open copowers (el! (Hom sep x)) sep
```

## Dense separators

::: {.definition #dense-separator}
A **dense separator** is an object $S : \cC$ such that the functor
$\cC(S,-)$ is [[fully faithful]].
:::

```agda
is-dense-separator : Ob → Type _
is-dense-separator s = is-fully-faithful (Hom-from C s)
```

In other words: morphisms of $\cC$ are given by *functions* between
$S$-global elements.

If $S$ is a dense separator, then it is also a separating object. The
proof of this is rather slick: suppose that $\forall (e : \cC(S,X),\ f \circ e = g \circ e)$
To show $f = g$, it suffices to show that $f \circ - = g \circ -$, as
functions $\cC(S,X) \to \cC(S,Y)$. We can then apply function extensionality,
which gets us a $S$-global element $e : \cC(S,X)$, and our hypothesis handles
the rest!

```agda
dense-separate : ∀ {s} → is-dense-separator s → is-separator s
dense-separate {s} dense p =
  Equiv.injective (_ , dense) $ funext λ e → p e
```


# Separating Families

```agda
is-separating-family : ∀ {ℓi} {I : Type ℓi} → (I → Ob) → Type _ 
is-separating-family s =
  ∀ {x y} {f g : Hom x y}
  → (∀ {i} (eᵢ : Hom (s i) x) → f ∘ eᵢ ≡ g ∘ eᵢ)
  → f ≡ g
```
