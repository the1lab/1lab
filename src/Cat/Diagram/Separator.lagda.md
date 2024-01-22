---
description: |
  We define separating objects, and prove some basic properties.
---

<!--
```agda
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Functor.FullSubcategory
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Properties
open import Cat.Instances.Comma
open import Cat.Functor.Joint
open import Cat.Functor.Base
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
open _=>_
```
-->

<!--
  [TODO: Reed M, 21/01/2024] Write the page on concrete categories; link separators
  to representing objects for the faithful functors.
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
```

Equivalently, an object $S$ is a separator if the hom functor $\cC(S,-)$
is [[faithful]]. A good way to view this condition is that it is requiring
the $S$-global elements functor to be somewhat well-behaved.

```agda
separator→faithful : ∀ {s} → is-separator s → is-faithful (Hom-from C s)
separator→faithful sep p = sep (happly p)

faithful→separator : ∀ {s} → is-faithful (Hom-from C s) → is-separator s
faithful→separator faithful p = faithful (ext p)
```

Intuitively, a separator $S$ gives us an internal version of function
extensionality, with pointwise equality replaced by $S$-wise equality.
We can make this formal by showing that a separator $S$ gives us an
[[identity system]] for morphisms in $\cC$.

```agda
separator-identity-system
  : ∀ {s x y}
  → is-separator s
  → is-identity-system {A = Hom x y}
      (λ f g → ∀ (e : Hom s x) → f ∘ e ≡ g ∘ e)
      (λ f e → refl)
separator-identity-system separate = set-identity-system hlevel! separate
```

## Separators and copowers

Recall that if $\cC$ is [[copowered]], then we can construct an
approximation of any object $X : \cC$ by taking the copower $\cC(A,X) \otimes A$
for some $A : \cC$. Intuitively, this approximation works by adding a copy
of $A$ for every generalized element $\cC(A,X)$. In the category of sets,
$\Sets(\top, X) \otimes X$ is the coproduct of $X$-many copies of $\top$,
which is isomorphic to $X$.

Generalizing from $\Sets$, we can attempt to approximate any object
$X$ by taking the copower $\cC(S,X) \otimes S$, where $S$ is a separating
object. While we don't quite get an isomorphism $\cC(S,X) \otimes S \iso X$,
we can show that the universal map $\cC(S,X) \otimes X \to X$ out of the
copower is an epimorphism.

To see this, let $f, g : \cC(X, Y)$ such that
$f \mathrm{match}(\lambda f. f) = f \circ \mathrm{match}(\lambda f. f)$;
$S$ is a separating object, so it suffices to show that $f \circ e = g \circ e$
for every generalized element $e : \cC(S, X)$. However, $e = \mathrm{match}(\lambda f. f) \circ \iota_e$,
which immediately gives us $f \circ e = g \circ e$ by our hypothesis.

```agda
module _
  {sep : Ob}
  (separate : is-separator sep)
  (copowers : (I : Set ℓ) → has-coproducts-indexed-by C ∣ I ∣)
  where
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

If $S$ is a dense separator, then it is also a separating object.
This follows by some abstract nonsense ($\cC(S,-)$ is fully faithful, and $S$
is a separator if $\cC(S,-)$ is faithful), but we provide an elementary proof for the
sake of intution. Suppose that $\forall (e : \cC(S,X),\ f \circ e = g \circ e)$
To show $f = g$, it suffices to show that $f \circ - = g \circ -$, as
functions $\cC(S,X) \to \cC(S,Y)$. We can then apply function extensionality,
which gets us a $S$-global element $e : \cC(S,X)$, and our hypothesis handles
the rest!

```agda
dense-separate : ∀ {s} → is-dense-separator s → is-separator s
dense-separate {s} dense p = Equiv.injective (_ , dense) $ funext λ e → p e
```

Furthermore, if $S$ is a dense separator, then every object $X$ is a copower
$\cC(S,X) \otimes S$. This can be seen as providing a particularly strong form
of the [[coyoneda lemma]] for $\cC$, as every object can be expressed as a colimit
of a single object.

```agda
dense-separator→coyoneda
  : ∀ {s}
  → is-dense-separator s
  → ∀ (x : Ob) → is-indexed-coproduct C {Idx = Hom s x} (λ _ → s) (λ f → f)
dense-separator→coyoneda dense x .is-indexed-coproduct.match fs =
  equiv→inverse dense fs
dense-separator→coyoneda dense x .is-indexed-coproduct.commute {e} {_} {fs} =
  equiv→counit dense fs $ₚ e
dense-separator→coyoneda dense x .is-indexed-coproduct.unique {h = h} fs p =
  Equiv.adjunctl (_ , dense) $ funext p
```

The converse is also true: if every object $X$ is a copower $\cC(S,X) \otimes S$,
then $S$ is a dense separator. Explicltly, we must construct an inverse to
$\cC(S,-) : \cC(X,Y) \to (\cC(S, X) \to \cC(S, Y))$. Recall $X$ is a copower
of $\cC(S,X) \otimes S$: the universal property of $\cC(S,X) \otimes S$ is *exactly*
a function $(\cC(S, X) \to \cC(S, Y)) \to \cC(X,Y)$. Furthermore, the $\beta$ and $\eta$
rules for copowers ensure that we actually obtain an inverse to $\cC(S,-)$.

```agda
coyoneda→dense-separator
  : ∀ {s}
  → (∀ (x : Ob) → is-indexed-coproduct C {Idx = Hom s x} (λ _ → s) (λ f → f))
  → is-dense-separator s
coyoneda→dense-separator {s} coyo {x} {y} =
  is-iso→is-equiv $ iso (coyo.match x)
    (λ fs → funext λ e → coyo.commute x)
    (λ f → sym $ coyo.unique _ _ λ _ → refl)
  where module coyo (x : Ob) = is-indexed-coproduct (coyo x)
```

# Separating Families

Many categories lack a single separating object $S : \cC$, but do have a *family* of
separating objects $S_i : I \to \cC$. The canonical is the category of presheaves:
we cannot determine equality of natural transformations $\alpha, \beta : P \to Q$
by looking at all maps $S \to P$ single $S$, but we *can* if we look at all
maps $\yo(A) \to P$! This leads us to the following notion:

:::{.definition #separating-object alias="separator"}
A **separating family or **separator** is a family of objects $S : I \to \cC$ such that:
- For every $f, g : \cC(A, B)$, if $f \circ e_i = g \circ e_i$ for every
  $i : I$ and every $e_i : \cC(S_i,A)$, then $f = g$.
:::

```agda
is-separating-family : ∀ {ℓi} {Idx : Type ℓi} → (Idx → Ob) → Type _ 
is-separating-family s =
  ∀ {x y} {f g : Hom x y}
  → (∀ {i} (eᵢ : Hom (s i) x) → f ∘ eᵢ ≡ g ∘ eᵢ)
  → f ≡ g
```

Equivalently, an family $S_i : \cC$ of objects form a separating family if the hom
functors $C(S_i, -)$ are [[jointly faithful]].

```agda
separating-family→jointly-faithful
  : ∀ {ℓi} {Idx : Type ℓi} {sᵢ : Idx → Ob}
  → is-separating-family sᵢ
  → is-jointly-faithful (λ i → Hom-from C (sᵢ i ))
separating-family→jointly-faithful separates p = separates λ eᵢ → p _ $ₚ eᵢ

jointly-faithful→separating-family
  : ∀ {ℓi} {Idx : Type ℓi} {sᵢ : Idx → Ob}
  → is-jointly-faithful (λ i → Hom-from C (sᵢ i ))
  → is-separating-family sᵢ
jointly-faithful→separating-family faithful p = faithful λ i → funext p
```

Most of the theory of separating object generalizes directly to separating families.
For instance, separating families also induce an identity system on morphisms.

```agda
separating-family-identity-system
  : ∀ {ℓi} {Idx : Type ℓi} {sᵢ : Idx → Ob} {x y}
  → is-separating-family sᵢ
  → is-identity-system {A = Hom x y}
      (λ f g → ∀ {i} (eᵢ : Hom (sᵢ i) x) → f ∘ eᵢ ≡ g ∘ eᵢ)
      (λ f e → refl)
separating-family-identity-system separate = set-identity-system hlevel! separate
```

## Separating families and indexed coproducts

Recall that if $\cC$ is $\kappa$ locally-small and admits $\kappa$-small
[[indexed coproducts]], then we can form an approximation of any object $X$
via a family of objects $S_i : I \to \cC$  by forming the indexed coproduct
$\coprod_{i : I, e_i : \cC(S_i, X)} S_i$. This approximation comes equipped
with a canonical map $u : \coprod_{i : I, e_i : \cC(S_i, X)} S_i \to X$
defined via the universal property of indexed coproducts. If $S_i$ is
a separating family, then this map is an epi.

```agda
module _
  {Idx : Type ℓ}
  {sᵢ : Idx → Ob}
  (Idx-set : is-set Idx)
  (separate : is-separating-family sᵢ)
  (coprods : (I : Set ℓ) → has-coproducts-indexed-by C ∣ I ∣)
  where
  module coprods (I : Set ℓ) (xᵢ : ∣ I ∣ → Ob) = Indexed-coproduct (coprods I xᵢ)

  private
    sᵢ-elts : Ob → Set ℓ
    sᵢ-elts x .∣_∣ =  Σ[ i ∈ Idx ] Hom (sᵢ i) x
    sᵢ-elts x .is-tr = Σ-is-hlevel 2 Idx-set (λ _ → hlevel!)

  separating-family-covers
    : ∀ x → is-epic (coprods.match (sᵢ-elts x) (sᵢ ⊙ fst) snd)
  separating-family-covers x f g p = separate λ {i} eᵢ →
    f ∘ eᵢ                       ≡⟨ pushr (sym commute) ⟩
    (f ∘ match snd) ∘ ι (i , eᵢ) ≡⟨ p ⟩∘⟨refl ⟩
    (g ∘ match snd) ∘ ι (i , eᵢ) ≡⟨ pullr commute ⟩
    g ∘ eᵢ                       ∎
    where open coprods (sᵢ-elts x) (sᵢ ⊙ fst)
```

## Dense separating families

::: {.definition #dense-separating-family}
A **dense separating family** is an family $S_i : I \to \cC$ such that the
functors $\cC(S_i,-)$ are [[jointly fully faithful]].
:::

Unfortunately, we need to jump through some hoops to construct the appropriate
functor from the full subcategory generated by $S_i$ into $[\cC, \Sets]$

```agda
is-dense-separating-family : ∀ {Idx : Type ℓ} → (Idx → Ob) → Type _
is-dense-separating-family sᵢ =
  is-jointly-fully-faithful (よcov C F∘ Functor.op (Forget-family {C = C} sᵢ))
```

```agda
module _
  {Idx : Type ℓ}
  {sᵢ : Idx → Ob}
  (dense : is-dense-separating-family sᵢ)
  where
  private
    module dense {x} {y} = Equiv (_ , dense {x} {y})
    open ↓Obj using (map)
    open ↓Hom using (sq)

  Approx : ∀ x → Functor (Forget-family {C = C} sᵢ ↘ x) C
  Approx x = Forget-family sᵢ F∘ Dom _ _

  dense-separating-family→coyoneda
    : ∀ (x : Ob)
    → is-colimit (Approx x) x _
  dense-separating-family→coyoneda x = to-is-colimit colim where
    open make-is-colimit

    colim : make-is-colimit (Approx x) x
    colim .ψ x = x .map
    colim .commutes f = f .sq ∙ idl _
    colim .universal eps p = dense.from λ where
      .η i f → eps (↓obj f)
      .is-natural i j f → ext λ g → sym (p (↓hom (sym (idl _))))
    colim .factors eps p = {!!}
    colim .unique = {!!}
```
