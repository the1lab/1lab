---
description: |
  We define separating objects, and prove some basic properties.
---

<!--
```agda
open import Cat.Diagram.Coproduct.Copower
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.FullSubcategory
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Limit.Finite
open import Cat.Functor.Conservative
open import Cat.Diagram.Coequaliser
open import Cat.Functor.Properties
open import Cat.Diagram.Equaliser
open import Cat.Functor.Constant
open import Cat.Functor.Compose
open import Cat.Instances.Comma
open import Cat.Instances.Sets
open import Cat.Functor.Joint
open import Cat.Diagram.Zero
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Prelude

open import Data.Dec.Base

import Cat.Morphism.Strong.Epi
import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Separator {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
open Cat.Morphism.Strong.Epi C
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
two functions $f, g : A \to B$ by showing that they are equal pointwise.
Categorically, this is equivalent to saying that we can determine the
equality of two morphisms $A \to B$ in $\Sets$ solely by looking at
global elements $\top \to A$. This is not the case for general categories
equipped with a terminal object: the [[category of groups]] has a terminal
object (the [[zero group]]), yet maps out of the zero group are
unique^[In other words, the zero group is a [[zero object]].]! In light of
this, we can generalize the role that $\top$ plays in $\Sets$ to obtain
the notion of separating object:

:::{.definition #separating-object alias="separator"}
A **separating object** or **separator** is an object $S : \cC$ that lets
us determine equality of morphisms $f, g : \cC(A,B)$ solely by looking at
the $S$-generalized elements of $A$. Explicitly, $S$ is a separator if:
- For every $f, g : \cC(A, B)$, if $f \circ e = g \circ e$ for every
  $e : \cC(S,A)$, then $f = g$.

In analogy to global elements, we will call morphisms $\cC(S,X)$ out of a
separator $S$ **$S$-global elements**.
:::

::: warning
Some authors (notably [@Borceux:vol1]) use the term "generator" to
in place of separator.
:::

```agda
is-separator : Ob → Type _
is-separator s =
  ∀ {x y} {f g : Hom x y}
  → (∀ (e : Hom s x) → f ∘ e ≡ g ∘ e)
  → f ≡ g
```

Equivalently, an object $S$ is a separator if the hom functor $\cC(S,-)$
is [[faithful]]. A good way to view this condition is that it ensures
that the $S$-global elements functor to be somewhat well-behaved.

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
separator-identity-system separate =
  set-identity-system (λ _ _ → hlevel 1) separate
```

# Separating families

Many categories lack a single separating object $S : \cC$, but do have a *family* of
separating objects $S_i : I \to \cC$. The canonical example is the category
of presheaves: we cannot determine equality of natural transformations
$\alpha, \beta : P \to Q$ by looking at all maps $S \to P$ for a single $S$,
but we *can* if we look at all maps $\yo(A) \to P$! This leads us to the
following notion:

:::{.definition #separating-family}
A **separating family** is a family of objects $S : I \to \cC$ such that
for every $f, g : \cC(A, B)$, if $f \circ e_i = g \circ e_i$ for every
$i : I$ and every $e_i : \cC(S_i,A)$, then $f = g$.
:::

```agda
is-separating-family : ∀ {ℓi} {Idx : Type ℓi} → (Idx → Ob) → Type _
is-separating-family s =
  ∀ {x y} {f g : Hom x y}
  → (∀ {i} (eᵢ : Hom (s i) x) → f ∘ eᵢ ≡ g ∘ eᵢ)
  → f ≡ g
```

Equivalently, a family $S_i : \cC$ of objects is a separating family if the hom
functors $C(S_i, -)$ are [[jointly faithful]].

```agda
separating-family→jointly-faithful
  : ∀ {ℓi} {Idx : Type ℓi} {sᵢ : Idx → Ob}
  → is-separating-family sᵢ
  → is-jointly-faithful (λ i → Hom-from C (sᵢ i))
separating-family→jointly-faithful separates p = separates λ eᵢ → p _ $ₚ eᵢ

jointly-faithful→separating-family
  : ∀ {ℓi} {Idx : Type ℓi} {sᵢ : Idx → Ob}
  → is-jointly-faithful (λ i → Hom-from C (sᵢ i))
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
separating-family-identity-system separate =
  set-identity-system (λ _ _ → hlevel 1) separate
```

## Separators and copowers {defines="separators-and-copowers"}

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
$f \circ \mathrm{match}(\lambda e. e) = g \circ \mathrm{match}(\lambda e. e)$;
$S$ is a separating object, so it suffices to show that $f \circ e = g \circ e$
for every generalized element $e : \cC(S, X)$. However, $e = \mathrm{match}(\lambda e. e) \circ \iota_e$,
which immediately gives us $f \circ e = g \circ e$ by our hypothesis.

```agda
module _
  (copowers : (I : Set ℓ) → has-coproducts-indexed-by C ∣ I ∣)
  where
  open Copowers copowers

  separator→epi : ∀ {s x} → is-separator s → is-epic (⊗!.match (Hom s x) s λ f → f)
  separator→epi {s} {x} separate f g p = separate λ e →
    f ∘ e                                     ≡⟨ pushr (sym (⊗!.commute _ _)) ⟩
    (f ∘ (⊗!.match _ _ λ f → f)) ∘ ⊗!.ι _ _ e ≡⟨ p ⟩∘⟨refl ⟩
    (g ∘ (⊗!.match _ _ λ f → f)) ∘ ⊗!.ι _ _ e ≡⟨ pullr (⊗!.commute _ _) ⟩
    g ∘ e                                     ∎
```

Conversely, if the canonical map $\gamma_{X} : \cC(S,X) \otimes S \to X$
is an epimorphism for every $X$, then $S$ is a separator.

Let $f, g : \cC(X, Y)$ such that $f \circ e = g \circ e$ for every
$e : \cC(S, X)$. Note that $f \circ \gamma_{X} \circ \iota = g \circ \gamma_{X} \circ \iota$
by our hypothesis, so $f \circ \gamma_{X} = g \circ \gamma_{X}$. Moreover,
$\gamma_{X}$ is an epi, so $f = g$.

```agda
  epi→separator : ∀ {s} → (∀ {x} → is-epic (⊗!.match (Hom s x) s λ f → f)) → is-separator s
  epi→separator epic {f = f} {g = g} p =
    epic f g $ ⊗!.unique₂ _ _ λ e →
      sym (assoc _ _ _)
      ∙ p _
      ∙ assoc _ _ _
```

A similar result holds for separating families, insofar that a family
$S_i : \cC$ is a separating family if and only if the canonical map
$\coprod_{\Sigma (i : I), \cC(S_i, X)} S_i \to X$ is an epimorphism.

```agda
  separating-family→epi
    : ∀ (Idx : Set ℓ) (sᵢ : ∣ Idx ∣ → Ob)
    → is-separating-family sᵢ
    → ∀ {x} → is-epic (∐!.match (Σ[ i ∈ ∣ Idx ∣ ] Hom (sᵢ i) x) (sᵢ ⊙ fst) snd)

  epi→separating-family
    : ∀ (Idx : Set ℓ)
    → (sᵢ : ∣ Idx ∣ → Ob)
    → (∀ {x} → is-epic (∐!.match (Σ[ i ∈ ∣ Idx ∣ ] Hom (sᵢ i) x) (sᵢ ⊙ fst) snd))
    → is-separating-family sᵢ
```

<details>
<summary>The proof is almost identical to the single-object case, so
we omit the details.
</summary>
```agda
  separating-family→epi Idx sᵢ separate f g p = separate λ {i} eᵢ →
    f ∘ eᵢ                                     ≡⟨ pushr (sym (∐!.commute _ _)) ⟩
    (f ∘ ∐!.match _ _ snd) ∘ ∐!.ι _ _ (i , eᵢ) ≡⟨ p ⟩∘⟨refl ⟩
    (g ∘ ∐!.match _ _ snd) ∘ ∐!.ι _ _ (i , eᵢ) ≡⟨ pullr (∐!.commute _ _) ⟩
    g ∘ eᵢ                                     ∎

  epi→separating-family Idx sᵢ epic {f = f} {g = g} p =
    epic f g $ ∐!.unique₂ _ _ λ (i , eᵢ) →
      sym (assoc _ _ _)
      ∙ p _
      ∙ assoc _ _ _
```
</details>

## Existence of separating families

If $\cC$ has [[equalisers]] and $\cC(S,-)$ is [[conservative]], then
$S$ is a separating family.

```agda
equalisers+conservative→separator
  : ∀ {s}
  → has-equalisers C
  → is-conservative (Hom-from C s)
  → is-separator s
```

Let $f, g : \cC(A,B)$, and suppose that $f \circ e = g \circ e$ for every $\cC(S,A)$.
We can then form the equaliser $(E,e)$ of $f$ and $g$. Note that if $e$
is invertible, then $f = g$, as $f \circ e = g \circ e$ holds by virtue of
$e$ being an equaliser.

```agda
equalisers+conservative→separator equalisers f∘-conservative {f = f} {g = g} p =
  invertible→epic equ-invertible f g Eq.equal
  where
    module Eq = Equaliser (equalisers f g)
```

Moreover, $\cC(S,-)$ is conservative, so it suffices to prove that
precomposition of $e$ with an $S$-generalized element is an equivalence.
This follows immediately from the universal property of equalisers!

```agda
    equ-invertible : is-invertible Eq.equ
    equ-invertible =
      f∘-conservative $
      is-equiv→is-invertible $
      is-iso→is-equiv $ iso
        (λ e → Eq.universal (p e))
        (λ e → Eq.factors)
        (λ h → sym (Eq.unique refl))
```

A similar line of argument lets us generalize this result to separating
families.

```agda
equalisers+jointly-conservative→separating-family
  : ∀ {κ} {Idx : Type κ} {sᵢ : Idx → Ob}
  → has-equalisers C
  → is-jointly-conservative (λ i → Hom-from C (sᵢ i))
  → is-separating-family sᵢ
```

<details>
<summary>The proof is more-or-less the same, so we omit the details.
</summary>
```agda
equalisers+jointly-conservative→separating-family
  equalisers fᵢ∘-conservative {f = f} {g = g} p =
  invertible→epic equ-invertible f g Eq.equal
  where
    module Eq = Equaliser (equalisers f g)

    equ-invertible : is-invertible Eq.equ
    equ-invertible =
      fᵢ∘-conservative λ i →
      is-equiv→is-invertible $
      is-iso→is-equiv $ iso
        (λ eᵢ → Eq.universal (p eᵢ))
        (λ eᵢ → Eq.factors)
        (λ h → sym (Eq.unique refl))
```
</details>


```agda
```

Our next result lets us relate separating objects and separating families.
Clearly, a separating object yields a separating family; when does the
converse hold?

One possible scenario is that there is an object $X : \cC$ such that
every $S_i$ comes equipped with a section/retraction pair
$f_i : S_i \rightleftarrows X : r_i$. To see why, let $g, h : \cC(A, B)$
and suppose that $g \circ e = h \circ e$ for every $e : \cC(X, A)$.
As $S_i$ is a separating family, it suffices to show that $g \circ e_i = h \circ e_i$
for every $i : I$, $e_i : \cC(S_i, A)$.

Next, note that $g \circ e_i = g  \circ e_i \circ r_i \circ f_i$, as
$f_i$ and $r_i$ are a section/retraction pair. Moreover,
$e_i \circ r_i : \cC(X, A)$, so

$$g \circ e_i \circ r_i \circ f_i = h \circ e_i \circ r_i \circ f_i$$

by our hypothesis. Finally, we can use the fact that $f_i$ and $r_i$
are a section/retraction pair to observe that $g \circ e_i = f \circ e_i$,
completing the proof

```agda
retracts+separating-family→separator
  : ∀ {κ} {Idx : Type κ} {sᵢ : Idx → Ob} {x : Ob}
  → is-separating-family sᵢ
  → (fᵢ : ∀ i → Hom (sᵢ i) x)
  → (∀ i → has-retract (fᵢ i))
  → is-separator x
retracts+separating-family→separator separate fᵢ r {f = g} {g = h} p =
  separate λ {i} eᵢ →
    g ∘ eᵢ                         ≡˘⟨ pullr (cancelr (r i .is-retract)) ⟩
    (g ∘ eᵢ ∘ r i .retract) ∘ fᵢ i ≡⟨ ap₂ _∘_ (p (eᵢ ∘ r i .retract)) refl ⟩
    (h ∘ eᵢ ∘ r i .retract) ∘ fᵢ i ≡⟨ pullr (cancelr (r i .is-retract)) ⟩
    h ∘ eᵢ                         ∎
```

We can immediately use this result to note that a separating family
$S_i$ can be turned into a separating object, provided that:

1. The separating family $S_i$ is indexed by a [[discrete]] type.
2. The coproduct of $\coprod_{I} S_i$ exists.
3. $\cC$ has a zero object.


```agda
zero+separating-family→separator
  : ∀ {κ} {Idx : Type κ} {sᵢ : Idx → Ob} {∐s : Ob} {ι : ∀ i → Hom (sᵢ i) ∐s}
  → ⦃ Idx-Discrete : Discrete Idx ⦄
  → Zero C
  → is-separating-family sᵢ
  → is-indexed-coproduct C sᵢ ι
  → is-separator ∐s
```

This follows immediately from the fact that coproduct inclusions have
retracts when hypotheses (1) and (3) hold.

```agda
zero+separating-family→separator {ι = ι} z separates coprod =
  retracts+separating-family→separator separates ι $
  zero→ι-has-retract C coprod z
```

# Dense separators

As noted in the previous sections, separating objects categorify
the idea that the behaviour of functions can be determined by their
action on $S$-generalized elements. However, note that a separating
object only lets us *equate* morphisms; ideally, we would be able to
construct a morphism $\cC(X,Y)$ by giving a function $\cC(S,X) \to \cC(S,Y)$
on $S$-generalized elements as well! This desire leads directly to the
notion of a **dense separating object**.

:::{.definition #dense-separating-object alias="dense-separator"}
An object $S : \cC$ **dense separating object** is a
**dense separating object** or **dense separator** if:

- For all $X, Y : \cC$, a function $\eta : \cC(S,X) \to \cC(S,Y)$ induces
  a morphism $u_{\eta} : \cC(X,Y)$; and
- For every generalized element $e : \cC(S, X)$, $u_{\eta} \circ e = \eta e$; and
- The map $u_{f}$ is universal among all such maps.
:::

```agda
record is-dense-separator (s : Ob) : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    universal
      : ∀ {x y}
      → (eta : Hom s x → Hom s y)
      → Hom x y
    commute
      : ∀ {x y}
      → {eta : Hom s x → Hom s y}
      → {e : Hom s x}
      → universal eta ∘ e ≡ eta e
    unique
      : ∀ {x y}
      → {eta : Hom s x → Hom s y}
      → (h : Hom x y)
      → (∀ (e : Hom s x) → h ∘ e ≡ eta e)
      → h ≡ universal eta
```

As the name suggests, dense separators are separators: this follows
directly from the uniqueness of the universal map.

```agda
  separate
    : ∀ {x y}
    → {f g : Hom x y}
    → (∀ (e : Hom s x) → f ∘ e ≡ g ∘ e)
    → f ≡ g
  separate p = unique _ p ∙ sym (unique _ λ _ → refl)
```

<!--
```agda
module _ where
  open is-dense-separator
```
-->

Equivalently, an object $S$ is a dense separator if the hom functor
$\cC(S,-)$ is [[fully faithful]].

```agda
  dense-separator→ff
    : ∀ {s}
    → is-dense-separator s
    → is-fully-faithful (Hom-from C s)
  dense-separator→ff dense =
    is-iso→is-equiv $ iso
      (dense .universal)
      (λ eta → ext λ e → dense .commute)
      (λ h → sym (dense .unique h (λ _ → refl)))

  ff→dense-separator
    : ∀ {s}
    → is-fully-faithful (Hom-from C s)
    → is-dense-separator s
  ff→dense-separator ff .universal =
    equiv→inverse ff
  ff→dense-separator ff .commute {eta = eta} {e = e} =
    equiv→counit ff eta $ₚ e
  ff→dense-separator ff .unique h p =
    sym (equiv→unit ff h) ∙ ap (equiv→inverse ff) (ext p)
```

Furthermore, if $S$ is a dense separator, then every object $X$ is a copower
$\cC(S,X) \otimes S$. This can be seen as providing a particularly strong form
of the [[coyoneda lemma]] for $\cC$, as every object can be expressed as a colimit
of a single object. Alternatively, this is a categorification of the idea
that every set is a coproduct of copies of the point!

```agda
dense-separator→coyoneda
  : ∀ {s}
  → is-dense-separator s
  → ∀ (x : Ob)
  → is-indexed-coproduct C {Idx = Hom s x} (λ _ → s) (λ f → f)
dense-separator→coyoneda {s = s} dense x = is-copower where
  module dense = is-dense-separator dense
  open is-indexed-coproduct

  is-copower : is-indexed-coproduct C {Idx = Hom s x} (λ _ → s) (λ f → f)
  is-copower .match  = dense.universal
  is-copower .commute = dense.commute
  is-copower .unique h p = dense.unique _ p
```

The converse is also true: if every object $X$ is a copower $\cC(S,X) \otimes S$,
then $S$ is a dense separator.

```agda
coyoneda→dense-separator
  : ∀ {s}
  → (∀ (x : Ob) → is-indexed-coproduct C {Idx = Hom s x} (λ _ → s) (λ f → f))
  → is-dense-separator s
coyoneda→dense-separator {s} coyo = dense where
  module coyo (x : Ob) = is-indexed-coproduct (coyo x)
  open is-dense-separator

  dense : is-dense-separator s
  dense .universal = coyo.match _
  dense .commute = coyo.commute _
  dense .unique h p = coyo.unique _ _ p
```

## Dense separating families

Next, we extend the notion of a dense separator to a family of objects.

::: {.definition #dense-separating-family}
A family of objects $S_i : \cC$ is a **dense separating family** if:

- functions $\eta : (i : I) \to \cC(S_i, X) \to \cC(S_i, y)$ with
  $\eta_i (f \circ g) = \eta_j f \circ g$ induce maps $u_{\eta} : \cC(X,Y)$; and
- For every $e_i : \cC(S_i, X)$, $u_{\eta} \circ e_i = \eta_i e_i$; and
- The map $u_{f}$ is universal among all such maps.
:::

```agda
record is-dense-separating-family
  {Idx : Type ℓ}
  (sᵢ : Idx → Ob)
  : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    universal
      : ∀ {x y}
      → (eta : ∀ i → Hom (sᵢ i) x → Hom (sᵢ i) y)
      → (∀ {i j} (f : Hom (sᵢ j) x) (g : Hom (sᵢ i) (sᵢ j)) → eta i (f ∘ g) ≡ eta j f ∘ g)
      → Hom x y
    commute
      : ∀ {x y}
      → {eta : ∀ i → Hom (sᵢ i) x → Hom (sᵢ i) y}
      → {p : ∀ {i j} (f : Hom (sᵢ j) x) (g : Hom (sᵢ i) (sᵢ j)) → eta i (f ∘ g) ≡ eta j f ∘ g}
      → {i : Idx} {eᵢ : Hom (sᵢ i) x}
      → universal eta p ∘ eᵢ ≡ eta i eᵢ
    unique
      : ∀ {x y}
      → {eta : ∀ i → Hom (sᵢ i) x → Hom (sᵢ i) y}
      → {p : ∀ {i j} (f : Hom (sᵢ j) x) (g : Hom (sᵢ i) (sᵢ j)) → eta i (f ∘ g) ≡ eta j f ∘ g}
      → (h : Hom x y)
      → (∀ (i : Idx) → (eᵢ : Hom (sᵢ i) x) → h ∘ eᵢ ≡ eta i eᵢ)
      → h ≡ universal eta p
```

Like their single-object counterparts, dense separating families are
also separating families; this follows immediately from the uniqueness
of the universal map.

```agda
  separate
    : ∀ {x y}
    → {f g : Hom x y}
    → (∀ (i : Idx) (eᵢ : Hom (sᵢ i) x) → f ∘ eᵢ ≡ g ∘ eᵢ)
    → f ≡ g
  separate p =
    unique {p = λ _ _ → assoc _ _ _} _ p
    ∙ sym (unique _ λ _ _ → refl)
```


<!--
```agda
module _ {Idx} {sᵢ : Idx → Ob} where
  open is-dense-separating-family
```
-->

Equivalently, a dense separating family is an family $S_i : I \to \cC$ such
that the functors $\cC(S_i,-)$ are [[jointly fully faithful]].
Unfortunately, we need to jump through some hoops to construct the
appropriate functor from the full subcategory generated
by $S_i$ into $[\cC, \Sets]$

```agda
  jointly-ff→dense-separating-family
    : is-jointly-fully-faithful (よcov C F∘ Functor.op (Forget-family sᵢ))
    → is-dense-separating-family sᵢ
  jointly-ff→dense-separating-family joint-ff .universal eta p =
    equiv→inverse joint-ff λ where
      .η → eta
      .is-natural _ _ g → ext λ f → p f g
  jointly-ff→dense-separating-family joint-ff .commute {i = i} {eᵢ = eᵢ} =
    equiv→counit joint-ff _ ηₚ i $ₚ eᵢ
  jointly-ff→dense-separating-family joint-ff .unique h p =
    sym (equiv→unit joint-ff h) ∙ ap (equiv→inverse joint-ff) (ext p)

  dense-separating-family→jointly-ff
    : is-dense-separating-family sᵢ
    → is-jointly-fully-faithful (よcov C F∘ Functor.op (Forget-family sᵢ))
  dense-separating-family→jointly-ff dense =
    is-iso→is-equiv $ iso
      (λ α → dense .universal (α .η) (λ f g → α .is-natural _ _ g $ₚ f))
      (λ α → ext λ i eᵢ → dense .commute)
      λ h → sym (dense .unique h λ i eᵢ → refl)
```

We can also express this universality using the language of colimits.
In particular, if $S_i : I \to \cC$ is a dense separating family,
then every object of $\cC$ can be expressed as a colimit over the
diagram $\mathrm{Dom}_{X} : S_i \downarrow X \to \cC$ that takes a map
$\cC(S_i, X)$ to its domain.

<!--
```agda
module _
  {Idx : Type ℓ}
  {sᵢ : Idx → Ob}
  where
  open ↓Obj using (map)
  open ↓Hom using (com)
```
-->

```agda
  Approx : ∀ x → Functor (Forget-family sᵢ ↘ x) C
  Approx x = Forget-family sᵢ F∘ Dom _ _

  is-dense-separating-family→coyoneda
    : is-dense-separating-family sᵢ
    → ∀ (x : Ob) → is-colimit (Approx x) x θ↘
```

First, note that we have a canonical cocone $\mathrm{Dom}_{X} \to \Delta_{X}$
that takes an object in slice $\cC(S_i, X)$ to itself.

```agda
  is-dense-separating-family→coyoneda dense x = to-is-colimitp colim refl where
    module dense = is-dense-separating-family dense
    open make-is-colimit

    colim : make-is-colimit (Approx x) x
    colim .ψ x = x .map
    colim .commutes f = f .com ∙ idl _
```

Moreover, this cocone is universal: given another cocone $\epsilon$ over $Y$,
we can form a map $X \to Y$ by using the universal property of dense
separating families.

```agda
    colim .universal eps p =
      dense.universal
        (λ i fᵢ → eps (↓obj fᵢ))
        (λ f g → sym (p (↓hom (sym (idl _)))))
    colim .factors {j} eps p =
      dense.universal _ _ ∘ colim .ψ j ≡⟨ dense.commute ⟩
      eps (↓obj (j .map))              ≡⟨ ap eps (↓Obj-path _ _ refl refl refl) ⟩
      eps j                            ∎
    colim .unique eta p other q = dense.unique other (λ i fᵢ → q (↓obj fᵢ))
```

As expected, the converse also holds: the proof is more or less the
previous proof in reverse, so we do not comment on it too deeply.

```agda
  coyoneda→is-dense-separating-family
    : (∀ (x : Ob) → is-colimit (Approx x) x θ↘)
    → is-dense-separating-family sᵢ
  coyoneda→is-dense-separating-family colim = dense where
    module colim {x} = is-colimit (colim x)
    open is-dense-separating-family

    dense : is-dense-separating-family sᵢ
    dense .universal eta p = colim.universal
      (λ f → eta _ (f .map))
      (λ γ → sym (p _ _) ∙ ap (eta _) (γ .com ∙ idl _))
    dense .commute {eᵢ = eᵢ} = colim.factors {j = ↓obj eᵢ} _ _
    dense .unique h p        = colim.unique _ _ _ λ j → p _ (j .map)
```
