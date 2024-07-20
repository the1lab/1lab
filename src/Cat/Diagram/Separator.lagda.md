---
description: |
  We define separating objects, and prove some basic properties.
---

<!--
```agda
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Functor.FullSubcategory
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Limit.Finite
open import Cat.Instances.Shape.Terminal
open import Cat.Instances.Sets
open import Cat.Functor.Constant
open import Cat.Functor.Conservative
open import Cat.Functor.Properties
open import Cat.Functor.Compose
open import Cat.Instances.Comma
open import Cat.Functor.Joint
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Reasoning
import Cat.Morphism.StrongEpi
```
-->

```agda
module Cat.Diagram.Separator {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
open Cat.Morphism.StrongEpi C
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
2 functions $f, g : A \to B$ by showing that they are equal pointwise.
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

# Separating Families

Many categories lack a single separating object $S : \cC$, but do have a *family* of
separating objects $S_i : I \to \cC$. The canonical is the category of presheaves:
we cannot determine equality of natural transformations $\alpha, \beta : P \to Q$
by looking at all maps $S \to P$ single $S$, but we *can* if we look at all
maps $\yo(A) \to P$! This leads us to the following notion:

:::{.definition #separating-family}
A **separating family** is a family of objects $S : I \to \cC$ such that:
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
separating-family-identity-system separate =
  set-identity-system (λ _ _ → hlevel 1) separate
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
  {s : Ob}
  (copowers : (I : Set ℓ) → has-coproducts-indexed-by C ∣ I ∣)
  where
  private
    module Elts x = Indexed-coproduct (copowers (el! (Hom s x)) λ f → s)

  separator→epi : ∀ {x} → is-separator s → is-epic (Elts.match x λ f → f)
  separator→epi {x} separate f g p = separate λ e →
    f ∘ e                       ≡⟨ pushr (sym (Elts.commute x)) ⟩
    (f ∘ (Elts.match x λ f → f)) ∘ Elts.ι x e ≡⟨ p ⟩∘⟨refl ⟩
    (g ∘ (Elts.match x λ f → f)) ∘ Elts.ι x e ≡⟨ pullr (Elts.commute x) ⟩
    g ∘ e                       ∎
```

Conversely, if the canonical map $\gamma_{X} : \cC(S,X) \otimes S \to X$
is an epimorphism for every $X$, then $S$ is a separator.

Let $f, g : \cC(X, Y)$ such that $f \circ e = g \circ e$ for every
$e : \cC(S, X)$. Note that $f \circ \gamma_{X} \circ \iota = g \circ \gamma_{X} \circ \iota$
by our hypothesis, so $f \circ \gamma_{X} = g \circ \gamma_{X}$. Moreover,
$\gamma_{X}$ is an epi, so $f = g$.

```agda
  epi→separator : (∀ {x} → is-epic (Elts.match x λ f → f)) → is-separator s
  epi→separator epic {f = f} {g = g} p =
    epic f g $ Elts.unique₂ _ λ e →
      sym (assoc _ _ _)
      ∙ p _
      ∙ assoc _ _ _
```

A similar result hold for separating families, but with: a family $S_i : \cC$
is a separating family if and only if the canonical map
$\coprod_{\Sigma (i : I), \cC(S_i, X)} S_i \to X$ is an epimorphism.

<!--
```agda
module _
  {Idx : Type ℓ}
  {sᵢ : Idx → Ob}
  (Idx-set : is-set Idx)
  (coprods : (I : Set ℓ) → has-coproducts-indexed-by C ∣ I ∣)
  where
  private
    instance
      H-Level-Idx : ∀ {n} → H-Level Idx (2 + n)
      H-Level-Idx = basic-instance 2 Idx-set

```
-->

```agda
  private
    module Elts (x : Ob) =
      Indexed-coproduct (coprods (el! (Σ[ i ∈ Idx ] Hom (sᵢ i) x)) (sᵢ ⊙ fst))

  separating-family→epi
    : ∀ {x}
    → is-separating-family sᵢ
    → is-epic (Elts.match x snd)

  epi→separating-family
    : (∀ {x} → is-epic (Elts.match x snd))
    → is-separating-family sᵢ
```

<details>
<summary>The proof is almost identical to the single-object case, so
we omit the details.
</summary>
```agda
  separating-family→epi {x = x} separate f g p = separate λ {i} eᵢ →
    f ∘ eᵢ                                     ≡⟨ pushr (sym (Elts.commute x)) ⟩
    (f ∘ Elts.match x snd) ∘ Elts.ι x (i , eᵢ) ≡⟨ p ⟩∘⟨refl ⟩
    (g ∘ Elts.match x snd) ∘ Elts.ι x (i , eᵢ) ≡⟨ pullr (Elts.commute x) ⟩
    g ∘ eᵢ                                     ∎

  epi→separating-family epic {f = f} {g = g} p =
    epic f g $ Elts.unique₂ _ λ (i , eᵢ) →
      sym (assoc _ _ _)
      ∙ p _
      ∙ assoc _ _ _
```
</details>

# Strong separators

```agda
module _
  (copowers : (I : Set ℓ) → has-coproducts-indexed-by C ∣ I ∣)
  where
  private
    module Elts s x = Indexed-coproduct (copowers (el! (Hom s x)) λ f → s)

  is-strong-separator : Ob → Type (o ⊔ ℓ)
  is-strong-separator s = ∀ {x} → is-strong-epi (Elts.match s x λ e → e)

  strong-separator→separator
    : ∀ {s}
    → is-strong-separator s
    → is-separator s
  strong-separator→separator strong =
    epi→separator copowers (strong .fst)
```

```agda
  strong-separator→conservative
    : ∀ {s}
    → is-strong-separator s
    → is-conservative (Hom-from C s)
  strong-separator→conservative {s = s} strong {A = a} {B = b} {f = f} f∘-inv =
    strong-epi-mono→is-invertible
      f-mono
      f-strong-epi
    where
      module f∘- = Equiv (f ∘_ , is-invertible→is-equiv f∘-inv)

      f-mono : is-monic f
      f-mono u v p =
        strong-separator→separator strong λ e →
        f∘-.injective (extendl p)

      f' : Hom (Elts.ΣF s b) a
      f' = Elts.match s b λ e → f∘-.from e

      f'-factors : f ∘ f' ≡ Elts.match s b (λ e → e)
      f'-factors = Elts.unique s b _ λ e →
        (f ∘ f') ∘ Elts.ι _ _ e ≡⟨ pullr (Elts.commute s b) ⟩
        f ∘ f∘-.from e          ≡⟨ f∘-.ε e ⟩
        e                       ∎

      f-strong-epi : is-strong-epi f
      f-strong-epi =
        strong-epi-cancell f f' $
        subst is-strong-epi (sym f'-factors) strong
```

```agda
  finitely-complete+conservative→strong-separator
    : ∀ {s}
    → Finitely-complete C
    → is-conservative (Hom-from C s)
    → is-strong-separator s
  finitely-complete+conservative→strong-separator lex f∘-conservative =
    is-extremal-epi→is-strong-epi lex λ m i p →
    f∘-conservative $
    is-equiv→is-invertible $
    is-iso→is-equiv $ iso
      (λ e → i ∘ Elts.ι _ _ e)
      (λ f' → pulll (sym p) ∙ Elts.commute _ _)
      (λ e → m .monic _ _ (pulll (sym p) ∙ Elts.commute _ _))
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
  $\eta i (f \circ g) = eta j f \circ g$ induce maps $u_{\eta} : \cC(X,Y)$; and
- For every $e_i : \cC(S_i, X)$, $u_{\eta} \circ e_i = \eta i e_i$; and
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
    : is-jointly-fully-faithful (よcov C F∘ Functor.op (Forget-family {C = C} sᵢ))
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
    → is-jointly-fully-faithful (よcov C F∘ Functor.op (Forget-family {C = C} sᵢ))
  dense-separating-family→jointly-ff dense =
    is-iso→is-equiv $ iso
      (λ α → dense .universal (α .η) (λ f g → α .is-natural _ _ g $ₚ f))
      (λ α → ext λ i eᵢ → dense .commute)
      λ h → sym (dense .unique h λ i eᵢ → refl)
```

We can also express this universality using the language of colimits.
In particular, if $S\_i : I \to \cC$ is a dense separating family,
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
  open ↓Hom using (sq)
```
-->

```agda
  Approx : ∀ x → Functor (Forget-family {C = C} sᵢ ↘ x) C
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
    colim .commutes f = f .sq ∙ idl _
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
      eps (↓obj (j .map))             ≡⟨ ap eps (↓Obj-path _ _ refl refl refl) ⟩
      eps j                           ∎
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
    dense .universal eta p =
      colim.universal
        (λ f → eta _ (f .map))
        (λ γ → sym (p _ _) ∙ ap (eta _) (γ .sq ∙ idl _))
    dense .commute {eᵢ = eᵢ} =
      colim.factors {j = ↓obj eᵢ} _ _
    dense .unique h p =
      colim.unique _ _ _ λ j → p _ (j .map)
```
