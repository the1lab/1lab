---
description: |
  We establish a correspondence between "fibrewise equivalences" and
  equivalences of total spaces (Σ-types), and define equivalences over.
---
<!--
```agda
open import 1Lab.Equiv.FromPath
open import 1Lab.HLevel.Closure
open import 1Lab.Type.Sigma
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.Equiv.Fibrewise where
```

# Fibrewise equivalences

In HoTT, a type family `P : A → Type` can be seen as a [_fibration_]
with total space `Σ P`, with the fibration being the projection
`fst`{.Agda}. Because of this, a function with type `(X : _) → P x → Q
x` can be referred as a _fibrewise map_.

[_fibration_]: https://ncatlab.org/nlab/show/fibration

A function like this can be lifted to a function on total spaces:

<!--
```agda
private variable
  ℓ : Level
  A B : Type ℓ
  P Q : A → Type ℓ
```
-->

```agda
total : ((x : A) → P x → Q x)
      → Σ A P → Σ A Q
total f (x , y) = x , f x y
```

Furthermore, the fibres of `total f` correspond to fibres of f, in the
following manner:

```agda
total-fibres : {f : (x : A) → P x → Q x} {x : A} {v : Q x}
             → Iso (fibre (f x) v) (fibre (total f) (x , v))
total-fibres {A = A} {P = P} {Q = Q} {f = f} {x = x} {v = v} = the-iso where
  open is-iso

  to : {x : A} {v : Q x} → fibre (f x) v → fibre (total f) (x , v)
  to (v' , p) = (_ , v') , λ i → _ , p i

  from : {x : A} {v : Q x} → fibre (total f) (x , v) → fibre (f x) v
  from ((x , v) , p) = transport (λ i → fibre (f (p i .fst)) (p i .snd)) (v , refl)

  the-iso : {x : A} {v : Q x} → Iso (fibre (f x) v) (fibre (total f) (x , v))
  the-iso .fst = to
  the-iso .snd .is-iso.inv = from
  the-iso .snd .is-iso.rinv ((x , v) , p) =
    J (λ { _ p → to (from ((x , v) , p)) ≡ ((x , v) , p) })
      (ap to (J-refl {A = Σ A Q} (λ { (x , v) _ → fibre (f x) v } ) (v , refl)))
      p
  the-iso .snd .is-iso.linv (v , p) =
    J (λ { _ p → from (to (v , p)) ≡ (v , p) })
      (J-refl {A = Σ A Q} (λ { (x , v) _ → fibre (f x) v } ) (v , refl))
      p
```

From this, we immediately get that a fibrewise transformation is an
equivalence iff. it induces an equivalence of total spaces by `total`.

```agda
total→equiv : {f : (x : A) → P x → Q x}
            → is-equiv (total f)
            → {x : A} → is-equiv (f x)
total→equiv eqv {x} .is-eqv y =
  iso→is-hlevel 0 (total-fibres .snd .is-iso.inv)
                  (is-iso.inverse (total-fibres .snd))
                  (eqv .is-eqv (x , y))

equiv→total : {f : (x : A) → P x → Q x}
            → ({x : A} → is-equiv (f x))
            → is-equiv (total f)
equiv→total always-eqv .is-eqv y =
  iso→is-hlevel 0
    (total-fibres .fst)
    (total-fibres .snd)
    (always-eqv .is-eqv (y .snd))
```

## Equivalences over {defines="equivalence-over"}

::: {.popup .keep}
We can generalise the notion of fibrewise equivalence to families
$P : A \to \type$, $Q : B \to \type$ over *different* base types,
provided we have an equivalence $e : A \simeq B$. In that case, we
say that $P$ and $Q$ are **equivalent over** $e$ if $P(a) \simeq Q(b)$
whenever $a : A$ and $b : B$ are identified [[over|path over]] $e$.
:::

Using univalence, we can see this as a special case of [[dependent
paths]], where the base type is taken to be the universe and the type
family sends a type $A$ to the type of type families over $A$. However,
the following explicit definition is easier to work with.

<!--
```agda
module _ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} where
```
-->

```agda
  _≃[_]_ : ∀ {ℓp ℓq} (P : A → Type ℓp) (e : A ≃ B) (Q : B → Type ℓq) → Type _
  P ≃[ e ] Q = ∀ (a : A) (b : B) → e .fst a ≡ b → P a ≃ Q b
```

While this definition is convenient to *use*, we provide helpers that
make it easier to *build* equivalences over.

<!--
```agda
  module _ {ℓp ℓq} {P : A → Type ℓp} {Q : B → Type ℓq} (e : A ≃ B) where
    private module e = Equiv e
```
-->

```agda
    over-left→over : (∀ (a : A) → P a ≃ Q (e.to a)) → P ≃[ e ] Q
    over-left→over e' a b p = e' a ∙e line→equiv (λ i → Q (p i))

    over-right→over : (∀ (b : B) → P (e.from b) ≃ Q b) → P ≃[ e ] Q
    over-right→over e' a b p = line→equiv (λ i → P (e.adjunctl p i)) ∙e e' b

    prop-over-ext
      : (∀ {a} → is-prop (P a))
      → (∀ {b} → is-prop (Q b))
      → (∀ (a : A) → P a → Q (e.to a))
      → (∀ (b : B) → Q b → P (e.from b))
      → P ≃[ e ] Q
    prop-over-ext propP propQ P→Q Q→P a b p = prop-ext propP propQ
      (subst Q p ∘ P→Q a)
      (subst P (sym (e.adjunctl p)) ∘ Q→P b)
```

An equivalence over $e$ induces an equivalence of total spaces:

```agda
    over→total : P ≃[ e ] Q → Σ A P ≃ Σ B Q
    over→total e' = Σ-ap e λ a → e' a (e.to a) refl
```

<!--
```agda
subst-fibrewise
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {B' : A → Type ℓ''} (g : ∀ x → B x → B' x)
  → {x y : A} (p : x ≡ y) (h : B x) → subst B' p (g x h) ≡ g y (subst B p h)
subst-fibrewise {B = B} {B'} g {x} p h = J (λ y p → subst B' p (g x h) ≡ g y (subst B p h)) (transport-refl _ ∙ ap (g x) (sym (transport-refl _))) p
```
-->
