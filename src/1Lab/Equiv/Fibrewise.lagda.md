---
description: |
  We establish a correspondence between "fibrewise equivalences" and
  equivalences of total spaces (Σ-types).
---
<!--
```agda
open import 1Lab.HLevel.Retracts
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
```
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
