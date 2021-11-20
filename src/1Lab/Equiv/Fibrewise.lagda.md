```
open import 1Lab.HLevel.Retracts
open import 1Lab.Equiv
open import 1Lab.Type
open import 1Lab.Path

module 1Lab.Equiv.Fibrewise where
```

# Fibrewise Equivalences

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

```
total : ((x : A) → P x → Q x)
      → Σ P → Σ Q
total f (x , y) = x , f x y
```

Furthermore, the fibres of `total f` correspond to fibres of f, in the
following manner:

```
total-fibers : {f : (x : A) → P x → Q x} {x : A} {v : Q x}
             → Iso (fibre (f x) v) (fibre (total f) (x , v))
total-fibers {A = A} {P = P} {Q = Q} {f = f} {x = x} {v = v} = the-iso where
  open isIso

  to : {x : A} {v : Q x} → fibre (f x) v → fibre (total f) (x , v)
  to (v' , p) = (_ , v') , λ i → _ , p i

  from : {x : A} {v : Q x} → fibre (total f) (x , v) → fibre (f x) v
  from ((x , v) , p) =
    J (λ { (x , v) _ → fibre (f x) v } )
      (v , refl)
      p
  
  the-iso : {x : A} {v : Q x} → Iso (fibre (f x) v) (fibre (total f) (x , v))
  fst the-iso = to
  g (snd the-iso) = from
  right-inverse (snd the-iso) ((x , v) , p) =
    J (λ { _ p → to (from ((x , v) , p)) ≡ ((x , v) , p) })
      (ap to (JRefl {A = Σ Q} (λ { (x , v) _ → fibre (f x) v } ) (v , refl)))
      p
  left-inverse (snd the-iso) (v , p) =
    J (λ { _ p → from (to (v , p)) ≡ (v , p) })
      (JRefl {A = Σ Q} (λ { (x , v) _ → fibre (f x) v } ) (v , refl))
      p
```

From this, we immediately get that a fibrewise transformation is an
equivalence iff. it induces an equivalence of total spaces by `total`.

```
total→equiv : {f : (x : A) → P x → Q x}
            → isEquiv (total f)
            → {x : A} → isEquiv (f x)
isEquiv.isEqv (total→equiv eqv {x}) y =
  isHLevel-iso 0 (total-fibers .snd .isIso.g)
                 (isIso.inverse (total-fibers .snd))
                 (eqv .isEqv (x , y))

equiv→total : {f : (x : A) → P x → Q x}
            → ({x : A} → isEquiv (f x))
            → isEquiv (total f)
isEquiv.isEqv (equiv→total always-eqv) y =
  isHLevel-iso 0 (total-fibers .fst)
                 (total-fibers .snd)
                 (always-eqv .isEqv (y .snd))
```