```
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Type
open import 1Lab.Path

module 1Lab.Data.Pi.Properties where
```

<!--
```
private variable
  ℓ ℓ₁ : Level
  A B C D : Type ℓ
  P Q : A → Type ℓ
```
-->

# Properties of Π types

This module contains properties of dependent function types, not necessarily
organised in any way.

## Closure under equivalences

Univalence automatically implies that every type former respects
equivalences. However, this theorem is limited to equivalences between
types _in the same universe_. Thus, there are functions to perturb the
codomain of a dependent function by an equivalence across universe levels:

```agda
Π-cod≃ : ((x : A) → P x ≃ Q x) → ((x : A) → P x) ≃ ((x : A) → Q x)
Π-cod≃ k .fst f x = k x .fst (f x)
Π-cod≃ k .snd .isEqv f .centre .fst x   = equiv-centre (k x) (f x) .fst
Π-cod≃ k .snd .isEqv f .centre .snd i x = equiv-centre (k x) (f x) .snd i
Π-cod≃ k .snd .isEqv f .paths (g , p) i .fst x =
  equiv-path (k x) (f x) (g x , λ j → p j x) i .fst
Π-cod≃ k .snd .isEqv f .paths (g , p) i .snd j x =
  equiv-path (k x) (f x) (g x , λ k → p k x) i .snd j

Π-impl-cod≃ : ((x : A) → P x ≃ Q x) → ({x : A} → P x) ≃ ({x : A} → Q x)
Π-impl-cod≃ k .fst f {x} = k x .fst (f {x})
Π-impl-cod≃ k .snd .isEqv f .centre .fst {x}   = equiv-centre (k x) (f {x}) .fst
Π-impl-cod≃ k .snd .isEqv f .centre .snd i {x} = equiv-centre (k x) (f {x}) .snd i
Π-impl-cod≃ k .snd .isEqv f .paths (g , p) i .fst {x} =
  equiv-path (k x) (f {x}) (g {x} , λ j → p j {x}) i .fst
Π-impl-cod≃ k .snd .isEqv f .paths (g , p) i .snd j {x} =
  equiv-path (k x) (f {x}) (g {x} , λ k → p k {x}) i .snd j
```

For non-dependent functions, we can easily perturb both domain and
codomain:

```agda
function≃ : (A ≃ B) → (C ≃ D) → (A → C) ≃ (B → D)
function≃ dom rng = Iso→Equiv the-iso where
  rng-iso = isEquiv→isIso (rng .snd)
  dom-iso = isEquiv→isIso (dom .snd)

  the-iso : Iso _ _
  the-iso .fst f x = rng .fst (f (dom-iso .isIso.g x))
  the-iso .snd .isIso.g f x = rng-iso .isIso.g (f (dom .fst x))
  the-iso .snd .isIso.right-inverse f =
    funext λ x → rng-iso .isIso.right-inverse _
               ∙ ap f (dom-iso .isIso.right-inverse _)
  the-iso .snd .isIso.left-inverse f =
    funext λ x → rng-iso .isIso.left-inverse _
               ∙ ap f (dom-iso .isIso.left-inverse _)
```


## Dependent Funext

When the domain and codomain are simple types, equality of functions is
characterised by `funext`{.Agda}. We can generalise this to `funextDep`,
in which the domain and codomain are allowed to be lines of types:

```agda
funextDep
  : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
    {f : (x : A i0) → B i0 x} {g : (x : A i1) → B i1 x}
  → ( {x₀ : A i0} {x₁ : A i1}
    → (p : PathP A x₀ x₁)
    → PathP (λ i → B i (p i)) (f x₀) (g x₁) )
  → PathP (λ i → (x : A i) → B i x) f g

funextDep {A = A} {B} {f} {g} h i x =
  comp
    (λ k → B i (coei→i A i x k))
    (λ k → λ
      { (i = i0) → f (coei→i A i0 x k)
      ; (i = i1) → g (coei→i A i1 x k)
      })
    (h (λ j → coei→j A i j x) i)
```

A very ugly cubical argument shows that this function is an equivalence:

```agda
funextDep≃
  : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
    {f : (x : A i0) → B i0 x} {g : (x : A i1) → B i1 x}

  → ( {x₀ : A i0} {x₁ : A i1} (p : PathP A x₀ x₁)
    → PathP (λ i → B i (p i)) (f x₀) (g x₁)
    )
  ≃ PathP (λ i → (x : A i) → B i x) f g

funextDep≃ {A = A} {B} {f} {g} = Iso→Equiv isom where
  open isIso hiding (g)
  isom : Iso _ _
  isom .fst = funextDep
  isom .snd .isIso.g q p i = q i (p i)

  isom .snd .right-inverse q m i x =
    comp
      (λ k → B i (coei→i A i x (k ∨ m)))
      (λ k → λ
        { (i = i0) → f (coei→i A i0 x (k ∨ m))
        ; (i = i1) → g (coei→i A i1 x (k ∨ m))
        ; (m = i1) → q i x
        })
      (q i (coei→i A i x m))

  isom .snd .left-inverse h m p i =
    comp
      (λ k → B i (lemi→i m k))
      (λ k → λ
        { (i = i0) → f (lemi→i m k)
        ; (i = i1) → g (lemi→i m k)
        ; (m = i1) → h p i
        })
      (h (λ j → lemi→j j m) i)
    where
    lemi→j : ∀ j → coei→j A i j (p i) ≡ p j
    lemi→j j =
      coei→j (λ k → coei→j A i k (p i) ≡ p k) i j (coei→i A i (p i))

    lemi→i : PathP (λ m → lemi→j i m ≡ p i) (coei→i A i (p i)) refl
    lemi→i =
      sym (coei→i (λ k → coei→j A i k (p i) ≡ p k) i (coei→i A i (p i)))
      ◁ λ m k → lemi→j i (m ∨ k)
```