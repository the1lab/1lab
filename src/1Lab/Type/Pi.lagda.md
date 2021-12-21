```
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Type.Pi where
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
  the-iso .fst f x = rng .fst (f (dom-iso .isIso.inv x))
  the-iso .snd .isIso.inv f x = rng-iso .isIso.inv (f (dom .fst x))
  the-iso .snd .isIso.rinv f =
    funext λ x → rng-iso .isIso.rinv _
               ∙ ap f (dom-iso .isIso.rinv _)
  the-iso .snd .isIso.linv f =
    funext λ x → rng-iso .isIso.linv _
               ∙ ap f (dom-iso .isIso.linv _)
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
  open isIso
  isom : Iso _ _
  isom .fst = funextDep
  isom .snd .isIso.inv q p i = q i (p i)

  isom .snd .rinv q m i x =
    comp
      (λ k → B i (coei→i A i x (k ∨ m)))
      (λ k → λ
        { (i = i0) → f (coei→i A i0 x (k ∨ m))
        ; (i = i1) → g (coei→i A i1 x (k ∨ m))
        ; (m = i1) → q i x
        })
      (q i (coei→i A i x m))

  isom .snd .linv h m p i =
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

heteroHomotopy≃Homotopy
  : {A : I → Type ℓ} {B : (i : I) → Type ℓ₁}
    {f : A i0 → B i0} {g : A i1 → B i1}

  → ({x₀ : A i0} {x₁ : A i1} → PathP A x₀ x₁ → PathP B (f x₀) (g x₁))
  ≃ ((x₀ : A i0) → PathP B (f x₀) (g (transport (λ i → A i) x₀)))

heteroHomotopy≃Homotopy {A = A} {B} {f} {g} = Iso→Equiv isom where
  open isIso
  isom : Iso _ _
  isom .fst h x₀ = h (isContrSinglP A x₀ .centre .snd)
  isom .snd .inv k {x₀} {x₁} p =
    subst (λ fib → PathP B (f x₀) (g (fib .fst))) (isContrSinglP A x₀ .paths (x₁ , p)) (k x₀)

  isom .snd .rinv k = funext λ x₀ →
    ap (λ α → subst (λ fib → PathP B (f x₀) (g (fib .fst))) α (k x₀))
      (isProp→isSet isPropSinglP (isContrSinglP A x₀ .centre) _
        (isContrSinglP A x₀ .paths (isContrSinglP A x₀ .centre))
        refl)
    ∙ transport-refl (k x₀)

  isom .snd .linv h j {x₀} {x₁} p =
    transp
      (λ i → PathP B (f x₀) (g (isContrSinglP A x₀ .paths (x₁ , p) (i ∨ j) .fst)))
      j
      (h (isContrSinglP A x₀ .paths (x₁ , p) j .snd))
```
