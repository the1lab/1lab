<!--
```agda
open import 1Lab.Path.Cartesian
open import 1Lab.Type.Sigma
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.Type.Pi where
```

<!--
```agda
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
Π-cod≃ k .snd .is-eqv f .centre .fst x   = equiv-centre (k x) (f x) .fst
Π-cod≃ k .snd .is-eqv f .centre .snd i x = equiv-centre (k x) (f x) .snd i
Π-cod≃ k .snd .is-eqv f .paths (g , p) i .fst x =
  equiv-path (k x) (f x) (g x , λ j → p j x) i .fst
Π-cod≃ k .snd .is-eqv f .paths (g , p) i .snd j x =
  equiv-path (k x) (f x) (g x , λ k → p k x) i .snd j

Π-dom≃ : (e : B ≃ A) → ((x : A) → P x) ≃ ((x : B) → P (e .fst x))
Π-dom≃ e .fst k x = k (e .fst x)
Π-dom≃ {P = P} e .snd = is-iso→is-equiv record where
  module e = Equiv e

  from k x = subst P (e.ε x) (k (e.from x))
  rinv k = funext λ x →
      ap₂ (subst P) (sym (e.zig x)) (sym (from-pathp (symP (ap k (e.η x)))))
    ∙ transport⁻transport (ap P (ap (e .fst) (sym (e.η x)))) (k x)
  linv k = funext λ x →
      ap (subst P _) (sym (from-pathp (symP (ap k (e.ε x)))))
    ∙ transport⁻transport (sym (ap P (e.ε x))) _

Π-impl-cod≃ : ((x : A) → P x ≃ Q x) → ({x : A} → P x) ≃ ({x : A} → Q x)
Π-impl-cod≃ k .fst f {x} = k x .fst (f {x})
Π-impl-cod≃ k .snd .is-eqv f .centre .fst {x}   = equiv-centre (k x) (f {x}) .fst
Π-impl-cod≃ k .snd .is-eqv f .centre .snd i {x} = equiv-centre (k x) (f {x}) .snd i
Π-impl-cod≃ k .snd .is-eqv f .paths (g , p) i .fst {x} =
  equiv-path (k x) (f {x}) (g {x} , λ j → p j {x}) i .fst
Π-impl-cod≃ k .snd .is-eqv f .paths (g , p) i .snd j {x} =
  equiv-path (k x) (f {x}) (g {x} , λ k → p k {x}) i .snd j
```

For non-dependent functions, we can easily perturb both domain and
codomain:

```agda
function≃ : (A ≃ B) → (C ≃ D) → (A → C) ≃ (B → D)
function≃ dom rng .fst f x = rng .fst (f (Equiv.from dom x))
function≃ dom rng .snd = is-iso→is-equiv record where
  module dom = Equiv dom
  module rng = Equiv rng

  from f x = rng.from (f (dom .fst x))
  linv f = funext λ x → rng.η _ ∙ ap f (dom.η _)
  rinv f = funext λ x → rng.ε _ ∙ ap f (dom.ε _)

equiv≃ : (A ≃ B) → (C ≃ D) → (A ≃ C) ≃ (B ≃ D)
equiv≃ x y = Σ-ap (function≃ x y) λ f → prop-ext
  (is-equiv-is-prop _) (is-equiv-is-prop _)
  (λ e → ∘-is-equiv (∘-is-equiv ((x e⁻¹) .snd) e) (y .snd))
  λ e → equiv-cancelr ((x e⁻¹) .snd) (equiv-cancell (y .snd) e)
```


## Dependent funext

When the domain and codomain are simple types (rather than a higher
shape), paths in function spaces are characterised by `funext`{.Agda}.
We can generalise this to `funext-dep`, in which the domain and codomain
are allowed to be lines of types:

```agda
funextP
  : ∀ {A : Type ℓ} {B : A → I → Type ℓ₁}
  → {f : ∀ a → B a i0} {g : ∀ a → B a i1}
  → (∀ a → PathP (B a) (f a) (g a))
  → PathP (λ i → ∀ a → B a i) f g
funextP p i x = p x i

funext-dep
  : ∀ {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁} {f g}
  → ( ∀ {x₀ x₁} (p : PathP A x₀ x₁)
    → PathP (λ i → B i (p i)) (f x₀) (g x₁) )
  → PathP (λ i → (x : A i) → B i x) f g
funext-dep {A = A} {B} h i x =
  transp (λ k → B i (coei→i A i x k)) (i ∨ ~ i)
    (h (λ j → coe A i j x) i)
```

A slightly wonky cubical argument shows that this function is an
equivalence. The complication comes from `coe` not being definitionally
the identity when staying at a variable point in the interval.

<!--
```agda
funext-dep≃
  : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
    {f : (x : A i0) → B i0 x} {g : (x : A i1) → B i1 x}

  → ( {x₀ : A i0} {x₁ : A i1} (p : PathP A x₀ x₁)
    → PathP (λ i → B i (p i)) (f x₀) (g x₁)
    )
  ≃ PathP (λ i → (x : A i) → B i x) f g
```
-->

```agda
funext-dep≃ {A = A} {B} {f} {g} = Iso→Equiv isom where
  open is-iso
  isom : Iso _ _
  isom .fst = funext-dep
  isom .snd .is-iso.from q p i = q i (p i)

  isom .snd .rinv q m i x =
    transp (λ k → B i (coei→i A i x (k ∨ m))) (m ∨ i ∨ ~ i) (q i (coei→i A i x m))

  isom .snd .linv h m p i =
    transp (λ k → B i (lemi→i m k)) (m ∨ i ∨ ~ i) (h (λ j → lemi→j j m) i)
    where
      lemi→j : ∀ j → coe A i j (p i) ≡ p j
      lemi→j j k = coe-path A (λ i → p i) i j k

      lemi→i : PathP (λ m → lemi→j i m ≡ p i) (coei→i A i (p i)) refl
      lemi→i m k = coei→i A i (p i) (m ∨ k)

hetero-homotopy≃homotopy
  : {A : I → Type ℓ} {B : (i : I) → Type ℓ₁}
    {f : A i0 → B i0} {g : A i1 → B i1}

  → ({x₀ : A i0} {x₁ : A i1} → PathP A x₀ x₁ → PathP B (f x₀) (g x₁))
  ≃ ((x₀ : A i0) → PathP B (f x₀) (g (coe0→1 A x₀)))

hetero-homotopy≃homotopy {A = A} {B} {f} {g} = Iso→Equiv isom where
  open is-iso
  isom : Iso _ _
  isom .fst h x₀ = h (SinglP-is-contr A x₀ .centre .snd)
  isom .snd .from k {x₀} {x₁} p =
    subst (λ fib → PathP B (f x₀) (g (fib .fst))) (SinglP-is-contr A x₀ .paths (x₁ , p)) (k x₀)

  isom .snd .rinv k = funext λ x₀ →
    ap (λ α → subst (λ fib → PathP B (f x₀) (g (fib .fst))) α (k x₀))
      (is-prop→is-set SinglP-is-prop (SinglP-is-contr A x₀ .centre) _
        (SinglP-is-contr A x₀ .paths (SinglP-is-contr A x₀ .centre))
        refl)
    ∙ transport-refl (k x₀)

  isom .snd .linv h j {x₀} {x₁} p =
    transp
      (λ i → PathP B (f x₀) (g (SinglP-is-contr A x₀ .paths (x₁ , p) (i ∨ j) .fst)))
      j
      (h (SinglP-is-contr A x₀ .paths (x₁ , p) j .snd))
```

<!--
```agda
funext≃ : ∀ {a b} {A : Type a} {B : A → Type b}
          {f g : (x : A) → B x}
        → ((x : A) → f x ≡ g x) ≃ (f ≡ g)
funext≃ .fst = funext
funext≃ .snd .is-eqv H .centre = strict-fibres happly H .fst
funext≃ .snd .is-eqv H .paths = strict-fibres happly H .snd

funextP'
  : ∀ {A : Type ℓ} {B : A → I → Type ℓ₁}
  → {f : ∀ {a} → B a i0} {g : ∀ {a} → B a i1}
  → (∀ {a} → PathP (B a) (f {a}) (g {a}))
  → PathP (λ i → ∀ {a} → B a i) f g
funextP' p i {x} = p {x} i

funext-dep-i0
  : ∀ {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁} {f g}
  → ( ∀ (x : A i0)
    → PathP (λ i → B i (coe0→i A i x)) (f x) (g (coe0→1 A x)))
  → PathP (λ i → (x : A i) → B i x) f g
funext-dep-i0 {A = A} {B} {f} {g} h = funext-dep λ {x₀} {x₁} p →
  subst (λ (p : (i : I) → A i) → PathP (λ i → B i (p i)) (f (p i0)) (g (p i1)))
    (λ j i → coe-path A (λ i → p i) i0 i j)
    (h x₀)

funext-dep-i1
  : ∀ {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁} {f g}
  → ( ∀ (x : A i1)
    → PathP (λ i → B i (coe1→i A i x)) (f (coe1→0 A x)) (g x))
  → PathP (λ i → (x : A i) → B i x) f g
funext-dep-i1 {A = A} {B} {f} {g} h = funext-dep λ {x₀} {x₁} p →
  subst (λ (p : (i : I) → A i) → PathP (λ i → B i (p i)) (f (p i0)) (g (p i1)))
    (λ j i → coe-path A (λ i → p i) i1 i j)
    (h x₁)

funext²
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : ∀ x → B x → Type ℓ''}
      {f g : ∀ x y → C x y}
  → (∀ i j → f i j ≡ g i j)
  → f ≡ g
funext² p i x y = p x y i

funext-square
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
      {f00 f01 f10 f11 : (a : A) → B a}
      {p : f00 ≡ f01}
      {q : f00 ≡ f10}
      {s : f01 ≡ f11}
      {r : f10 ≡ f11}
  → (∀ a → Square (p $ₚ a) (q $ₚ a) (s $ₚ a) (r $ₚ a))
  → Square p q s r
funext-square p i j a = p a i j

Π-⊤-eqv
  : ∀ {ℓ ℓ'} {B : Lift ℓ ⊤ → Type ℓ'}
  → (∀ a → B a) ≃ B _
Π-⊤-eqv .fst b = b _
Π-⊤-eqv .snd = is-iso→is-equiv record where
  from b _ = b
  rinv b = refl
  linv b = refl

Π-contr-eqv
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  → (c : is-contr A)
  → (∀ a → B a) ≃ B (c .centre)
Π-contr-eqv c .fst b = b (c .centre)
Π-contr-eqv {B = B} c .snd = is-iso→is-equiv record where
  from b = λ a → subst B (c .paths a) b
  rinv b = ap (λ e → subst B e b) (is-contr→is-set c _ _ _ _) ∙ transport-refl b
  linv b = funext λ a → from-pathp (ap b (c .paths a))

flip
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : A → B → Type ℓ''}
  → (∀ a b → C a b) → (∀ b a → C a b)
flip f b a = f a b
```
-->
