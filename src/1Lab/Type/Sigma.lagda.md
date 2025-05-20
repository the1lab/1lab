<!--
```agda
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.Type.Sigma where
```

<!--
```agda
private variable
  ℓ ℓ₁ : Level
  A A' X X' Y Y' Z Z' : Type ℓ
  B P Q : A → Type ℓ
  C : (x : A) → B x → Type ℓ
```
-->

# Properties of Σ types

This module contains properties of $\Sigma$ types, not necessarily
organised in any way.

## Universal property

If we have a pair of maps $f : (x : A) \to B(x)$ and $g : (x : A) \to C(x, f(x))$,
then there exists a unique universal map $\langle f , g \rangle : (x : A) \to \Sigma (B x) (C x)$
that commutes with the projections. This is essentially a dependently
typed version of the universal property of [[products]].

```agda
⟨_,_⟩ : (f : (x : A) → B x) → (g : (x : A) → C x (f x)) → (x : A) → Σ (B x) (C x)
⟨ f , g ⟩ x = f x , g x

⟨⟩-unique
  : ∀ {f : (x : A) → B x} {g : (x : A) → C x (f x)}
  → (h : (x : A) → Σ (B x) (C x))
  → (p : fst ∘ h ≡ f)
  → PathP (λ i → (x : A) → C x (p i x)) (snd ∘ h) g
  → h ≡ ⟨ f , g ⟩
⟨⟩-unique h p q i x = p i x , q i x
```

## Groupoid structure

The first thing we prove is that _paths in sigmas are sigmas of paths_.
The type signatures make it clearer:

```agda
Σ-pathp-iso
  : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
    {x : Σ (A i0) (B i0)} {y : Σ (A i1) (B i1)}
  → Iso
      (Σ[ p ∈ PathP A (x .fst) (y .fst) ]
        (PathP (λ i → B i (p i)) (x .snd) (y .snd)))
      (PathP (λ i → Σ (A i) (B i)) x y)

Σ-path-iso
  : {x y : Σ A B}
  → Iso (Σ[ p ∈ x .fst ≡ y .fst ] (subst B p (x .snd) ≡ y .snd)) (x ≡ y)
```

The first of these, using a dependent path, is easy to prove directly,
because paths in cubical type theory _automatically_ inherit the
structure of their domain types. The second is a consequence of the
first, using the fact  that `PathPs and paths over a transport are the
same`{.Agda ident=PathP≡Path}.

```agda
Σ-pathp-iso .fst (p , q) i = p i , q i
Σ-pathp-iso .snd = record
  { from = λ p → (λ i → p i .fst) , (λ i → p i .snd)
  ; rinv = λ p → refl
  ; linv = λ p → refl
  }

Σ-path-iso {B = B} {x} {y} =
  transport (λ i → Iso (Σ[ p ∈ x .fst ≡ y .fst ]
                         (PathP≡Path (λ j → B (p j)) (x .snd) (y .snd) i))
                       (x ≡ y))
            Σ-pathp-iso
```

## Closure under equivalences

Univalence automatically implies that every type former respects
equivalences. However, this theorem is limited to equivalences between
types _in the same universe_. Thus, we provide `Σ-ap-fst`{.Agda},
`Σ-ap-snd`{.Agda}, and `Σ-ap`{.Agda}, which allows one to perturb a
`Σ`{.Agda} by equivalences across levels:

```agda
Σ-ap-snd : ((x : A) → P x ≃ Q x) → Σ A P ≃ Σ A Q
Σ-ap-fst : (e : A ≃ A') → Σ A (B ∘ e .fst) ≃ Σ A' B

Σ-ap : (e : A ≃ A') → ((x : A) → P x ≃ Q (e .fst x)) → Σ A P ≃ Σ A' Q
Σ-ap e e' = Σ-ap-snd e' ∙e Σ-ap-fst e
```

<details>
<summary> The proofs of these theorems are not very enlightening, but
they are included for completeness. </summary>

```agda
Σ-ap-snd {A = A} {P = P} {Q = Q} pointwise = eqv where
  module pwise {i} = Equiv (pointwise i)

  eqv : (Σ _ P) ≃ (Σ _ Q)
  eqv .fst (i , x) = i , pwise.to x
  eqv .snd = is-iso→is-equiv λ where
    .is-iso.from (i , x) → i , pwise.from x
    .is-iso.linv (i , x) → ap₂ _,_ refl (pwise.η _)
    .is-iso.rinv (i , x) → ap₂ _,_ refl (pwise.ε _)

Σ-ap-fst {A = A} {A' = A'} {B = B} e = intro , isEqIntro
 where
  intro : Σ _ (B ∘ e .fst) → Σ _ B
  intro (a , b) = e .fst a , b

  isEqIntro : is-equiv intro
  isEqIntro .is-eqv x = contr ctr isCtr where
    PB : ∀ {x y} → x ≡ y → B x → B y → Type _
    PB p = PathP (λ i → B (p i))

    open Σ x renaming (fst to a'; snd to b)
    open Σ (e .snd .is-eqv a' .is-contr.centre) renaming (fst to ctrA; snd to α)

    ctrB : B (e .fst ctrA)
    ctrB = subst B (sym α) b

    ctrP : PB α ctrB b
    ctrP i = coe1→i (λ i → B (α i)) i b

    ctr : fibre intro x
    ctr = (ctrA , ctrB) , Σ-pathp α ctrP

    isCtr : ∀ y → ctr ≡ y
    isCtr ((r , s) , p) = λ i → (a≡r i , b!≡s i) , Σ-pathp (α≡ρ i) (coh i) where
      open Σ (Σ-pathp-iso .snd .is-iso.from p) renaming (fst to ρ; snd to σ)
      open Σ (Σ-pathp-iso .snd .is-iso.from (e .snd .is-eqv a' .is-contr.paths (r , ρ))) renaming (fst to a≡r; snd to α≡ρ)

      b!≡s : PB (ap (e .fst) a≡r) ctrB s
      b!≡s i = comp (λ k → B (α≡ρ i (~ k))) (∂ i) λ where
        k (i = i0) → ctrP (~ k)
        k (i = i1) → σ (~ k)
        k (k = i0) → b

      coh : PathP (λ i → PB (α≡ρ i) (b!≡s i) b) ctrP σ
      coh i j = fill (λ k → B (α≡ρ i (~ k))) (∂ i) (~ j) λ where
        k (i = i0) → ctrP (~ k)
        k (i = i1) → σ (~ k)
        k (k = i0) → b

Σ-assoc : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : (x : A) → B x → Type ℓ''}
        → (Σ[ x ∈ A ] Σ[ y ∈ B x ] C x y) ≃ (Σ[ x ∈ Σ _ B ] (C (x .fst) (x .snd)))
Σ-assoc .fst (x , y , z) = (x , y) , z
Σ-assoc .snd .is-eqv ((x , y), z) = contr (fib .fst) (fib .snd)
  where fib = strict-fibres _ ((x , y) , z)

Σ-Π-distrib : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : (x : A) → B x → Type ℓ''}
            → ((x : A) → Σ[ y ∈ B x ] C x y)
            ≃ (Σ[ f ∈ ((x : A) → B x) ] ((x : A) → C x (f x)))
Σ-Π-distrib .fst f = (fst ∘ f) , (snd ∘ f)
Σ-Π-distrib .snd .is-eqv (f , r) = contr (fib .fst) (fib .snd)
  where fib = strict-fibres (λ h → ⟨ h .fst , h .snd ⟩) (f , r)
```
</details>


## Paths in subtypes

When `P` is a family of propositions, it is sound to regard `Σ[ x ∈ A ]
(P x)` as a _subtype_ of `A`. This is because identification in the
subtype is characterised uniquely by identification of the first
projections:

```agda
Σ-prop-path
  : {B : A → Type ℓ} (bp : ∀ x → is-prop (B x))
  → {x y : Σ _ B}
  → (x .fst ≡ y .fst) → x ≡ y
Σ-prop-path bp {x} {y} p i =
  p i , is-prop→pathp (λ i → bp (p i)) (x .snd) (y .snd) i
```

The proof that this is an equivalence uses a cubical argument, but the
gist of it is that since `B` is a family of propositions, it really
doesn't matter where we get our equality of `B`-s from - whether it was
from the input, or from `Σ≡Path`{.Agda}.

```agda
Σ-prop-path-is-equiv
  : {B : A → Type ℓ}
  → (bp : ∀ x → is-prop (B x))
  → {x y : Σ _ B}
  → is-equiv (Σ-prop-path bp {x} {y})
Σ-prop-path-is-equiv bp {x} {y} = is-iso→is-equiv λ where
  .is-iso.from   → ap fst
  .is-iso.linv p → refl
```

The `inverse`{.Agda ident=is-iso.from} is the `action on paths`{.Agda
ident=ap} of the `first projection`{.Agda ident=fst}, which lets us
conclude `x .fst ≡ y .fst` from `x ≡ y`. This is a left inverse to
`Σ-prop-path`{.Agda} on the nose. For the other direction, we have the
aforementioned cubical argument:

```agda
  .is-iso.rinv p i j → p j .fst , is-prop→pathp
    (λ k → Path-is-hlevel 1 (bp (p k .fst))
       {x = Σ-prop-path bp {x} {y} (ap fst p) k .snd}
       {y = p k .snd})
    refl refl j i
```

Since `Σ-prop-path`{.Agda} is an equivalence, this implies that its
inverse, `ap fst`{.Agda}, is also an equivalence; This is precisely what
it means for `fst`{.Agda} to be an [[embedding]].

There is also a convenient packaging of the previous two definitions
into an equivalence:

```agda
Σ-prop-path≃
  : {B : A → Type ℓ}
  → (∀ x → is-prop (B x))
  → {x y : Σ _ B}
  → (x .fst ≡ y .fst) ≃ (x ≡ y)
Σ-prop-path≃ bp = Σ-prop-path bp , Σ-prop-path-is-equiv bp
```

<!--
```agda
Σ-prop-square
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  → {w x y z : Σ _ B}
  → (∀ x → is-prop (B x))
  → {p : x ≡ w} {q : x ≡ y} {s : w ≡ z} {r : y ≡ z}
  → Square (ap fst p) (ap fst q) (ap fst s) (ap fst r)
  → Square p q s r
Σ-prop-square Bprop sq i j .fst = sq i j
Σ-prop-square Bprop {p} {q} {s} {r} sq i j .snd =
  is-prop→squarep (λ i j → Bprop (sq i j))
    (ap snd p) (ap snd q) (ap snd s) (ap snd r) i j

Σ-set-square
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  → {w x y z : Σ _ B}
  → (∀ x → is-set (B x))
  → {p : x ≡ w} {q : x ≡ y} {s : w ≡ z} {r : y ≡ z}
  → Square (ap fst p) (ap fst q) (ap fst s) (ap fst r)
  → Square p q s r
Σ-set-square Bset sq i j .fst = sq i j
Σ-set-square Bset {p} {q} {s} {r} sq i j .snd =
  is-set→squarep (λ i j → Bset (sq i j))
    (ap snd p) (ap snd q) (ap snd s) (ap snd r) i j
```
-->

## Dependent sums of contractibles

If `B` is a family of contractible types, then `Σ B ≃ A`:

```agda
Σ-contract : {B : A → Type ℓ} → (∀ x → is-contr (B x)) → Σ _ B ≃ A
Σ-contract bcontr = Iso→Equiv the-iso where
  the-iso : Iso _ _
  the-iso .fst (a , b) = a
  the-iso .snd .is-iso.from x = x , bcontr _ .centre
  the-iso .snd .is-iso.rinv x = refl
  the-iso .snd .is-iso.linv (a , b) i = a , bcontr a .paths b i
```

<!--
```agda
Σ-map
  : (f : A → A')
  → ({x : A} → P x → Q (f x)) → Σ _ P → Σ _ Q
Σ-map f g (x , y) = f x , g y

Σ-map₂ : ({x : A} → P x → Q x) → Σ _ P → Σ _ Q
Σ-map₂ f (x , y) = (x , f y)

×-map : (A → A') → (X → X') → A × X → A' × X'
×-map f g (x , y) = (f x , g y)

×-map₁ : (A → A') → A × X → A' × X
×-map₁ f = ×-map f id

×-map₂ : (X → X') → A × X → A × X'
×-map₂ f = ×-map id f
```
-->

<!--
```agda
_,ₚ_ = Σ-pathp
infixr 4 _,ₚ_

Σ-prop-pathp
  : ∀ {ℓ ℓ'} {A : I → Type ℓ} {B : ∀ i → A i → Type ℓ'}
  → (∀ i x → is-prop (B i x))
  → {x : Σ (A i0) (B i0)} {y : Σ (A i1) (B i1)}
  → PathP A (x .fst) (y .fst)
  → PathP (λ i → Σ (A i) (B i)) x y
Σ-prop-pathp bp {x} {y} p i =
  p i , is-prop→pathp (λ i → bp i (p i)) (x .snd) (y .snd) i

Σ-inj-set
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {x y z}
  → is-set A
  → Path (Σ A B) (x , y) (x , z)
  → y ≡ z
Σ-inj-set {B = B} {y = y} {z} aset path =
  subst (λ e → e ≡ z) (ap (λ e → transport (ap B e) y) (aset _ _ _ _) ∙ transport-refl y)
    (from-pathp (ap snd path))

Σ-swap₂
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : A → B → Type ℓ''}
  → (Σ[ x ∈ A ] Σ[ y ∈ B ] (C x y)) ≃ (Σ[ y ∈ B ] Σ[ x ∈ A ] (C x y))
Σ-swap₂ .fst (x , y , f) = y , x , f
Σ-swap₂ .snd .is-eqv y = contr (f .fst) (f .snd) where
  f = strict-fibres _ y
  -- agda can actually infer the inverse here, which is neat

×-swap
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → (A × B) ≃ (B × A)
×-swap .fst (x , y) = y , x
×-swap .snd .is-eqv y = contr (f .fst) (f .snd) where
  f = strict-fibres _ y

Σ-contr-eqv
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  → (c : is-contr A)
  → (Σ A B) ≃ B (c .centre)
Σ-contr-eqv {B = B} c .fst (_ , p) = subst B (sym (c .paths _)) p
Σ-contr-eqv {B = B} c .snd = is-iso→is-equiv λ where
  .is-iso.from x → _ , x
  .is-iso.rinv x → ap (λ e → subst B e x) (is-contr→is-set c _ _ _ _) ∙ transport-refl x
  .is-iso.linv x → Σ-path (c .paths _) (transport⁻transport (ap B (sym (c .paths (x .fst)))) (x .snd))
```
-->

<!--
```agda
module _ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : X → Type ℓ'} {Z : (x : X) → Y x → Type ℓ''} where
  curry : ((p : Σ X Y) → Z (p .fst) (p .snd)) → (x : X) → (y : Y x) → Z x y
  curry f a b = f (a , b)

  uncurry : ((x : X) → (y : Y x) → Z x y) → (p : Σ X Y) → Z (p .fst) (p .snd)
  uncurry f (a , b) = f a b
```
-->
