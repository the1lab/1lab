```
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Type.Sigma where
```

<!--
```
private variable
  ℓ ℓ₁ : Level
  A A' : Type ℓ
  B P Q : A → Type ℓ

open import Agda.Builtin.Sigma renaming (Σ to ∑) public
-- ^ for Agda display
```
-->

# Properties of Σ types

This module contains properties of $\Sigma$ types, not necessarily
organised in any way.

## Groupoid structure

The first thing we prove is that _paths in sigmas are sigmas of paths_.
The type signatures make it clearer:

```agda
Σ-PathP-iso : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
              {x : Σ (B i0)} {y : Σ (B i1)}
            → Iso (Σ[ p ∈ PathP A (x .fst) (y .fst) ]
                    (PathP (λ i → B i (p i)) (x .snd) (y .snd)))
                  (PathP (λ i → Σ (B i)) x y)

Σ-Path-iso : {x y : Σ B}
           → Iso (Σ[ p ∈ x .fst ≡ y .fst ] (subst B p (x .snd) ≡ y .snd))
                 (x ≡ y)
```

The first of these, using a dependent path, is easy to prove directly,
because paths in cubical type theory _automatically_ inherit the
structure of their domain types. The second is a consequence of the
first, using the fact  that `PathPs and paths over a transport are the
same`{.Agda ident=PathP≡Path}.

```agda
fst Σ-PathP-iso (p , q) i = p i , q i
isIso.inv (snd Σ-PathP-iso) p = (λ i → p i .fst) , (λ i → p i .snd)
isIso.rinv (snd Σ-PathP-iso) x = refl
isIso.linv (snd Σ-PathP-iso) x = refl

Σ-Path-iso {B = B} {x} {y} =
  transport (λ i → Iso (Σ[ p ∈ x .fst ≡ y .fst ]
                         (PathP≡Path (λ j → B (p j)) (x .snd) (y .snd) i))
                       (x ≡ y))
            Σ-PathP-iso
```

## Closure under equivalences

Univalence automatically implies that every type former respects
equivalences. However, this theorem is limited to equivalences between
types _in the same universe_. Thus, we provide `Σ-ap-fst`{.Agda},
`Σ-ap-snd`{.Agda}, and `Σ-ap`{.Agda}, which allows one to perturb a
`Σ`{.Agda} by equivalences across levels:

```agda
Σ-ap-snd : ((x : A) → P x ≃ Q x) → Σ P ≃ Σ Q
Σ-ap-fst : (e : A ≃ A') → Σ (B ∘ e .fst) ≃ Σ B

Σ-ap : (e : A ≃ A') → ((x : A) → P x ≃ Q (e .fst x)) → Σ P ≃ Σ Q
Σ-ap e e' = Σ-ap-snd e' ∙e Σ-ap-fst e
```

<details>
<summary> The proofs of these theorems are not very enlightening, but
they are included for completeness. </summary>
```
Σ-ap-snd {A = A} {P = P} {Q = Q} pointwise = Iso→Equiv morp where
  pwise : (x : A) → Iso (P x) (Q x)
  pwise x = _ , isEquiv→isIso (pointwise x .snd)

  morp : Iso (Σ P) (Σ Q)
  fst morp (i , x) = i , pointwise i .fst x
  isIso.inv (snd morp) (i , x) = i , pwise i .snd .isIso.inv x
  isIso.rinv (snd morp) (i , x) = ap₂ _,_ refl (pwise i .snd .isIso.rinv _)
  isIso.linv (snd morp) (i , x) = ap₂ _,_ refl (pwise i .snd .isIso.linv _)

Σ-ap-fst {A = A} {A' = A'} {B = B} e = intro , isEqIntro
 where
  intro : Σ (B ∘ e .fst) → Σ B
  intro (a , b) = e .fst a , b

  isEqIntro : isEquiv intro
  isEqIntro .isEqv x = contr ctr isCtr where
    PB : ∀ {x y} → x ≡ y → B x → B y → Type _
    PB p = PathP (λ i → B (p i))

    open Σ x renaming (fst to a'; snd to b)
    open Σ (e .snd .isEqv a' .isContr.centre) renaming (fst to ctrA; snd to α)

    ctrB : B (e .fst ctrA)
    ctrB = subst B (sym α) b

    ctrP : PB α ctrB b
    ctrP i = coe1→i (λ i → B (α i)) i b

    ctr : fibre intro x
    ctr = (ctrA , ctrB) , Σ-PathP α ctrP

    isCtr : ∀ y → ctr ≡ y
    isCtr ((r , s) , p) = λ i → (a≡r i , b!≡s i) , Σ-PathP (α≡ρ i) (coh i) where
      open Σ (Σ-PathP-iso .snd .isIso.inv p) renaming (fst to ρ; snd to σ)
      open Σ (Σ-PathP-iso .snd .isIso.inv (e .snd .isEqv a' .isContr.paths (r , ρ))) renaming (fst to a≡r; snd to α≡ρ)

      b!≡s : PB (ap (e .fst) a≡r) ctrB s
      b!≡s i = comp (λ k → B (α≡ρ i (~ k))) (λ k → (λ
        { (i = i0) → ctrP (~ k)
        ; (i = i1) → σ (~ k)
        })) b

      coh : PathP (λ i → PB (α≡ρ i) (b!≡s i) b) ctrP σ
      coh i j = fill (λ k → B (α≡ρ i (~ k))) (λ k → (λ
        { (i = i0) → ctrP (~ k)
        ; (i = i1) → σ (~ k)
        })) (inS b) (~ j)

Σ-assoc : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : (x : A) → B x → Type ℓ''}
        → (Σ[ x ∈ A ] Σ[ y ∈ B x ] C x y) ≃ (Σ[ x ∈ Σ B ] (C (x .fst) (x .snd)))
Σ-assoc .fst (x , y , z) = (x , y) , z
Σ-assoc .snd .isEqv y .centre = strict-fibres (λ { ((x , y) , z) → x , y , z}) y .fst
Σ-assoc .snd .isEqv y .paths = strict-fibres (λ { ((x , y) , z) → x , y , z}) y .snd

Σ-Π-distrib : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : (x : A) → B x → Type ℓ''}
            → ((x : A) → Σ[ y ∈ B x ] C x y)
            ≃ (Σ[ f ∈ ((x : A) → B x) ] ((x : A) → C x (f x)))
Σ-Π-distrib .fst f = (λ x → f x .fst) , λ x → f x .snd
Σ-Π-distrib .snd .isEqv y .centre = strict-fibres (λ f x → f .fst x , f .snd x) y .fst
Σ-Π-distrib .snd .isEqv y .paths = strict-fibres (λ f x → f .fst x , f .snd x) y .snd
```
</details>


## Paths in subtypes

When `P` is a family of propositions, it is sound to regard `Σ[ x ∈ A ]
(P x)` as a _subtype_ of `A`. This is because identification in the
subtype is characterised uniquely by identification of the first
projections:

```agda
Σ≡Prop : {B : A → Type ℓ}
       → (∀ x → isProp (B x))
       → {x y : Σ B}
       → (x .fst ≡ y .fst) → x ≡ y
Σ≡Prop bp {x} {y} p i = p i , isProp→PathP (λ i → bp (p i)) (x .snd) (y .snd) i
```

The proof that this is an equivalence uses a cubical argument, but the
gist of it is that since `B` is a family of propositions, it really
doesn't matter where we get our equality of `B`-s from - whether it was
from the input, or from `Σ≡Path`{.Agda}.

```agda
isEquiv-Σ≡Prop
  : {B : A → Type ℓ}
  → (bp : ∀ x → isProp (B x))
  → {x y : Σ B}
  → isEquiv (Σ≡Prop bp {x} {y})
isEquiv-Σ≡Prop bp {x} {y} = isIso→isEquiv is-iso where
  is-iso : isIso _
  is-iso .isIso.inv = ap fst
  is-iso .isIso.linv p = refl
```

The `inverse`{.Agda ident=isIso.inv} is the `action on paths`{.Agda
ident=ap} of the `first projection`{.Agda ident=fst}, which lets us
conclude `x .fst ≡ y .fst` from `x ≡ y`. This is a left inverse to
`Σ≡Prop`{.Agda} on the nose. For the other direction, we have the
aforementioned cubical argument:

```agda
  is-iso .isIso.rinv p i j =
    p j .fst , isProp→PathP (λ k → isHLevelPath 1 (bp (p k .fst))
                                      {x = Σ≡Prop bp {x} {y} (ap fst p) k .snd}
                                      {y = p k .snd})
                            refl refl j i
```

Since `Σ≡Prop`{.Agda} is an equivalence, this implies that its inverse,
`ap fst`{.Agda}, is also an equivalence; This is precisely what it means
for `fst`{.Agda} to be an [embedding].

[embedding]: agda://1Lab.Equiv.Embedding

There is also a convenient packaging of the previous two definitions
into an equivalence:

```agda
Σ≡Prop≃ : {B : A → Type ℓ}
        → (∀ x → isProp (B x))
        → {x y : Σ B}
        → (x .fst ≡ y .fst) ≃ (x ≡ y)
Σ≡Prop≃ bp = Σ≡Prop bp , isEquiv-Σ≡Prop bp

Σ≡Prop-Sq : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} 
          → {w x y z : Σ B} 
          → (∀ x → isProp (B x))
          → {p : x ≡ w} {q : x ≡ y} {s : w ≡ z} {r : y ≡ z}
          → Square (ap fst p) (ap fst q) (ap fst s) (ap fst r)
          → Square p q s r
Σ≡Prop-Sq Bprop sq i j .fst = sq i j
Σ≡Prop-Sq Bprop {p} {q} {s} {r} sq i j .snd = 
  isProp→SquareP (λ i j → Bprop (sq i j)) 
    (ap snd p) (ap snd q) (ap snd s) (ap snd r) i j
```

## Dependent sums of contractibles

If `B` is a family of contractible types, then `Σ B ≃ A`:

```agda
Σ-contract : {B : A → Type ℓ} → (∀ x → isContr (B x)) → Σ B ≃ A
Σ-contract bcontr = Iso→Equiv the-iso where
  the-iso : Iso _ _
  the-iso .fst (a , b) = a
  the-iso .snd .isIso.inv x = x , bcontr _ .centre
  the-iso .snd .isIso.rinv x = refl
  the-iso .snd .isIso.linv (a , b) i = a , bcontr a .paths b i
```

```agda
Σ-map₂ : ({x : A} → P x → Q x) → Σ P → Σ Q
Σ-map₂ f (x , y) = (x , f y)
```
