<!--
```agda
open import Cat.Displayed.Univalence.Thin
open import Cat.Instances.OFE.Complete
open import Cat.Displayed.Total
open import Cat.Instances.OFE
open import Cat.Prelude
```
-->

```agda
module Cat.Instances.OFE.Later where
```

# The "Later" OFE

Given a [OFE] $A$, we define an OFE $\later A$, the **later** modality
of systems of guarded recursion. The idea is that $\later A$ is like
$A$, but we have to wait a bit to think about it: at level zero, $\later
A$ is an indiscrete blob, but at positive time steps, it looks just like
$A$.

The $\later A$ construction extends to an endofunctor of OFE, equipped
with a natural transformation $\rm{next} : A \to \later A$, expressing
that if we have something now, we can very well stop thinking about it
for a step. This natural transformation actually has a universal
property, within the category of OFEs: Non-expansive maps $\later A \to
B$ are equivalent to contractive maps $A \to B$.

[OFE]: Cat.Instances.OFE.html
[complete OFE]: Cat.Instances.OFE.Complete.html
[bfpt]: Cat.Instances.OFE.Complete.html#banachs-fixed-point-theorem

<!--
```agda
open OFE-Notation

module _ {ℓ ℓ'} {A : Type ℓ} (P : OFE-on ℓ' A) where
  private
    instance _ = P
    module P = OFE-on P
```
-->

To emphasize that the distinction between $A$ and $\later A$ is entirely
in skipping a step, we have formatted the construction below so the
cases are split between time zero and positive time.

```agda
  Later : OFE-on ℓ' A
  Later .within zero x y    = Lift ℓ' ⊤
  Later .within (suc n) x y = x ≈[ n ] y

  -- Trivial!
  Later .has-is-ofe .has-is-prop zero = λ _ _ _ _ _ → _
  Later .has-is-ofe .≈-trans     zero = _
  Later .has-is-ofe .≈-refl      zero = _
  Later .has-is-ofe .≈-sym       zero = _
  Later .has-is-ofe .step        zero = _

  -- Just like A!
  Later .has-is-ofe .has-is-prop (suc n) = P.has-is-prop n
  Later .has-is-ofe .≈-trans     (suc n) = P.≈-trans     n
  Later .has-is-ofe .≈-refl      (suc n) = P.≈-refl      n
  Later .has-is-ofe .≈-sym       (suc n) = P.≈-sym       n
  Later .has-is-ofe .step        (suc n) = P.step        n

  Later .has-is-ofe .bounded x y = _
  Later .has-is-ofe .limit x y a = P.limit x y λ n → a (suc n)
```

```agda
▶ : ∀ {ℓ ℓ'} → OFE ℓ ℓ' → OFE ℓ ℓ'
▶ (A , O) = from-ofe-on (Later O)

to-later : ∀ {ℓ ℓ'} (A : OFE ℓ ℓ') → OFEs.Hom A (▶ A)
to-later A .hom x = x
to-later A .preserves .pres-≈ {n = zero} α  = lift tt
to-later A .preserves .pres-≈ {n = suc n} α = A .snd .OFE-on.step n _ _ α
```

<!--
```
module
  _ {ℓa ℓa' ℓb ℓb'} {A : Type ℓa} {B : Type ℓb}
    (P : OFE-on ℓa' A) (Q : OFE-on ℓb' B)
  where

  private
    instance
      _ = P
      _ = Q
    module P = OFE-on P
    module Q = OFE-on Q
```
-->

The universal property promised, that $\later P$ represents the
contractive maps with domain $P$, is a short exercise in shuffling
indices:

```agda
  later-contractive
    : (f : A → B)
    → is-non-expansive f (Later P) Q ≃ is-contractive f P Q
  later-contractive f = prop-ext! {A = is-non-expansive _ _ _} {B = is-contractive _ _ _}
    (λ { r .contract {n = n} α → r .pres-≈ {n = suc n} α })
    (λ { r .pres-≈ {n = zero} α  → Q.bounded _ _
       ; r .pres-≈ {n = suc n} α → r .contract α
       })
```

<!--
```agda
module _ {ℓa ℓa'} {A : Type ℓa} (P : OFE-on ℓa' A) where
  private
    instance _ = P
    module P = OFE-on P
```
-->

We can put this together to define something akin to **Löb induction**:
if $A$ is an inhabited, [complete OFE], Banach's fixed point theorem
implies that non-expansive functions $\later P \to P$ have fixed points.

```agda
  löb : ∥ A ∥ → is-cofe P → (f : Later P →ⁿᵉ P) → Σ A λ x → f .map x ≡ x
  löb pt lim f = banach P lim pt record {
    contract = λ n p → f .pres-≈ (suc n) p }
```
