<!--
```agda
open import Algebra.Group.Cat.Base
open import Algebra.Group.Ab
open import Algebra.Prelude
open import Algebra.Group

open import Cat.Functor.Adjoint

open import Data.Int.Universal
open import Data.Int

open is-group-hom
```
-->

```agda
module Algebra.Group.Instances.Integers where
```

<!--
```agda
private module ℤ = Integers Int-integers
```
-->

# The group of integers {defines="integer-group group-of-integers"}

The fundamental example of an [[abelian group]] is the group of [[**integers**]], $\ZZ$, under
addition. A type-theoretic interjection is necessary: the integers live
on the zeroth universe, so to have an $\ell$-sized group of integers, we
must lift it.

```agda
ℤ-ab : ∀ {ℓ} → Abelian-group ℓ
ℤ-ab = to-ab mk-ℤ where
  open make-abelian-group
  mk-ℤ : make-abelian-group (Lift _ Int)
  mk-ℤ .ab-is-set = hlevel 2
  mk-ℤ .mul (lift x) (lift y) = lift (x +ℤ y)
  mk-ℤ .inv (lift x) = lift (negℤ x)
  mk-ℤ .1g = 0
  mk-ℤ .idl (lift x) = ap lift (+ℤ-zerol x)
  mk-ℤ .assoc (lift x) (lift y) (lift z) = ap lift (+ℤ-assoc x y z)
  mk-ℤ .invl (lift x) = ap lift (+ℤ-invl x)
  mk-ℤ .comm (lift x) (lift y) = ap lift (+ℤ-commutative x y)

ℤ : ∀ {ℓ} → Group ℓ
ℤ = Abelian→Group ℤ-ab
```

We show that $\ZZ$ is the [[free group]] on one generator, i.e. the
[[free object]] on $\top$ relative to the forgetful functor from groups
to sets, `Grp↪Sets`{.Agda}.

We start by defining the [[group homomorphism]] $\ZZ \to G$ that sends
$n$ to $x^n$ (or, in additive notation, $n \cdot x$), where $G$ is a group
and $x$ is an element of $G$, using the [[universal property of the integers]].

<!--
```agda
module _ {ℓ} (G : Group ℓ) where
  open Group-on (G .snd)
```
-->

```agda
  module pow (x : ⌞ G ⌟) where
    pow : Int → ⌞ G ⌟
    pow = ℤ.map-out unit ((_⋆ x) , ⋆-equivr x)

    pow-sucr : ∀ a → pow (sucℤ a) ≡ pow a ⋆ x
    pow-sucr = ℤ.map-out-rotate _ _

    pow-+ : ∀ a b → pow (a +ℤ b) ≡ pow a ⋆ pow b
    pow-+ a = ℤ.induction
      (ap pow (+ℤ-zeror a) ∙ sym idr)
      λ b →
        pow (a +ℤ b)        ≡ pow a ⋆ pow b        ≃⟨ ap (_⋆ x) , equiv→cancellable (⋆-equivr x) ⟩
        pow (a +ℤ b) ⋆ x    ≡ (pow a ⋆ pow b) ⋆ x  ≃⟨ ∙-post-equiv (sym associative) ⟩
        pow (a +ℤ b) ⋆ x    ≡ pow a ⋆ pow b ⋆ x    ≃⟨ ∙-post-equiv (ap (pow a ⋆_) (sym (pow-sucr b))) ⟩
        pow (a +ℤ b) ⋆ x    ≡ pow a ⋆ pow (sucℤ b) ≃⟨ ∙-pre-equiv (pow-sucr (a +ℤ b)) ⟩
        pow (sucℤ (a +ℤ b)) ≡ pow a ⋆ pow (sucℤ b) ≃⟨ ∙-pre-equiv (ap pow (+ℤ-sucr a b)) ⟩
        pow (a +ℤ sucℤ b)   ≡ pow a ⋆ pow (sucℤ b) ≃∎

    pow-hom : Groups.Hom ℤ G
    pow-hom .hom (lift i) = pow i
    pow-hom .preserves .pres-⋆ (lift a) (lift b) = pow-+ a b
```

This is the unique group homomorphism $\ZZ \to G$ that sends $1$ to $x$.

```agda
    pow-unique : (g : Groups.Hom ℤ G) → g # 1 ≡ x → g ≡ pow-hom
    pow-unique g g1≡x = ext $ ℤ.map-out-unique (λ i → g # lift i)
      (pres-id (g .preserves))
      λ y →
        g # lift ⌜ sucℤ y ⌝ ≡⟨ ap! (sym (+ℤ-oner y)) ⟩
        g # lift (y +ℤ 1)   ≡⟨ g .preserves .pres-⋆ (lift y) 1 ⟩
        g # lift y ⋆ g # 1  ≡⟨ ap (g # lift y ⋆_) g1≡x ⟩
        g # lift y ⋆ x      ∎

  open pow public
```

<details>
<summary>
We prove some other useful basic properties of exponentiation.
^[Pedantically, these properties say that `pow`{.Agda} is the unique
*near-ring* homomorphism from $\ZZ$, the [[initial near-ring|initial
ring]], to the near-ring of (pointed) endofunctions of $G$, a generalisation
of [[endomorphism rings]] to non-abelian groups.]

```agda
  pow-sucl : ∀ x a → pow x (sucℤ a) ≡ x ⋆ pow x a
  pow-0 : ∀ x → pow x 0 ≡ unit
  pow-1 : ∀ x → pow x 1 ≡ x
  pow-* : ∀ x a b → pow x (a *ℤ b) ≡ pow (pow x a) b
  pow-unit : ∀ n → pow unit n ≡ unit
  pow-inverse : ∀ x n → pow (x ⁻¹) n ≡ pow x n ⁻¹
```
</summary>

```agda
  pow-sucl x a =
    pow x (sucℤ a)    ≡˘⟨ ap (pow x) (+ℤ-onel a) ⟩
    pow x (1 +ℤ a)    ≡⟨ pow-+ x 1 a ⟩
    pow x 1 ⋆ pow x a ≡⟨ ap (_⋆ pow x a) (pow-1 x) ⟩
    x ⋆ pow x a       ∎

  pow-0 x = refl

  pow-1 x = idl

  pow-* x a = ℤ.induction (ap (pow x) (*ℤ-zeror a)) λ b →
    pow x (a *ℤ b)           ≡ pow (pow x a) b           ≃⟨ _ , equiv→cancellable (⋆-equivr _) ⟩
    pow x (a *ℤ b) ⋆ pow x a ≡ pow (pow x a) b ⋆ pow x a ≃⟨ ∙-pre-equiv (pow-+ x (a *ℤ b) a) ⟩
    pow x (a *ℤ b +ℤ a)      ≡ pow (pow x a) b ⋆ pow x a ≃⟨ ∙-pre-equiv (ap (pow x) (*ℤ-sucr a b)) ⟩
    pow x (a *ℤ sucℤ b)      ≡ pow (pow x a) b ⋆ pow x a ≃⟨ ∙-post-equiv (sym (pow-sucr (pow x a) b)) ⟩
    pow x (a *ℤ sucℤ b)      ≡ pow (pow x a) (sucℤ b)    ≃∎

  pow-unit = ℤ.induction refl (λ x → ∙-pre-equiv (pow-sucr unit x ∙ idr))

  pow-inverse x = ℤ.induction (sym inv-unit) λ n →
    pow (x ⁻¹) n        ≡ pow x n ⁻¹        ≃⟨ _ , equiv→cancellable (⋆-equivr (x ⁻¹)) ⟩
    pow (x ⁻¹) n ⋆ x ⁻¹ ≡ pow x n ⁻¹ ⋆ x ⁻¹ ≃⟨ ∙-pre-equiv (pow-sucr (x ⁻¹) n) ⟩
    pow (x ⁻¹) (sucℤ n) ≡ pow x n ⁻¹ ⋆ x ⁻¹ ≃⟨ ∙-post-equiv (sym inv-comm) ⟩
    pow (x ⁻¹) (sucℤ n) ≡ (x ⋆ pow x n) ⁻¹  ≃⟨ ∙-post-equiv (ap _⁻¹ (sym (pow-sucl x n))) ⟩
    pow (x ⁻¹) (sucℤ n) ≡ pow x (sucℤ n) ⁻¹ ≃∎
```
</details>

Finally, the properties above imply that $\ZZ$ is the free group on
one generator.

```agda
ℤ-free : Free-object Grp↪Sets (el! ⊤)
ℤ-free .Free-object.free = ℤ
ℤ-free .Free-object.unit _ = 1
ℤ-free .Free-object.fold {G} x = pow-hom G (x _)
ℤ-free .Free-object.commute {G} {x} = ext λ _ → pow-1 G (x _)
ℤ-free .Free-object.unique {G} {x} g comm =
  pow-unique G (x _) g (unext comm _)
```
