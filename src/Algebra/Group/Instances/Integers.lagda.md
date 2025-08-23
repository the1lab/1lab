<!--
```agda
open import Algebra.Group.Cat.Base
open import Algebra.Group.Ab
open import Algebra.Group

open import Cat.Functor.Adjoint
open import Cat.Prelude

open import Data.Int.Universal
open import Data.Nat.Order
open import Data.Int hiding (Positive ; <-not-equal)
open import Data.Nat

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

The fundamental example of an [[abelian group]] is the group of
[[**integers**]], $\ZZ$, under addition.

```agda
ℤ-ab : Abelian-group lzero
ℤ-ab = to-ab mk-ℤ where
  open make-abelian-group
  mk-ℤ : make-abelian-group Int
  mk-ℤ .ab-is-set = hlevel 2
  mk-ℤ .mul x y = x +ℤ y
  mk-ℤ .inv x = negℤ x
  mk-ℤ .1g = 0
  mk-ℤ .idl x = +ℤ-zerol x
  mk-ℤ .assoc x y z = +ℤ-assoc x y z
  mk-ℤ .invl x = +ℤ-invl x
  mk-ℤ .comm x y = +ℤ-commutative x y

ℤ : Group lzero
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
    pow-pos : Nat → ⌞ G ⌟
    pow-pos zero    = x
    pow-pos (suc n) = pow-pos n ⋆ x

    pow-neg : Nat → ⌞ G ⌟
    pow-neg zero    = x ⁻¹
    pow-neg (suc n) = pow-neg n ⋆ (x ⁻¹)

    pow : Int → ⌞ G ⌟
    pow posz       = unit
    pow (possuc x) = pow-pos x
    pow (negsuc x) = pow-neg x

    pow-sucr : ∀ a → pow (sucℤ a) ≡ pow a ⋆ x
    pow-sucr posz             = sym idl
    pow-sucr (possuc x)       = refl
    pow-sucr (negsuc zero)    = sym inversel
    pow-sucr (negsuc (suc x)) = sym (cancelr inversel)

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
```

A type-theoretic interjection is necessary: the integers live on the
zeroth universe, so to have an $\ell$-sized group of integers, we
must lift it.

```agda
    pow-hom : Groups.Hom (Lift-group ℓ ℤ) G
    pow-hom .fst (lift i) = pow i
    pow-hom .snd .pres-⋆ (lift a) (lift b) = pow-+ a b
```

This is the unique group homomorphism $\ZZ \to G$ that sends $1$ to $x$.

```agda
    pow-unique : (g : Groups.Hom (Lift-group ℓ ℤ) G) → g · 1 ≡ x → g ≡ pow-hom
    pow-unique g g1≡x = ext λ x → p x ∙ sym (q x) where
      pow' = ℤ.map-out unit ((_⋆ x) , ⋆-equivr x)
      p : ∀ x → g · lift x ≡ pow' x
      p = ℤ.map-out-unique (λ i → g · lift i) (pres-id (g .snd)) λ y →
        g · lift ⌜ sucℤ y ⌝ ≡⟨ ap! (sym (+ℤ-oner y)) ⟩
        g · lift (y +ℤ 1)   ≡⟨ g .snd .pres-⋆ (lift y) 1 ⟩
        g · lift y ⋆ g · 1  ≡⟨ ap (g · lift y ⋆_) g1≡x ⟩
        g · lift y ⋆ x      ∎

      q : ∀ x → pow x ≡ pow' x
      q = ℤ.map-out-unique pow refl pow-sucr

  open pow public

  pow-unique₂ : (g h : Groups.Hom (Lift-group ℓ ℤ) G) → g · 1 ≡ h · 1 → g ≡ h
  pow-unique₂ g h p = pow-unique (g · 1) g refl ∙ sym (pow-unique (g · 1) h (sym p))
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

  pow-1 x = refl

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
ℤ-free .Free-object.free = Lift-group lzero ℤ
ℤ-free .Free-object.unit _ = 1
ℤ-free .Free-object.fold {G} x = pow-hom G (x _)
ℤ-free .Free-object.commute {G} {x} = ext λ _ → pow-1 G (x _)
ℤ-free .Free-object.unique {G} {x} g comm =
  pow-unique G (x _) g (unext comm _)
```

<!--
```agda
instance
  Extensional-ℤ-Hom
    : ∀ {ℓ ℓr} {G : Group ℓ} ⦃ _ : Extensional ⌞ G ⌟ ℓr ⦄
    → Extensional (Groups.Hom (Lift-group ℓ ℤ) G) ℓr
  Extensional-ℤ-Hom ⦃ e ⦄ = injection→extensional! {f = λ h → h · 1} (pow-unique₂ _ _ _) e

  Extensional-Ab-ℤ-Hom
    : ∀ {ℓ ℓr} {G : ⌞ Ab ℓ ⌟} ⦃ _ : Extensional ⌞ G ⌟ ℓr ⦄
    → Extensional (Ab.Hom (Lift-ab ℓ ℤ-ab) G) ℓr
  Extensional-Ab-ℤ-Hom {ℓ = ℓ} {G = G} ⦃ ef ⦄ = injection→extensional! {f = λ h → h · 1} inj ef where
    inj : {x y : Ab.Hom (Lift-ab ℓ ℤ-ab) G} → x · 1 ≡ y · 1 → x ≡ y
    inj {x} {y} p = Structured-hom-path _ (ap fst (pow-unique₂ G' x' y' p)) where
      G' : Group ℓ
      G' .fst = G .fst
      G' .snd = Abelian→Group-on (G .snd)

      x' y' : Groups.Hom (Lift-group ℓ ℤ) G'
      x' .fst = apply x
      x' .snd = record { pres-⋆ = x .snd .is-group-hom.pres-⋆ }

      y' .fst = apply y
      y' .snd = record { pres-⋆ = y .snd .is-group-hom.pres-⋆ }

  {-# OVERLAPPING Extensional-ℤ-Hom Extensional-Ab-ℤ-Hom #-}

```
-->

::: note
While the notation $x^n$ for `pow`{.Agda} makes sense in
multiplicative notation, we would instead write $n \cdot x$ in additive
notation. In fact, we can show that $n \cdot x$ coincides with the
multiplication $n \times x$ in the group of integers itself.

```agda
pow-ℤ : ∀ a b → pow ℤ a b ≡ a *ℤ b
pow-ℤ a = ℤ.induction (sym (*ℤ-zeror a)) λ b →
  pow ℤ a b        ≡ a *ℤ b      ≃⟨ ap (_+ℤ a) , equiv→cancellable (Group-on.⋆-equivr (ℤ .snd) a) ⟩
  pow ℤ a b +ℤ a   ≡ a *ℤ b +ℤ a ≃⟨ ∙-pre-equiv (pow-sucr ℤ a b) ⟩
  pow ℤ a (sucℤ b) ≡ a *ℤ b +ℤ a ≃⟨ ∙-post-equiv (sym (*ℤ-sucr a b)) ⟩
  pow ℤ a (sucℤ b) ≡ a *ℤ sucℤ b ≃∎
```
:::

# Order of an element {defines="order-of-an-element"}

<!--
```agda
module _ {ℓ} (G : Group ℓ) where
  open Group-on (G .snd)
```
-->

We define the **order** of an element $x : G$ of a group $G$ as the
minimal *positive*^[Without this requirement, every element would
trivially have order $0$!] integer $n$ such that $x^n = 1$, if it exists.

In particular, if $x^n = 1$, then we have that the order of $x$ divides
$n$. We define this notion first in the code, then use it to define the
order of $x$.

```agda
  order-divides : ⌞ G ⌟ → Nat → Type ℓ
  order-divides x n = pow G x (pos n) ≡ unit

  has-finite-order : ⌞ G ⌟ → Type ℓ
  has-finite-order x = minimal-solution λ n →
    Positive n × order-divides x n

  order : (x : ⌞ G ⌟) → has-finite-order x → Nat
  order x (n , _) = n
```

::: {.definition #torsion}
An element $x$ with finite order is also called a **torsion element**.
A group all of whose elements are torsion is called a **torsion group**,
while a group whose only torsion element is the unit is called
**torsion-free**.
:::

```agda
  is-torsion-group : Type ℓ
  is-torsion-group = ∀ g → has-finite-order g

  is-torsion-free : Type ℓ
  is-torsion-free = ∀ g → has-finite-order g → g ≡ unit
```

::: note
Our definition of torsion groups requires being able to compute
the order of every element of the group. There is a weaker definition
that only requires every element $x$ to have *some* $n$ such that
$x^n = 1$; the two definitions are equivalent if the group is
[[discrete]], since [[$\NN$ is well-ordered|N is well-ordered]].
:::

We quickly note that $\ZZ$ is torsion-free, since multiplication by
a nonzero integer is injective.

```agda
ℤ-torsion-free : is-torsion-free ℤ
ℤ-torsion-free n (k , (k>0 , nk≡0) , _) = *ℤ-injectiver (pos k) n 0
  (λ p → <-not-equal k>0 (pos-injective (sym p)))
  (sym (pow-ℤ n (pos k)) ∙ nk≡0)
```
