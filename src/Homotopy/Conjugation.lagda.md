<!--
```agda
open import 1Lab.Prelude
```
-->

```agda
module Homotopy.Conjugation where
```

# Conjugation of paths {defines="conjugation-of-paths conjugation"}

<!--
```agda
private variable
  ℓ : Level
  A : Type ℓ
  x y z : A
  p q r : x ≡ y

open is-iso
```
-->

In any type $G$ for which we know two points $x, y : G$, the existence
of any identification $p : x \equiv y$ induces an equivalence between
the loop spaces $x \equiv x$ and $y \equiv y$, given by transport in the
usual way. However, since we know ahead-of-time what transport in a type
of paths computes to, we can take a short-cut and define the equivalence
directly: it is given by **conjugation** with $p$.

```agda
opaque
  conj : ∀ {ℓ} {A : Type ℓ} {x y : A} → y ≡ x → y ≡ y → x ≡ x
  conj p q = sym p ·· q ·· p
```

<!--
```agda
opaque
  unfolding conj
```
-->

```agda
  conj-defn : (p : y ≡ x) (q : y ≡ y) → conj p q ≡ sym p ∙ q ∙ p
  conj-defn p q = double-composite (sym p) q p

  conj-defn' : (p : y ≡ x) (q : y ≡ y) → conj p q ≡ subst (λ x → x ≡ x) p q
  conj-defn' p q = conj-defn p q ∙ sym (subst-path-both q p)
```

<!--
```agda
opaque
```
-->

```agda
  conj-refl : (l : x ≡ x) → conj refl l ≡ l
  conj-refl l = conj-defn _ _ ·· ∙-idl _ ·· ∙-idr _

  conj-∙ : (p : x ≡ y) (q : y ≡ z) (r : x ≡ x)
            → conj q (conj p r) ≡ conj (p ∙ q) r
  conj-∙ p q r = transport
    (λ i → conj-defn' q (conj-defn' p r (~ i)) (~ i) ≡ conj-defn' (p ∙ q) r (~ i))
    (sym (subst-∙ (λ x → x ≡ x) p q r))
```

```agda
  conj-of-refl : (p : y ≡ x) → conj p refl ≡ refl
  conj-of-refl p = conj-defn _ _ ·· ap (sym p ∙_) (∙-idl p) ·· ∙-invl p

  conj-of-∙ : (p : y ≡ x) (q r : y ≡ y) → conj p (q ∙ r) ≡ conj p q ∙ conj p r
  conj-of-∙ = J (λ x p → ∀ q r → conj p (q ∙ r) ≡ conj p q ∙ conj p r) λ q r →
    conj-refl (q ∙ r) ∙ ap₂ _∙_ (sym (conj-refl q)) (sym (conj-refl r))
```

```agda
opaque
  unfolding conj

  ap-conj
    : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {x y : A}
    → (f : A → B) (p : y ≡ x) (q : y ≡ y)
    → ap f (conj p q) ≡ conj (ap f p) (ap f q)
  ap-conj f p q = ap-·· f _ _ _
```

```agda
opaque
  conj⁻conj : conj (sym p) (conj p q) ≡ q
  conj⁻conj {p = p} {q = q} =
       ap (conj _) (conj-defn' _ _)
    ·· conj-defn' _ _
    ·· transport⁻transport (λ i → p i ≡ p i) q
```

```agda
opaque
  pathp→conj
    : {p : y ≡ x} {q₁ : y ≡ y} {q₂ : x ≡ x}
    → PathP (λ i → p i ≡ p i) q₁ q₂ → conj p q₁ ≡ q₂
  pathp→conj p = conj-defn' _ _ ∙ from-pathp p
```

```agda
opaque
  conj-commutative : {p q : x ≡ x} → q ∙ p ≡ p ∙ q → conj p q ≡ q
  conj-commutative α = conj-defn _ _ ·· ap₂ _∙_ refl α ·· ∙-cancell _ _
```

```agda
conj-is-iso : (p : y ≡ x) → is-iso (conj p)
conj-is-iso p .inv  q = conj (sym p) q
conj-is-iso p .rinv q = conj⁻conj
conj-is-iso p .linv q = conj⁻conj
```

<!--
```agda
opaque
  conj-is-equiv : (p : y ≡ x) → is-equiv (conj p)
  conj-is-equiv p = is-iso→is-equiv (conj-is-iso p)

module conj {ℓ} {A : Type ℓ} {x y : A} (p : y ≡ x) = Equiv (conj p , conj-is-equiv p)
```
-->
