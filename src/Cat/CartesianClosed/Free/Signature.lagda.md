<!--
```agda
open import 1Lab.Prelude
```
-->

```agda
module Cat.CartesianClosed.Free.Signature where
```

# Signatures for free CCCs

<!--
```agda
module types {ℓ} (T : Type ℓ) where
  infixr 22 _`⇒_
  infixr 20 _`×_
  infix 25 `_
```
-->

:::{.definition #simple-type}
The type of **simple types** $\operatorname{Ty}(T)$ over a base type $T$
is the inductive type with a constructor for base types, a nullary
constructor for the unit type, and binary constructors for products and
functions.

```agda
  data Ty : Type ℓ where
    `⊤        : Ty
    `_        : T → Ty
    _`×_ _`⇒_ : Ty → Ty → Ty
```
:::

<details>
<summary>We'll need an 'observational' equality on types, both to show
that the types of a given $\lambda$-signature are a [[set]], and later
to show this also of further constructions on syntax.</summary>

```agda
  module code ⦃ _ : H-Level T 2 ⦄ where
    same-ty : Ty → Ty → Prop ℓ
    same-ty `⊤ `⊤ = el! (Lift _ ⊤)
    same-ty `⊤ _  = el! (Lift _ ⊥)

    same-ty (` x) (` y) = el! (x ≡ y)
    same-ty (` x) _     = el! (Lift _ ⊥)

    same-ty (a `× x) (b `× y) = el! (⌞ same-ty a b ⌟ × ⌞ same-ty x y ⌟)
    same-ty (a `× x) _        = el! (Lift _ ⊥)

    same-ty (a `⇒ x) (b `⇒ y) = el! (⌞ same-ty a b ⌟ × ⌞ same-ty x y ⌟)
    same-ty (a `⇒ x) _        = el! (Lift _ ⊥)

    refl-same-ty : ∀ x → ⌞ same-ty x x ⌟
    refl-same-ty `⊤       = lift tt
    refl-same-ty (` x)    = refl
    refl-same-ty (a `× b) = refl-same-ty a , refl-same-ty b
    refl-same-ty (a `⇒ b) = refl-same-ty a , refl-same-ty b

    from-same-ty : ∀ x y → ⌞ same-ty x y ⌟ → x ≡ y
    from-same-ty `⊤       `⊤       p = refl
    from-same-ty (` x)    (` y)    p = ap `_ p
    from-same-ty (a `× x) (b `× y) p = ap₂ _`×_ (from-same-ty a b (p .fst)) (from-same-ty x y (p .snd))
    from-same-ty (a `⇒ x) (b `⇒ y) p = ap₂ _`⇒_ (from-same-ty a b (p .fst)) (from-same-ty x y (p .snd))

    instance
      H-Level-Ty : ∀ {n} → H-Level Ty (2 + n)
      H-Level-Ty = basic-instance 2 $ set-identity-system→hlevel
        (λ x y → ⌞ same-ty x y ⌟) refl-same-ty (λ x y → hlevel 1) from-same-ty
```

</details>

<!--
```agda
open types using (module Ty ; `_ ; _`×_ ; _`⇒_ ; `⊤) public
```
-->

::: {.definition #lambda-signature}
A **$\lambda$-signature** consists of a [[set]] $T$ of **base types**,
and, for each [[simple type]] $\tau : \operatorname{Ty}(T)$ and base
type $b$, a set of **operations** $H(\tau, b)$.
:::

```agda
record λ-Signature ℓ : Type (lsuc ℓ) where
  field
    Ob         : Type ℓ
    Ob-is-set  : is-set Ob
    Hom        : types.Ty Ob → Ob → Type ℓ
    Hom-is-set : ∀ {τ σ} → is-set (Hom τ σ)
```

<!--
```agda
  -- This module is meant to always be opened instantiated, so we don't
  -- provide these as instances.

  instance
    H-Level-Ob : ∀ {n} → H-Level Ob (2 + n)
    H-Level-Ob = basic-instance 2 Ob-is-set

    H-Level-Hom : ∀ {τ σ n} → H-Level (Hom τ σ) (2 + n)
    H-Level-Hom = basic-instance 2 Hom-is-set

  open types Ob using (Ty) public
  open types.code Ob ⦃ auto ⦄ public
```
-->
