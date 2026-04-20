<!--
```agda
open import 1Lab.HLevel.Closure

open import Cat.Functor.Naturality
open import Cat.Instances.Product
open import Cat.Groupoid
open import Cat.Morphism
open import Cat.Prelude

open import Data.Id.Properties
open import Data.Id.Base
open import Data.Dec

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Discrete where
```

<!--
```agda
private variable
  ℓ ℓ' : Level
  X : Type ℓ
  C : Precategory ℓ ℓ'

open Precategory
open Functor
open _=>_
```
-->

# Discrete categories {defines="discrete-category"}

Given a [[groupoid]] $A$, we can see $A$ as a [[category]] with
space of objects $A$ and path types $x \equiv y$ as $\hom$-sets $x \to
y$. When $A$ is a [[set]], we call this the **discrete category** on $A$.
For technical reasons, we prefer to define this category using the
[[inductive identity]] type instead of the path type.

```agda
Disc : (A : Type ℓ) → is-groupoid A → Precategory ℓ ℓ
Disc A A-grpd .Ob          = A
Disc A A-grpd .Hom         = _≡ᵢ_
Disc A A-grpd .Hom-set     = ≡ᵢ-is-hlevel' {n = 2} A-grpd
Disc A A-grpd .id          = reflᵢ
Disc A A-grpd ._∘_ p q     = q ∙ᵢ p
Disc A A-grpd .idr _       = refl
Disc A A-grpd .idl _       = ∙ᵢ-idr _
Disc A A-grpd .assoc p q r = sym (∙ᵢ-assoc r q p)

Disc' : Set ℓ → Precategory ℓ ℓ
Disc' A = Disc ∣ A ∣ h module Disc' where abstract
  h : is-groupoid ∣ A ∣
  h = is-hlevel-suc 2 (A .is-tr)
```

By construction, this is a [[univalent|univalent category]]
[[groupoid|pregroupoid]]:

```agda
Disc-is-category : ∀ {A : Type ℓ} {A-grpd} → is-category (Disc A A-grpd)
Disc-is-category .to-path is              = Id≃path.to (is .to)
Disc-is-category .to-path-over {a = a} is = ≅-pathp _ _ _ $
  Jᵢ (λ _ p → PathP (λ i → a ≡ᵢ Id≃path.to p i) reflᵢ p) refl (is .to)

Disc-is-groupoid : ∀ {A : Type ℓ} {A-grpd} → is-pregroupoid (Disc A A-grpd)
Disc-is-groupoid p = make-invertible _ (symᵢ p) (∙ᵢ-invl p) (∙ᵢ-invr p)
```

<!--
```agda
Codisc' : ∀ {ℓ'} → Type ℓ → Precategory ℓ ℓ'
Codisc' x .Ob = x
Codisc' x .Hom _ _ = Lift _ ⊤
Codisc' x .Hom-set _ _ = is-prop→is-set (λ _ _ i → lift tt)
Codisc' x .id = lift tt
Codisc' x ._∘_ _ _ = lift tt
Codisc' x .idr _ = refl
Codisc' x .idl _ = refl
Codisc' x .assoc _ _ _ = refl
```
-->

## Diagrams in Disc(X)

Because the morphisms in a discrete category are identifications, and
functions respect equality, any function on objects out of a discrete
category induces a functor.

```agda
Disc-diagram
  : {X : Type ℓ} (iss : is-groupoid X)
  → (X → Ob C)
  → Functor (Disc X iss) C
Disc-diagram {C = C} {X = X} _ f = F where
  module C = Precategory C

  go : ∀ {x y : X} → x ≡ᵢ y → C.Hom (f x) (f y)
  go = Jᵢ (λ y _ → C.Hom (f _) (f y)) C.id

  F : Functor _ _
  F .F₀      = f
  F .F₁      = go
  F .F-id    = refl
  F .F-∘ f g =
    Jᵢ (λ y g → ∀ f → go (g ∙ᵢ f) ≡ go f C.∘ go g) (λ _ → sym (C.idr _)) g f
```

<!--
```agda
Disc-diagram!
  : ∀ ⦃ iss : H-Level {ℓ} X 3 ⦄
  → (X → Ob C)
  → Functor (Disc X (hlevel 3)) C
Disc-diagram! = Disc-diagram (hlevel 3)
```
-->

As a corollary, we can lift any function between underlying types to a
functor between discrete categories.

```agda
lift-disc : {A : Set ℓ} {B : Set ℓ'} → (∣ A ∣ → ∣ B ∣) → Functor (Disc' A) (Disc' B)
lift-disc {A = A} f = Disc-diagram (Disc'.h A) f
```

<!--
```agda
Disc-into
  : ∀ {ℓ} (X : Set ℓ)
  → (F : C .Ob → ∣ X ∣)
  → (F₁ : ∀ {x y} → C .Hom x y → F x ≡ᵢ F y)
  → Functor C (Disc' X)
Disc-into X F F₁ .F₀      = F
Disc-into X F F₁ .F₁      = F₁
Disc-into X F F₁ .F-id    = ≡ᵢ-is-hlevel' {n = 1} (X .is-tr) _ _ _ _
Disc-into X F F₁ .F-∘ _ _ = ≡ᵢ-is-hlevel' {n = 1} (X .is-tr) _ _ _ _

Disc-natural
  : ∀ {X : Set ℓ}
  → {F G : Functor (Disc' X) C}
  → (∀ x → C .Hom (F .F₀ x) (G .F₀ x))
  → F => G
Disc-natural fam .η = fam
Disc-natural {C = C} {F = F} {G = G} fam .is-natural x y =
  Jᵢ (λ y p → fam y C.∘ F .F₁ p ≡ G .F₁ p C.∘ fam x)
    (C.elimr (F .F-id) ∙ C.introl (G .F-id))
  where module C = Cat.Reasoning C

Disc-natural₂
  : ∀ {X : Type ℓ} {Y : Type ℓ'}
  → {issx : is-groupoid X} {issy : is-groupoid Y}
  → {F G : Functor (Disc X issx ×ᶜ Disc Y issy) C}
  → ((x : X × Y) → C .Hom (F .F₀ x) (G .F₀ x))
  → F => G
Disc-natural₂ fam .η = fam
Disc-natural₂ {C = C} {F = F} {G = G} fam .is-natural x y (p , q) =
  Jᵢ (λ y₁ p → ∀ y₂ q → fam (y₁ , y₂) C.∘ F .F₁ (p , q) ≡ G .F₁ (p , q) C.∘ fam x)
    (λ y₂ → Jᵢ
      (λ y₂ q → fam (x .fst , y₂) C.∘ F .F₁ (reflᵢ , q) ≡ G .F₁ (reflᵢ , q) C.∘ fam x)
      (C.elimr (F .F-id) ∙ C.introl (G .F-id)))
    p (y .snd) q
  where module C = Cat.Reasoning C

open _≅_
open Inverses
Disc-natural-iso : ∀ {X : Set ℓ}
  → {F G : Functor (Disc' X) C}
  → (∀ x → Isomorphism C (F .F₀ x) (G .F₀ x))
  → F ≅ⁿ G
Disc-natural-iso isos .to       = Disc-natural λ x → isos x .to
Disc-natural-iso isos .from     = Disc-natural λ x → isos x .from
Disc-natural-iso isos .inverses =
  to-inversesⁿ (λ x → isos x .inverses .invl) (λ x → isos x .inverses .invr)
```
-->
