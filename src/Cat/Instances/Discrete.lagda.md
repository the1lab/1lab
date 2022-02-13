```agda
open import Cat.Univalent
open import Cat.Prelude

module Cat.Instances.Discrete where
```

<!--
```agda
private variable
  ℓ ℓ' : Level
  
open Precategory
open Functor
```
-->

# Discrete categories

Given a groupoid $A$, we can build the category $\mathrm{Disc}(A)$ with
space of objects $A$ and a single morphism $x \to y$ whenever $x \equiv
y$.

```agda
Disc : (A : Type ℓ) → isGroupoid A → Precategory ℓ ℓ
Disc A A-grpd .Ob = A
Disc A A-grpd .Hom = _≡_
Disc A A-grpd .Hom-set = A-grpd
Disc A A-grpd .id = refl
Disc A A-grpd ._∘_ p q = q ∙ p
Disc A A-grpd .idr _ = ∙-id-l _
Disc A A-grpd .idl _ = ∙-id-r _
Disc A A-grpd .assoc _ _ _ = sym (∙-assoc _ _ _)

Disc′ : Set ℓ → Precategory ℓ ℓ
Disc′ (A , aset) = Disc A h where abstract
  h : isGroupoid A
  h = isHLevel-suc 2 aset
```

We can lift any function between the underlying types to a functor
between discrete categories. This is because every function
automatically respects equality in a functorial way.

```agda
liftDisc 
  : ∀ {A : Set ℓ} {B : Set ℓ'}
  → (A .fst → B .fst)
  → Functor (Disc′ A) (Disc′ B)
liftDisc f .F₀ = f
liftDisc f .F₁ = ap f
liftDisc f .F-id = refl
liftDisc f .F-∘ p q = ap-comp-path f q p
```

<!--
```agda
Codisc′ : ∀ {ℓ'} → Type ℓ → Precategory ℓ ℓ'
Codisc′ x .Ob = x
Codisc′ x .Hom _ _ = Lift _ ⊤
Codisc′ x .Hom-set _ _ = isProp→isSet (λ _ _ i → lift tt)
Codisc′ x .id = lift tt
Codisc′ x ._∘_ _ _ = lift tt
Codisc′ x .idr _ = refl
Codisc′ x .idl _ = refl
Codisc′ x .assoc _ _ _ = refl
```
-->
