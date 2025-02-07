<!--
```agda
open import 1Lab.Reflection.Record

open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Diagram.Product
open import Cat.Prelude
open import Cat.Strict
```
-->

```agda
module Cat.Instances.StrictCat where
```

<!--
```agda
open Product
open is-product
open Precategory
open Functor

private variable
  o h : Level
```
-->

# The category of strict categories {defines="category-of-strict-categories"}

Recall that a precategory is said [[**strict**|strict category]] if its
space of objects is a `Set`{.Agda ident=is-set}. While general
precategories are too homotopically interesting to fit into a
`Precategory`{.Agda} (because functor spaces will not, in general, be
h-sets), the strict categories _do_ form a precategory, which we denote
$\strcat$.

<!--
```agda
private unquoteDecl eqv = declare-record-iso eqv (quote Functor)

Functor-is-set : ∀ {o h} {C D : Precategory o h} → is-set (Ob D)
               → is-set (Functor C D)
Functor-is-set {o = o} {h} {C} {D} dobset = Iso→is-hlevel! 2 eqv where instance
  Dob : H-Level (Ob D) 2
  Dob = basic-instance 2 dobset
```
-->

```agda
Strict-cats : ∀ o h → Precategory _ _
Strict-cats o h .Ob = Σ[ C ∈ Precategory o h ] (is-strict C)
Strict-cats o h .Hom (C , _) (D , _) = Functor C D
Strict-cats o h .id  = Id
Strict-cats o h ._∘_ = _F∘_
Strict-cats o h .idr _       = Functor-path (λ _ → refl) λ _ → refl
Strict-cats o h .idl _       = Functor-path (λ _ → refl) λ _ → refl
Strict-cats o h .assoc _ _ _ = Functor-path (λ _ → refl) λ _ → refl
```

This assembles into a `Precategory`{.Agda} because the only bit of a
`Functor`{.Agda} that doesn't have a fixed h-level is the object
mapping; By asking that `D`{.Agda} be a strict category, this fixes the
functors to be sets.

```agda
Strict-cats o h .Hom-set _ (D , dset) = Functor-is-set dset
```

## Products

We prove that `Strict-cats`{.Agda} has products. This is because $(\cC
\times \cD)_0$ is $\cC_0 \times \cD_0$, and h-levels are closed under
products.

```agda
Strict-cats-products
  : {C D : Precategory o h}
  → (cob : is-set (Ob C)) (dob : is-set (Ob D))
  → Product (Strict-cats o h) (C , cob) (D , dob)
Strict-cats-products {C = C} {D = D} cob dob = prod where
  prod : Product (Strict-cats _ _) (C , cob) (D , dob)
  prod .apex = C ×ᶜ D , ×-is-hlevel 2 cob dob
  prod .π₁ = Fst {C = C} {D = D}
  prod .π₂ = Snd {C = C} {D = D}
  prod .has-is-product .⟨_,_⟩ p q = Cat⟨ p , q ⟩
  prod .has-is-product .π₁∘⟨⟩ = Functor-path (λ _ → refl) λ _ → refl
  prod .has-is-product .π₂∘⟨⟩ = Functor-path (λ _ → refl) λ _ → refl
  prod .has-is-product .unique p q =
    Functor-path (λ x i → F₀ (p i) x , F₀ (q i) x) λ f i → F₁ (p i) f , F₁ (q i) f
```
