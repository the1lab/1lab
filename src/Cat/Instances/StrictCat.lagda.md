```agda
open import 1Lab.Reflection.Record

open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Diagram.Product
open import Cat.Prelude

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

# Strict precategories

We call a precategory **strict** if its space of objects is a
`Set`{.Agda ident=is-set.}. While general precategories are too
homotopically interesting to fit into a `Precategory`{.Agda} (because
functor spaces will not, in general, be h-sets), the strict categories
_do_ form a precategory, which we denote $\strcat$.

<!--
```agda
private unquoteDecl eqv = declare-record-iso eqv (quote Functor)

Functor-is-set : ∀ {o h} {C D : Precategory o h} → is-set (Ob D)
               → is-set (Functor C D)
Functor-is-set {o = o} {h} {C} {D} dobset =
  is-hlevel≃ 2 (Iso→Equiv eqv e⁻¹) (hlevel 2)
  where
    open Precategory.HLevel-instance D
    instance
      Dob : H-Level (Ob D) 2
      Dob = basic-instance 2 dobset
```
-->

```agda
Strict-Cat : ∀ o h → Precategory _ _
Strict-Cat o h .Ob = Σ[ C ∈ Precategory o h ] (is-set (Ob C))
Strict-Cat o h .Hom (C , _) (D , _) = Functor C D
Strict-Cat o h .id  = Id
Strict-Cat o h ._∘_ = _F∘_
Strict-Cat o h .idr _       = Functor-path (λ _ → refl) λ _ → refl
Strict-Cat o h .idl _       = Functor-path (λ _ → refl) λ _ → refl
Strict-Cat o h .assoc _ _ _ = Functor-path (λ _ → refl) λ _ → refl
```

This assembles into a `Precategory`{.Agda} because the only bit of a
`Functor`{.Agda} that doesn't have a fixed h-level is the object
mapping; By asking that `D`{.Agda} be a strict category, this fixes the
functors to be sets.

```agda
Strict-Cat o h .Hom-set _ (D , dset) = Functor-is-set dset
```

## Products

We prove that `Strict-Cat`{.Agda} has products. This is because
$(\ca{C} \times_\cat \ca{D})_0$ is $\ca{C}_0 \times \ca{D}_0$,
and h-levels are closed under products.

```agda
Strict-Cat-Product
  : {C D : Precategory o h}
  → (cob : is-set (Ob C)) (dob : is-set (Ob D))
  → Product (Strict-Cat o h) (C , cob) (D , dob)
Strict-Cat-Product {C = C} {D = D} cob dob = prod where
  prod : Product (Strict-Cat _ _) (C , cob) (D , dob)
  prod .apex = C ×ᶜ D , ×-is-hlevel 2 cob dob
  prod .π₁ = Fst {C = C} {D = D}
  prod .π₂ = Snd {C = C} {D = D}
  prod .has-is-product .⟨_,_⟩ p q = Cat⟨ p , q ⟩
  prod .has-is-product .π₁∘factor = Functor-path (λ _ → refl) λ _ → refl
  prod .has-is-product .π₂∘factor = Functor-path (λ _ → refl) λ _ → refl
  prod .has-is-product .unique other p q =
    Functor-path (λ x i → F₀ (p i) x , F₀ (q i) x) λ f i → F₁ (p i) f , F₁ (q i) f
```
