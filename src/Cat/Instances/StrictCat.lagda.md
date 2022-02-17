```agda
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Diagram.Product
open import Cat.Prelude

module Cat.Instances.StrictCat where
```

<!--
```agda
open Product
open IsProduct
open Precategory
open Functor

private variable
  o h : Level
```
-->

# Strict precategories

We call a precategory **strict** if its space of objects is a
`Set`{.Agda ident=isSet.}. While general precategories are too
homotopically interesting to fit into a `Precategory`{.Agda} (because
functor spaces will not, in general, be h-sets), the strict categories
_do_ form a precategory, which we denote $\strcat$.

<!--
```agda
isSet-Functor : ∀ {o h} {C D : Precategory o h} → isSet (Ob D)
              → isSet (Functor C D)
isSet-Functor {o = o} {h} {C} {D} dobset = 
  isHLevel-retract 2 unpack pack linv hl 
  where abstract
    T : Type (o ⊔ h)
    T = Σ[ F₀ ∈ (Ob C → Ob D) ] 
        Σ[ F₁ ∈ (∀ x y (f : Hom C x y) → Hom D (F₀ x) (F₀ y)) ]
        ((∀ x → F₁ x x (id C) ≡ id D) ×
         (∀ w x y (f : Hom C w x) (g : Hom C x y) 
           → F₁ _ _ (_∘_ C g f) ≡ _∘_ D (F₁ _ _ g) (F₁ _ _ f)))

    pack : Functor C D → T
    pack x = F₀ x , (λ _ _ → F₁ x) , (λ _ → F-id x) , λ _ _ _ g f → F-∘ x f g

    unpack : T → Functor C D
    unpack (f , g , p , q) .F₀ = f
    unpack (f , g , p , q) .F₁ = g _ _
    unpack (f , g , p , q) .F-id = p _
    unpack (f , g , p , q) .F-∘ _ _ = q _ _ _ _ _

    linv : isLeftInverse unpack pack
    linv x i .F₀ = F₀ x
    linv x i .F₁ = F₁ x
    linv x i .F-id = F-id x
    linv x i .F-∘ = F-∘ x

    hl : isSet T
    hl = isHLevelΣ 2 (isHLevel→ 2 dobset) λ F →
         isHLevelΣ 2 (isHLevelΠ 2 λ _ → 
                      isHLevelΠ 2 λ _ → isHLevel→ 2 (D .Hom-set _ _)) λ F₁ → 
         isProp→isSet (isHLevel× 1 (isHLevelΠ 1 λ _ → D .Hom-set _ _ _ _) 
                                   (isHLevelΠ 1 λ _ → 
                                    isHLevelΠ 1 λ _ → 
                                    isHLevelΠ 1 λ _ → 
                                    isHLevelΠ 1 λ _ → 
                                    isHLevelΠ 1 λ _ → D .Hom-set _ _ _ _))
```
-->

```agda
StrictCat : ∀ o h → Precategory _ _
StrictCat o h .Ob = Σ[ C ∈ Precategory o h ] (isSet (Ob C))
StrictCat o h .Hom (C , _) (D , _) = Functor C D
StrictCat o h .id  = Id
StrictCat o h ._∘_ = _F∘_
StrictCat o h .idr _       = Functor≡ (λ _ → refl) λ _ → refl
StrictCat o h .idl _       = Functor≡ (λ _ → refl) λ _ → refl
StrictCat o h .assoc _ _ _ = Functor≡ (λ _ → refl) λ _ → refl
```

This assembles into a `Precategory`{.Agda} because the only bit of a
`Functor`{.Agda} that doesn't have a fixed h-level is the object
mapping; By asking that `D`{.Agda} be a strict category, this fixes the
functors to be sets.

```agda
StrictCat o h .Hom-set _ (D , dset) = isSet-Functor dset
```

## Products

We prove that `StrictCat`{.Agda} has products. This is because 
$(\ca{C} \times_\cat \ca{D})_0$ is $\ca{C}_0 \times \ca{D}_0$,
and h-levels are closed under products.

```agda
StrictCat-Product 
  : {C D : Precategory o h}
  → (cob : isSet (Ob C)) (dob : isSet (Ob D))
  → Product (StrictCat o h) (C , cob) (D , dob)
StrictCat-Product {C = C} {D = D} cob dob = prod where
  prod : Product (StrictCat _ _) (C , cob) (D , dob)
  prod .apex = C ×Cat D , isHLevel× 2 cob dob
  prod .π₁ = Fst {C = C} {D = D}
  prod .π₂ = Snd {C = C} {D = D}
  prod .hasIsProduct .⟨_,_⟩ p q = Cat⟨ p , q ⟩
  prod .hasIsProduct .π₁∘factor = Functor≡ (λ _ → refl) λ _ → refl
  prod .hasIsProduct .π₂∘factor = Functor≡ (λ _ → refl) λ _ → refl
  prod .hasIsProduct .unique other p q = 
    Functor≡ (λ x i → F₀ (p i) x , F₀ (q i) x) λ f i → F₁ (p i) f , F₁ (q i) f
```
