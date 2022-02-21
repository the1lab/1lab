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
Functor-is-set : ∀ {o h} {C D : Precategory o h} → is-set (Ob D)
              → is-set (Functor C D)
Functor-is-set {o = o} {h} {C} {D} dobset = 
  retract→is-hlevel 2 unpack pack linv hl 
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

    linv : is-left-inverse unpack pack
    linv x i .F₀ = F₀ x
    linv x i .F₁ = F₁ x
    linv x i .F-id = F-id x
    linv x i .F-∘ = F-∘ x

    hl : is-set T
    hl = Σ-is-hlevel 2 (fun-is-hlevel 2 dobset) λ F →
         Σ-is-hlevel 2 (Π-is-hlevel 2 λ _ → 
                      Π-is-hlevel 2 λ _ → fun-is-hlevel 2 (D .Hom-set _ _)) λ F₁ → 
         is-prop→is-set (×-is-hlevel 1 (Π-is-hlevel 1 λ _ → D .Hom-set _ _ _ _) 
                                   (Π-is-hlevel 1 λ _ → 
                                    Π-is-hlevel 1 λ _ → 
                                    Π-is-hlevel 1 λ _ → 
                                    Π-is-hlevel 1 λ _ → 
                                    Π-is-hlevel 1 λ _ → D .Hom-set _ _ _ _))
```
-->

```agda
StrictCat : ∀ o h → Precategory _ _
StrictCat o h .Ob = Σ[ C ∈ Precategory o h ] (is-set (Ob C))
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
StrictCat o h .Hom-set _ (D , dset) = Functor-is-set dset
```

## Products

We prove that `StrictCat`{.Agda} has products. This is because 
$(\ca{C} \times_\cat \ca{D})_0$ is $\ca{C}_0 \times \ca{D}_0$,
and h-levels are closed under products.

```agda
StrictCat-Product 
  : {C D : Precategory o h}
  → (cob : is-set (Ob C)) (dob : is-set (Ob D))
  → Product (StrictCat o h) (C , cob) (D , dob)
StrictCat-Product {C = C} {D = D} cob dob = prod where
  prod : Product (StrictCat _ _) (C , cob) (D , dob)
  prod .apex = C ×Cat D , ×-is-hlevel 2 cob dob
  prod .π₁ = Fst {C = C} {D = D}
  prod .π₂ = Snd {C = C} {D = D}
  prod .has-is-product .⟨_,_⟩ p q = Cat⟨ p , q ⟩
  prod .has-is-product .π₁∘factor = Functor≡ (λ _ → refl) λ _ → refl
  prod .has-is-product .π₂∘factor = Functor≡ (λ _ → refl) λ _ → refl
  prod .has-is-product .unique other p q = 
    Functor≡ (λ x i → F₀ (p i) x , F₀ (q i) x) λ f i → F₁ (p i) f , F₁ (q i) f
```
