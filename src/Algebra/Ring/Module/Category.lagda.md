<!--
```agda
open import Algebra.Ring.Module
open import Algebra.Group.Ab
open import Algebra.Group
open import Algebra.Ring

open import Cat.Abelian.Instances.Ab
open import Cat.Abelian.Base
open import Cat.Prelude
```
-->

```agda
module Algebra.Ring.Module.Category {ℓ} (R : Ring ℓ) where
```

<!--
```agda
private module R = Ring-on (R .snd)
open Ab-category
open is-additive
open make-abelian-group
```
-->

# The category R-Mod

Let us investigate the structure of the category $R$-Mod, for whatever
your favourite ring $R$ is^[if you don't have a favourite ring, just
pick the integers, they're fine.]. The first thing we'll show is that it
admits an $\Ab$-enrichment. This is the usual "pointwise" group
structure, but proving that the pointwise sum is a still a linear map
is, ahem, very annoying. See for yourself:

```agda
R-Mod-ab-category : ∀ {ℓ′} → Ab-category (R-Mod ℓ′ R)
R-Mod-ab-category .Abelian-group-on-hom A B = to-abelian-group-on grp where
  module A = Module A
  module B = Module B
  grp : make-abelian-group (R-Mod.Hom A B)
  grp .ab-is-set = R-Mod.Hom-set _ _

  grp .mul f g .map x = f .map x B.+ g .map x
  grp .mul f g .linear r m s n =
    fₘ (r A.⋆ m A.+ s A.⋆ n) B.+ gₘ (r A.⋆ m A.+ s A.⋆ n)       ≡⟨ ap₂ B._+_ (f .linear _ _ _ _) (g .linear _ _ _ _) ⟩
    (r B.⋆ fₘ m B.+ s B.⋆ fₘ n) B.+ (r B.⋆ gₘ m B.+ s B.⋆ gₘ n) ≡⟨ B.G.pullr (B.G.pulll B.G.commutes) ⟩
    r B.⋆ fₘ m B.+ (r B.⋆ gₘ m B.+ s B.⋆ fₘ n) B.+ s B.⋆ gₘ n   ≡⟨ B.G.pulll (B.G.pulll (sym (B.⋆-add-r r _ _))) ⟩
    (r B.⋆ (fₘ m B.+ gₘ m) B.+ (s B.⋆ fₘ n)) B.+ (s B.⋆ gₘ n)   ≡⟨ B.G.pullr (sym (B.⋆-add-r s _ _)) ⟩
    r B.⋆ (fₘ m B.+ gₘ m) B.+ s B.⋆ (fₘ n B.+ gₘ n)             ∎
    where
      fₘ = f .map
      gₘ = g .map
```

<details>
<summary>The rest of the construction is also _Just Like That_, so I'm
going to keep it in this `<details>`{.html} element out of
decency.</summary>
```agda
  grp .1g .map x    = B.G.1g
  grp .1g .linear r m s n =
    B.G.1g                        ≡˘⟨ B.⋆-group-hom.pres-id _ ⟩
    s B.⋆ B.G.1g                  ≡˘⟨ B.G.eliml (B.⋆-group-hom.pres-id _) ⟩
    r B.⋆ B.G.1g B.+ s B.⋆ B.G.1g ∎
  grp .inv f .map x   = B.G._⁻¹ (f .map x)
  grp .inv f .linear r m s n =
       ap B.G._⁻¹ (f .linear r m s n)
    ·· B.G.inv-comm
    ·· B.G.commutes
     ∙ ap₂ B._+_ (sym (B.⋆-group-hom.pres-inv _)) (sym (B.⋆-group-hom.pres-inv _))
  grp .assoc x y z = Linear-map-path (funext λ x → sym B.G.associative)
  grp .invl x = Linear-map-path (funext λ x → B.G.inversel)
  grp .idl x = Linear-map-path (funext λ x → B.G.idl)
  grp .comm x y = Linear-map-path (funext λ x → B.G.commutes)
R-Mod-ab-category .∘-linear-l f g h = Linear-map-path refl
R-Mod-ab-category .∘-linear-r {B = B} {C} f g h =
  Linear-map-path $ funext λ x →
    f .map (g .map x) C.+ f .map (h .map x)                     ≡⟨ ap₂ C._+_ (sym (C.⋆-id _)) (sym (C.⋆-id _)) ⟩
    R.1r C.⋆ f .map (g .map x) C.+ (R.1r C.⋆ f .map (h .map x)) ≡⟨ sym (f .linear R.1r (g .map x) R.1r (h .map x)) ⟩
    f .map (R.1r B.⋆ g .map x B.+ R.1r B.⋆ h .map x)            ≡⟨ ap (f .map) (ap₂ B._+_ (B.⋆-id _) (B.⋆-id _)) ⟩
    f .map (g .map x B.+ h .map x)                              ∎
  where
    module C = Module C
    module B = Module B
```
</details>

## Finite biproducts

Let's now prove that $R$-Mod is a preadditive category. This is exactly
as in $\Ab$: The zero object is the zero group, equipped with its unique
choice of $R$-module structure, and direct products $M \oplus N$ are
given by direct products of the underlying groups $M_G \oplus N_G$ with
the canonical choice of $R$-module structure.

The zero object is simple, because the unit type is so well-behaved^[and
`Lift` types, too] when it comes to definitional equality: Everything is
constantly the unit, including the paths, which are _all_ reflexivity.

```agda
R-Mod-is-additive : is-additive (R-Mod _ R)
R-Mod-is-additive .has-ab = R-Mod-ab-category
R-Mod-is-additive .has-terminal = record
  { top  = _ , ∅ᴹ
  ; has⊤ = λ x → contr
    (record { map    = λ _ → lift tt
            ; linear = λ _ _ _ _ → refl
            })
    (λ _ → Linear-map-path refl)
  }
  where
    ∅ᴹ : Module-on R (Ab-is-additive .has-terminal .Terminal.top)
    ∅ᴹ .Module-on._⋆_ = λ _ _ → lift tt
    ∅ᴹ .Module-on.⋆-id _        = refl
    ∅ᴹ .Module-on.⋆-add-r _ _ _ = refl
    ∅ᴹ .Module-on.⋆-add-l _ _ _ = refl
    ∅ᴹ .Module-on.⋆-assoc _ _ _ = refl
```

For the direct products, on the other hand, we have to do a bit more
work. Like we mentioned before, the direct product of modules is built
on the direct product of abelian groups (which is, in turn, built on the
Cartesian product of types). The module action, and its laws, are
defined pointwise using the $R$-module structures of $M$ and $N$:

```agda
R-Mod-is-additive .has-prods M N = prod where
  module P = is-additive.Product
    Ab-is-additive
    (Ab-is-additive .has-prods (M .fst) (N .fst))
  module M = Module M
  module N = Module N

  M⊕ᵣN : Module-on R P.apex
  M⊕ᵣN .Module-on._⋆_ r (a , b) = r M.⋆ a , r N.⋆ b
  M⊕ᵣN .Module-on.⋆-id _        = Σ-pathp (M.⋆-id _)        (N.⋆-id _)
  M⊕ᵣN .Module-on.⋆-add-r _ _ _ = Σ-pathp (M.⋆-add-r _ _ _) (N.⋆-add-r _ _ _)
  M⊕ᵣN .Module-on.⋆-add-l _ _ _ = Σ-pathp (M.⋆-add-l _ _ _) (N.⋆-add-l _ _ _)
  M⊕ᵣN .Module-on.⋆-assoc _ _ _ = Σ-pathp (M.⋆-assoc _ _ _) (N.⋆-assoc _ _ _)
```

We can readily define the universal cone: The projection maps are the
projection maps of the underlying type, which are definitionally linear.
Proving that this cone is actually universal involves a bit of
path-mangling, but it's nothing _too_ bad:

```agda
  open Ab-category.is-product
  open Ab-category.Product
  prod : Ab-category.Product R-Mod-ab-category M N
  prod .apex = _ , M⊕ᵣN
  prod .π₁ .map (a , _)    = a
  prod .π₁ .linear r m s n = refl
  prod .π₂ .map (_ , b)    = b
  prod .π₂ .linear r m s n = refl

  prod .has-is-product .⟨_,_⟩ f g .map x = f .map x , g .map x
  prod .has-is-product .⟨_,_⟩ f g .linear r m s n =
    Σ-pathp (f .linear _ _ _ _) (g .linear _ _ _ _)
  prod .has-is-product .π₁∘factor = Linear-map-path refl
  prod .has-is-product .π₂∘factor = Linear-map-path refl
  prod .has-is-product .unique other p q = Linear-map-path {ℓ′ = lzero} $ funext λ x →
    Σ-pathp (ap map p $ₚ x) (ap map q $ₚ x)
```

<!-- TODO [Amy 2022-09-15]
Define kernels, cokernels, and show that ker (coker f) ≃ coker (ker f).
-->
