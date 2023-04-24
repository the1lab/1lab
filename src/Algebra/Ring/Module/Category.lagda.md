<!--
```agda
open import Algebra.Ring.Module.Notation
open import Algebra.Group.Notation
open import Algebra.Ring.Module
open import Algebra.Group.Ab
open import Algebra.Group
open import Algebra.Ring

open import Cat.Displayed.Univalence.Thin
open import Cat.Abelian.Instances.Ab
open import Cat.Diagram.Terminal
open import Cat.Abelian.Base
open import Cat.Prelude hiding (_+_ ; _*_)
```
-->

```agda
module Algebra.Ring.Module.Category {ℓ} (R : Ring ℓ) where
```

<!--
```agda
private module R = Ring-on (R .snd)
open Ab-category hiding (_+_ ; Terminal)
open is-additive hiding (_+_ ; Terminal)
open make-abelian-group
open Total-hom
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
R-Mod-ab-category : ∀ {ℓ′} → Ab-category (R-Mod R ℓ′)
R-Mod-ab-category .Abelian-group-on-hom A B = to-abelian-group-on grp where
  open Module-notation ⦃ ... ⦄
  open Additive-notation ⦃ ... ⦄
  instance
    _ = module-notation A
    _ = module-notation B

  grp : make-abelian-group (R-Mod.Hom A B)
  grp .ab-is-set = R-Mod.Hom-set _ _
  grp .mul f g .hom x = f # x + g # x
  grp .mul f g .preserves .linear r s t =
    f # (r ⋆ s + t) + g # (r ⋆ s + t)         ≡⟨ ap₂ _+_ (f .preserves .linear r s t) (g .preserves .linear r s t) ⟩
    (r ⋆ f # s + f # t) + (r ⋆ g # s + g # t) ≡⟨ sym +-assoc ∙ ap₂ _+_ refl (+-assoc ∙ ap₂ _+_ (+-comm _ _) refl ∙ sym +-assoc) ∙ +-assoc ∙ +-assoc ⟩
    ⌜ r ⋆ f # s + r ⋆ g # s ⌝ + f # t + g # t ≡˘⟨ ap¡ (⋆-distribl r (f # s) (g # s)) ⟩
    r ⋆ (f # s + g # s) + f # t + g # t       ≡˘⟨ +-assoc ⟩
    r ⋆ (f # s + g # s) + (f # t + g # t)     ∎
```

<details>
<summary>The rest of the construction is also _Just Like That_, so I'm
going to keep it in this `<details>`{.html} element out of
decency.</summary>
```agda
  grp .inv f .hom x = - f # x
  grp .inv f .preserves .linear r s t =
    - f # (r ⋆ s + t)         ≡⟨ ap -_ (f .preserves .linear r s t) ⟩
    - (r ⋆ f # s + f # t)     ≡⟨ neg-comm ∙ +-comm _ _ ⟩
    - (r ⋆ f # s) + - (f # t) ≡⟨ ap₂ _+_ (sym (Module-on.⋆-negr (B .snd))) refl ⟩
    r ⋆ - f # s + - f # t     ∎
  grp .1g .hom x = 0g
  grp .1g .preserves .linear r s t = sym (+-idr ∙ Module-on.⋆-idr (B .snd))
  grp .idl f = Homomorphism-path λ x → +-idl
  grp .assoc f g h = Homomorphism-path λ x → +-assoc
  grp .invl f = Homomorphism-path λ x → +-invl
  grp .comm f g = Homomorphism-path λ x → +-comm _ _
R-Mod-ab-category .∘-linear-l f g h = Homomorphism-path λ x → refl
R-Mod-ab-category .∘-linear-r {B = B} {C} f g h = Homomorphism-path λ x → sym (is-linear-map.pres-+ (f .preserves) _ _)
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
R-Mod-is-additive : is-additive (R-Mod R _)
R-Mod-is-additive .has-ab = R-Mod-ab-category
R-Mod-is-additive .has-terminal = term where
  ∅ᴹ : Module R _
  ∅ᴹ = from-module-on R $ action→module-on R
    (Ab-is-additive .has-terminal .Terminal.top)
      (λ _ _ → lift tt)
      (λ _ _ _ → refl)
      (λ _ _ _ → refl)
      (λ _ _ _ → refl)
      λ _ → refl

  term : Terminal (R-Mod R _)
  term .Terminal.top = ∅ᴹ
  term .Terminal.has⊤ x .centre .hom _ = lift tt
  term .Terminal.has⊤ x .centre .preserves .linear r s t = refl
  term .Terminal.has⊤ x .paths r = Homomorphism-path λ _ → refl
```

For the direct products, on the other hand, we have to do a bit more
work. Like we mentioned before, the direct product of modules is built
on the direct product of abelian groups (which is, in turn, built on the
Cartesian product of types). The module action, and its laws, are
defined pointwise using the $R$-module structures of $M$ and $N$:

```agda
R-Mod-is-additive .has-prods M N = prod where
  module P = is-additive.Product Ab-is-additive (Ab-is-additive .has-prods
    (M .fst , Module-on→Abelian-group-on R (M .snd))
    (N .fst , Module-on→Abelian-group-on R (N .snd)))

  open Module-notation ⦃ ... ⦄
  instance
    _ = module-notation M
    _ = module-notation N

  M⊕ᵣN : Module R _
  M⊕ᵣN = from-module-on R $ action→module-on R
    P.apex
    (λ r (a , b) → r ⋆ a , r ⋆ b)
    (λ r x y → Σ-pathp (⋆-distribl _ _ _) (⋆-distribl _ _ _))
    (λ r x y → Σ-pathp (⋆-distribr _ _ _) (⋆-distribr _ _ _))
    (λ r x y → Σ-pathp (⋆-assoc _ _ _) (⋆-assoc _ _ _))
    (λ x → Σ-pathp (⋆-id _) (⋆-id _))
```

We can readily define the universal cone: The projection maps are the
projection maps of the underlying type, which are definitionally linear.
Proving that this cone is actually universal involves a bit of
path-mangling, but it's nothing _too_ bad:

```agda
  open Ab-category.Product
  open Ab-category.is-product

  prod : Ab-category.Product R-Mod-ab-category M N
  prod .apex = M⊕ᵣN
  prod .π₁ .hom = fst
  prod .π₁ .preserves .linear r s t = refl
  prod .π₂ .hom = snd
  prod .π₂ .preserves .linear r s t = refl
  prod .has-is-product .⟨_,_⟩ f g .hom x = f # x , g # x
  prod .has-is-product .⟨_,_⟩ f g .preserves .linear r m s =
    Σ-pathp (f .preserves .linear _ _ _) (g .preserves .linear _ _ _)
  prod .has-is-product .π₁∘factor = Homomorphism-path λ _ → refl
  prod .has-is-product .π₂∘factor = Homomorphism-path λ _ → refl
  prod .has-is-product .unique other p q = Homomorphism-path {ℓ = lzero} λ x →
    Σ-pathp (ap hom p $ₚ x) (ap hom q $ₚ x)
```

<!-- TODO [Amy 2022-09-15]
Define kernels, cokernels, and show that ker (coker f) ≃ coker (ker f).
-->
