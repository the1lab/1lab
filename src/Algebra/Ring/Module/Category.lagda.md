<!--
```agda
open import Algebra.Ring.Module.Notation
open import Algebra.Ring.Module.Action
open import Algebra.Ring.Commutative
open import Algebra.Group.Notation
open import Algebra.Ring.Module
open import Algebra.Group.Ab
open import Algebra.Group
open import Algebra.Ring

open import Cat.Displayed.Univalence.Thin
open import Cat.Abelian.Instances.Ab
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
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
open Ab-category hiding (_+_)
open is-additive hiding (_+_)
open make-abelian-group
open Total-hom

open Module-notation ⦃ ... ⦄
open Additive-notation ⦃ ... ⦄
```
-->

# The category R-Mod

Let us investigate the structure of the category $R$-Mod, for whatever
your favourite ring $R$ is^[if you don't have a favourite ring, just
pick the integers, they're fine.]. The first thing we'll show is that it
admits an $\Ab$-enrichment. This is the usual "pointwise" group
structure, but proving that the pointwise sum is a still a linear map
is, ahem, very annoying. See for yourself:

<!--
```agda
module _ {ℓm ℓn} (M : Module R ℓm) (N : Module R ℓn) where
  instance
    _ = module-notation M
    _ = module-notation N
```
-->

```agda
  +-is-linear-map
    : ∀ {f g : ⌞ M ⌟ → ⌞ N ⌟}
    → is-linear-map f (M .snd) (N .snd)
    → is-linear-map g (M .snd) (N .snd)
    → is-linear-map (λ x → f x + g x) (M .snd) (N .snd)
  +-is-linear-map {f = f} {g} fp gp .linear r s t =
    f (r ⋆ s + t) + g (r ⋆ s + t)      ≡⟨ ap₂ _+_ (fp .linear r s t) (gp .linear r s t) ⟩
    (r ⋆ f s + f t) + (r ⋆ g s + g t)  ≡⟨ sym +-assoc ∙ ap₂ _+_ refl (+-assoc ∙ ap₂ _+_ (+-comm _ _) refl ∙ sym +-assoc) ∙ +-assoc ∙ +-assoc ⟩
    ⌜ r ⋆ f s + r ⋆ g s ⌝ + f t + g t  ≡˘⟨ ap¡ (⋆-distribl r (f s) (g s)) ⟩
    r ⋆ (f s + g s) + f t + g t        ≡˘⟨ +-assoc ⟩
    r ⋆ (f s + g s) + (f t + g t)      ∎
```

Doing some further algebra will let us prove that linear maps are also
closed under pointwise inverse, and contain the zero map. The
calculations speak for themselves:

```agda
  neg-is-linear-map
    : ∀ {f : ⌞ M ⌟ → ⌞ N ⌟}
    → is-linear-map f (M .snd) (N .snd)
    → is-linear-map (λ x → - f x) (M .snd) (N .snd)
  neg-is-linear-map {f = f} fp .linear r s t =
    - f (r ⋆ s + t)        ≡⟨ ap -_ (fp .linear r s t) ⟩
    - (r ⋆ f s + f t)      ≡⟨ neg-comm ∙ +-comm _ _ ⟩
    - (r ⋆ f s) + - (f t)  ≡⟨ ap₂ _+_ (sym (Module-on.⋆-invr (N .snd))) refl ⟩
    r ⋆ - f s + - f t      ∎

  0-is-linear-map : is-linear-map (λ x → 0g) (M .snd) (N .snd)
  0-is-linear-map .linear r s t = sym (+-idr ∙ Module-on.⋆-idr (N .snd))
```

Finally, if the base ring $R$ is commutative, then linear maps are also
closed under pointwise scalar multiplication:

```agda
  ⋆-is-linear-map
    : ∀ {f : ⌞ M ⌟ → ⌞ N ⌟} {r : ⌞ R ⌟}
    → is-commutative-ring R
    → is-linear-map f (M .snd) (N .snd)
    → is-linear-map (λ x → r ⋆ f x) (M .snd) (N .snd)
  ⋆-is-linear-map {f = f} {r} cring fp .linear s x y =
    r ⋆ f (s ⋆ x + y)      ≡⟨ ap (r ⋆_) (fp .linear _ _ _) ⟩
    r ⋆ (s ⋆ f x + f y)    ≡⟨ ⋆-distribl r (s ⋆ f x) (f y) ⟩
    r ⋆ s ⋆ f x + r ⋆ f y  ≡⟨ ap (_+ r ⋆ f y) (⋆-assoc _ _ _ ∙ ap (_⋆ f x) cring ∙ sym (⋆-assoc _ _ _)) ⟩
    s ⋆ r ⋆ f x + r ⋆ f y  ∎
```

<!--
```agda

  Linear-map-group : Abelian-group (ℓ ⊔ ℓm ⊔ ℓn)
  ∣ Linear-map-group .fst ∣ = Linear-map M N
  Linear-map-group .fst .is-tr = Linear-map-is-set R
  Linear-map-group .snd = to-abelian-group-on grp where
    grp : make-abelian-group (Linear-map M N)
    grp .ab-is-set = Linear-map-is-set R

    grp .mul f g .map x = f .map x + g .map x
    grp .mul f g .lin = +-is-linear-map (f .lin) (g .lin)

    grp .inv f .map x = - f .map x
    grp .inv f .lin = neg-is-linear-map (f .lin)

    grp .1g .map x = 0g
    grp .1g .lin = 0-is-linear-map

    grp .idl f       = ext λ x → +-idl
    grp .assoc f g h = ext λ x → +-assoc
    grp .invl f      = ext λ x → +-invl
    grp .comm f g    = ext λ x → +-comm _ _

module _ (cring : is-commutative-ring R) {ℓm ℓn} (M : Module R ℓm) (N : Module R ℓn) where
  private instance
    _ = module-notation M
    _ = module-notation N

  Action-on-hom : Ring-action R (Linear-map-group M N .snd)
  Action-on-hom .Ring-action._⋆_ r f .map z = r ⋆ f .map z
  Action-on-hom .Ring-action._⋆_ r f .lin = ⋆-is-linear-map M N cring (f .lin)
  Action-on-hom .Ring-action.⋆-distribl f g h = ext λ x → ⋆-distribl _ _ _
  Action-on-hom .Ring-action.⋆-distribr f g h = ext λ x → ⋆-distribr _ _ _
  Action-on-hom .Ring-action.⋆-assoc f g h = ext λ x → ⋆-assoc _ _ _
  Action-on-hom .Ring-action.⋆-id f = ext λ x → ⋆-id _

  Hom-Mod : Module R (level-of ⌞ R ⌟ ⊔ ℓm ⊔ ℓn)
  Hom-Mod .fst = Action→Module R (Linear-map-group M N) Action-on-hom .fst
  Hom-Mod .snd = Action→Module R (Linear-map-group M N) Action-on-hom .snd
```
-->

Since we've essentially equipped the set of linear maps $M \to N$ with
an $R$-module structure, which certainly includes an [[abelian group]]
structure, we can conclude that $\Mod[R]$ is not only a category, but an
$\Ab$-category to boot!

```agda
R-Mod-ab-category : ∀ {ℓ'} → Ab-category (R-Mod R ℓ')
```

<!--
```agda
R-Mod-ab-category .Abelian-group-on-hom A B = to-abelian-group-on grp where
  instance
    _ = module-notation A
    _ = module-notation B

  grp : make-abelian-group (R-Mod.Hom A B)
  grp .ab-is-set = R-Mod.Hom-set _ _
  grp .mul f g .hom x = f # x + g # x
  grp .mul f g .preserves = +-is-linear-map A B (f .preserves) (g .preserves)
  grp .inv f .hom x = - f # x
  grp .inv f .preserves = neg-is-linear-map A B (f .preserves)
  grp .1g .hom x = 0g
  grp .1g .preserves = 0-is-linear-map A B

  grp .idl f       = ext λ x → +-idl
  grp .assoc f g h = ext λ x → +-assoc
  grp .invl f      = ext λ x → +-invl
  grp .comm f g    = ext λ x → +-comm _ _

R-Mod-ab-category .∘-linear-l f g h = trivial!
R-Mod-ab-category .∘-linear-r {B = B} {C} f g h = ext λ x →
  sym (is-linear-map.pres-+ (f .preserves) _ _)
```
-->

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
R-Mod-is-additive : ∀ {ℓ} → is-additive (R-Mod R ℓ)
R-Mod-is-additive .has-ab = R-Mod-ab-category
R-Mod-is-additive .has-terminal = term where
  act : Ring-action R _
  act .Ring-action._⋆_ r _          = lift tt
  act .Ring-action.⋆-distribl r x y = refl
  act .Ring-action.⋆-distribr r x y = refl
  act .Ring-action.⋆-assoc r s x    = refl
  act .Ring-action.⋆-id x           = refl

  ∅ᴹ : Module R _
  ∅ᴹ = Action→Module R (Ab-is-additive .has-terminal .Terminal.top) act

  term : Terminal (R-Mod R _)
  term .Terminal.top = ∅ᴹ
  term .Terminal.has⊤ x .centre .hom _ = lift tt
  term .Terminal.has⊤ x .centre .preserves .linear r s t = refl
  term .Terminal.has⊤ x .paths r = trivial!
```

For the direct products, on the other hand, we have to do a bit more
work. Like we mentioned before, the direct product of modules is built
on the direct product of abelian groups (which is, in turn, built on the
Cartesian product of types). The module action, and its laws, are
defined pointwise using the $R$-module structures of $M$ and $N$:

```agda
R-Mod-is-additive .has-prods M N = prod where
  module P = Product (Ab-is-additive .has-prods
    (M .fst , Module-on→Abelian-group-on (M .snd))
    (N .fst , Module-on→Abelian-group-on (N .snd)))

  instance
    _ = module-notation M
    _ = module-notation N

  act : Ring-action R _
  act .Ring-action._⋆_ r (a , b)    = r ⋆ a , r ⋆ b
  act .Ring-action.⋆-distribl r x y = ap₂ _,_ (⋆-distribl _ _ _) (⋆-distribl _ _ _)
  act .Ring-action.⋆-distribr r x y = ap₂ _,_ (⋆-distribr _ _ _) (⋆-distribr _ _ _)
  act .Ring-action.⋆-assoc r s x    = ap₂ _,_ (⋆-assoc _ _ _) (⋆-assoc _ _ _)
  act .Ring-action.⋆-id x           = ap₂ _,_ (⋆-id _) (⋆-id _)

  M⊕ᵣN : Module R _
  M⊕ᵣN = Action→Module R P.apex act
```

We can readily define the universal cone: The projection maps are the
projection maps of the underlying type, which are definitionally linear.
Proving that this cone is actually universal involves a bit of
path-mangling, but it's nothing _too_ bad:

```agda
  open Product
  open is-product

  prod : Product (R-Mod _ _) M N
  prod .apex = M⊕ᵣN
  prod .π₁ .hom = fst
  prod .π₁ .preserves .linear r s t = refl
  prod .π₂ .hom = snd
  prod .π₂ .preserves .linear r s t = refl
  prod .has-is-product .⟨_,_⟩ f g .hom x = f # x , g # x
  prod .has-is-product .⟨_,_⟩ f g .preserves .linear r m s =
    Σ-pathp (f .preserves .linear _ _ _) (g .preserves .linear _ _ _)
  prod .has-is-product .π₁∘⟨⟩ = trivial!
  prod .has-is-product .π₂∘⟨⟩ = trivial!
  prod .has-is-product .unique p q = ext λ x → p #ₚ x , q #ₚ x
```

<!-- TODO [Amy 2022-09-15]
Define kernels, cokernels, and show that ker (coker f) ≃ coker (ker f).
-->
