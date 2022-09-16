```agda
open import Cat.Functor.Equivalence.Path
open import Cat.Functor.Equivalence
open import Cat.Instances.Discrete
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Reasoning as Cr

module Cat.Bi.Instances.Grpd where
```

# Groupoids

A pregroupoid is a precategory where all morphisms are isomorphisms
(this is a property of a precategory, not structure on precategories). A
groupoid, then, is a _category_ where all morphisms are isomorphisms.
But these are entirely determined by their spaces of objects, as we'll
see.

```agda
is-groupoid′ : ∀ {o ℓ} → Precategory o ℓ → Type _
is-groupoid′ C = is-category C × (∀ {x y} (f : Hom x y) → is-invertible f)
  where open Cr C

Groupoid→3-type : ∀ {o ℓ} → Σ (Precategory o ℓ) is-groupoid′ → n-Type o 3
Groupoid→3-type (X , u , _) = el (X .Precategory.Ob) (Univalent.Ob-is-groupoid u)

3-type→Groupoid : ∀ {o} → n-Type o 3 → Σ (Precategory o o) is-groupoid′
3-type→Groupoid x .fst = Disc ∣ x ∣ (x .is-tr)
3-type→Groupoid x .snd = ids , λ f → make-invertible (sym f) (∙-inv-l f) (∙-inv-r f)
  where
    open Cr (Disc ∣ x ∣ (x .is-tr))
    ids : is-identity-system _≅_ (λ a → id-iso)
    ids .to-path = to
    ids .to-path-over p = ≅-pathp refl (p .to) (λ i j → p .to (i ∧ j))

open is-iso
Groupoid≃3-Type : ∀ {o} → Σ (Precategory o o) is-groupoid′ ≃ n-Type o 3
Groupoid≃3-Type .fst = Groupoid→3-type
Groupoid≃3-Type .snd =
  is-iso→is-equiv λ where
    .inv → 3-type→Groupoid
    .rinv x → n-ua (_ , id-equiv)
    .linv x →
      let module x = Cr (x .fst) in
      Σ-prop-path
      (λ x → ×-is-hlevel 1 (hlevel 1) λ p q i f → is-invertible-is-prop x (p f) (q f) i)
      (ap fst $ Category-identity-system .to-path
        {_ , 3-type→Groupoid (Groupoid→3-type x) .snd .fst}
        {_ , x .snd .fst}
        ( Disc-adjunct (λ x → x)
        , ff+split-eso→is-equivalence
            (is-iso→is-equiv (iso
              (λ e → x .snd .fst .to-path (invertible→iso (x .fst) _ (x .snd .snd e)))
              (λ p → Hom-transport {C = x .fst} _ _ _
                ·· x.elimr (x.idl _ ∙ transport-refl _)
                ·· from-pathp (λ i → x .snd .fst .to-path-over (x.invertible→iso p (x .snd .snd p)) i .to))
              (λ p → ap (x .snd .fst .to-path) (≅-pathp (x .fst) _ _ refl)
                   ∙ Univalent.path→iso→path (x .snd .fst) p)))
            (λ y → y , id-iso (x .fst))))
  where open Cr
