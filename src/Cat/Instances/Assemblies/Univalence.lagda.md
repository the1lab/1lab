<!--
```agda
open import Cat.Instances.Assemblies
open import Cat.Instances.Sets
open import Cat.Functor.Base
open import Cat.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Bool.Base

open import Realisability.PCA.Trivial
open import Realisability.PCA

import Cat.Reasoning

import Realisability.Data.Bool
import Realisability.PCA.Sugar
import Realisability.Base
```
-->

```agda
module Cat.Instances.Assemblies.Univalence {ℓA} (𝔸 : PCA ℓA) where
```

<!--
```agda
open Realisability.Data.Bool 𝔸
open Realisability.PCA.Sugar 𝔸
```
-->

# Failure of univalence in categories of assemblies

While the category $\thecat{Asm}(\bA)$ of [[assemblies]] over a
[[partial combinatory algebra]] $\bA$ may look like an ordinary category
of structured sets, the computable maps $X \to Y$ are *not* the maps
which preserve the realisability relation. This means that the category
of assemblies fails to be [[univalent|univalent category]], unless $\bA$
is trivial (so that $\thecat{Asm}(\bA) \cong \Sets$). We show this by
formalising the "flipped" assembly of booleans, `𝟚'`{.Agda} below, and
showing that no identifications between `𝟚`{.Agda} and `𝟚'`{.Agda}
extend the identity map.

```agda
𝟚' : Assembly 𝔸 lzero
𝟚' .Ob = Bool
𝟚' .has-is-set  = hlevel 2
𝟚' .realisers true  = singleton⁺ `false
𝟚' .realisers false = singleton⁺ `true
𝟚' .realised  true  = inc (`false .fst , inc refl)
𝟚' .realised  false = inc (`true .fst , inc refl)
```

This theorem turns out to be pretty basic path algebra: if we *are*
given an identification between `𝟚`{.Agda} and `𝟚'`{.Agda}, we have,
in particular, an identification between their realisability relations
*over* the identification between their underlying sets. And if we
assume that the identification between the underlying sets is
`refl`{.Agda}, we're left with an ordinary identification between the
realisability relations; but the realisability relation of `𝟚'`{.Agda}
was chosen explicitly so it differs from `𝟚`{.Agda}'s.

```agda
no-path-extends-identity
  : (p : 𝟚 𝔸 ≡ 𝟚') → ap Ob p ≡ refl → `true .fst ≡ `false .fst
no-path-extends-identity p q =
  let
    p' : (e : ↯ ⌞ 𝔸 ⌟) (x : Bool) → [ 𝟚 𝔸 ] e ⊩ x ≡ [ 𝟚' ] e ⊩ x
    p' e x =
      [ 𝟚 𝔸 ] e ⊩ transport refl x                     ≡⟨ sym (ap₂ (λ e x → [ 𝟚 𝔸 ] e ⊩ x) (transport-refl e) (ap (λ e → transport (sym e) x) q)) ⟩
      [ 𝟚 𝔸 ] (transport refl e) ⊩ subst Ob (sym p) x  ≡⟨ ap (λ r → e ∈ r x) (from-pathp (ap realisers p)) ⟩
      [ 𝟚' ] e ⊩ x                                     ∎
  in sym (□-out! (transport (p' (`true .fst) true) (inc refl)))
```

As we argued above, the identity map is a computable function from
`𝟚`{.Agda} to `𝟚'`{.Agda} with computable inverse; so if
$\thecat{Asm}(\bA)$ were univalent, we could extend it to a path
satisfying the conditions of the theorem above.

```agda
𝟚≅𝟚' : 𝟚 𝔸 Asm.≅ 𝟚'
𝟚≅𝟚' = Asm.make-iso to from (ext λ _ → refl) (ext λ _ → refl) where
  to = to-assembly-hom record where
    map      = λ x → x
    realiser = `not
    tracks   = λ where
      {true}  p → inc (sym (ap (`not ⋆_) (sym (□-out! p)) ∙ `not-βt))
      {false} p → inc (sym (ap (`not ⋆_) (sym (□-out! p)) ∙ `not-βf))

  from = to-assembly-hom record where
    map      = λ x → x
    realiser = `not
    tracks   = λ where
      {true}  p → inc (sym (ap (`not ⋆_) (sym (□-out! p)) ∙ `not-βf))
      {false} p → inc (sym (ap (`not ⋆_) (sym (□-out! p)) ∙ `not-βt))

Assemblies-not-univalent
  : is-category (Assemblies 𝔸 lzero) → is-trivial-pca 𝔸
Assemblies-not-univalent cat =
  let
    p : 𝟚 𝔸 ≡ 𝟚'
    p = cat .to-path 𝟚≅𝟚'

    Γ = Forget 𝔸
    module Sets = Cat.Reasoning (Sets lzero)

    γ : Path (Set lzero) (Γ · 𝟚 𝔸) (Γ · 𝟚') → Bool ≡ Bool
    γ = ap ∣_∣

    q : ap Ob p ≡ refl
    q =
      ap Ob p                                          ≡⟨⟩
      γ (ap (apply Γ) p)                               ≡⟨ ap γ (F-map-path (Forget 𝔸) cat Sets-is-category 𝟚≅𝟚') ⟩
      γ (Sets-is-category .to-path (F-map-iso Γ 𝟚≅𝟚')) ≡⟨ ap γ (ap (Sets-is-category .to-path) (Sets.≅-pathp refl refl refl)) ⟩
      γ (Sets-is-category .to-path Sets.id-iso)        ≡⟨ ap γ (to-path-refl Sets-is-category) ⟩
      γ refl                                           ≡⟨⟩
      refl                                             ∎
  in no-path-extends-identity p q
```
