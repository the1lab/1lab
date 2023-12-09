<!--
```agda
open import Cat.Diagram.Pullback.Properties
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Product
open import Cat.Prelude

import Cat.Displayed.Instances.Subobjects as Sub
import Cat.Diagram.Pullback.Along as Pba
import Cat.Diagram.Pullback as Pb
import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Diagram.Power
```

<!--
```agda
  {o ℓ} (C : Precategory o ℓ) (fc : Finitely-complete C)
  where

open Finitely-complete fc
open Binary-products C products hiding (_⊗₀_)
open Sub C
open Cat C
open Pba C
open Pb C
```
-->

# Power objects

```agda
record is-power-object (A : Ob) (PA : Ob) {mem : Ob} (∋ : Hom mem (PA ⊗₀ A)) : Type (o ⊔ ℓ) where
  field
    name  : ∀ {B} (m : Subobject (B ⊗₀ A)) → Hom B PA
    names : ∀ {B} (m : Subobject (B ⊗₀ A)) → is-pullback-along (m .map) (name m ⊗₁ id) ∋
    unique
      : ∀ {B} (m : Subobject (B ⊗₀ A)) {n : Hom B PA}
      → is-pullback-along (m .map) (n ⊗₁ id) ∋
      → n ≡ name m

record Power-object (A : Ob) : Type (o ⊔ ℓ) where
  field
    PA       : Ob
    ∋        : Subobject (PA ⊗₀ A)
    is-power : is-power-object A PA (∋ .map)

  open is-power-object is-power public

has-power-objects : Type _
has-power-objects = ∀ x → Power-object x
```

```agda
module Powers (pows : has-power-objects) where
  𝒫 : Ob → Ob
  𝒫 x = Power-object.PA (pows x)

  ∋ₘ : ∀ {x} → Subobject (𝒫 x ⊗₀ x)
  ∋ₘ = Power-object.∋ (pows _)

  membered : Ob → Ob
  membered x = ∋ₘ {x} .domain

  ∋ : ∀ {x} → Hom (membered x) (𝒫 x ⊗₀ x)
  ∋ = ∋ₘ .map

  name : ∀ {A B} (m : Subobject (B ⊗₀ A)) → Hom B (𝒫 A)
  name m = Power-object.name (pows _) m

  names-relation : ∀ {A B} (m : Subobject (B ⊗₀ A)) (h : Hom B (𝒫 A)) → Type (o ⊔ ℓ)
  names-relation m h = is-pullback-along (m .map) (h ⊗₁ id) ∋

  name-names : ∀ {A B} (m : Subobject (B ⊗₀ A)) → names-relation m (name m)
  name-names m = Power-object.names (pows _) m

  name-unique : ∀ {A B} (m : Subobject (B ⊗₀ A)) {h} → names-relation m h → h ≡ name m
  name-unique m = Power-object.unique (pows _) m

  names-relation→iso-pullback
    : ∀ {A B} (m : Subobject (B ⊗₀ A)) (h : Hom B (𝒫 A))
    → names-relation m h
    → m Sub.≅ pullback-subobject pullbacks (h ⊗₁ id) ∋ₘ
  names-relation→iso-pullback m h nm = Sub-antisym
    (record { map = im .to   ; sq = sym (Pullback.p₂∘universal (pullbacks _ _) ∙ introl refl) })
    (record { map = im .from ; sq = sym (is-pullback-along.p₁∘universal nm ∙ introl refl) }) where
    im = pullback-unique (nm .is-pullback-along.has-is-pb) (rotate-pullback (Pullback.has-is-pb (pullbacks _ _)))

  is-pullback→names-relation
    : ∀ {A B} (m : Subobject (B ⊗₀ A)) (h : Hom B (𝒫 A)) {t}
    → is-pullback (m .map) (h ⊗₁ id) t ∋
    → names-relation m h
  is-pullback→names-relation m h p = record { has-is-pb = p }

  name-ap-iso'
    : ∀ {A B} (m m' : Subobject (B ⊗₀ A))
    → (im : m .domain ≅ m' .domain)
    → m' .Sub.map ≡ m .Sub.map ∘ im .from
    → name m ≡ name m'
  name-ap-iso' m m' im coh = name-unique m' record
    { top       = name-names m .is-pullback-along.top ∘ im .from
    ; has-is-pb =
      let
        a = is-pullback-iso im (name-names m .is-pullback-along.has-is-pb)
        in subst-is-pullback (sym coh) refl refl refl a
    }

  name-ap-iso : ∀ {A B} (m m' : Subobject (B ⊗₀ A)) → m Sub.≅ m' → name m ≡ name m'
  name-ap-iso m m' im = name-ap-iso' m m'
    (make-iso (im .Sub.to .map) (im .Sub.from .map)
      (ap ≤-over.map (im .Sub.invl))
      (ap ≤-over.map (im .Sub.invr)))
    (introl refl ∙ im .Sub.from .sq)

  named : ∀ {A B} (h : Hom B (𝒫 A)) → Subobject (B ⊗₀ A)
  named h .Sub.domain = _
  named h .Sub.map    = Pullback.p₁ (pullbacks (h ⊗₁ id) ∋)
  named h .Sub.monic  = is-monic→pullback-is-monic
    (∋ₘ .monic)
    (rotate-pullback (Pullback.has-is-pb (pullbacks (h ⊗₁ id) ∋)))

  named-names : ∀ {A B} (h : Hom B (𝒫 A)) → names-relation (named h) h
  named-names h = record { Pullback (pullbacks (h ⊗₁ id) ∋) }

  name-named : ∀ {A B} (h : Hom B (𝒫 A)) → name (named h) ≡ h
  name-named h = sym (name-unique (named h) (named-names h))

  name-natural
    : ∀ {A B B'} (m : Subobject (B ⊗₀ A)) (g : Hom B' B)
    → name (pullback-subobject pullbacks (g ⊗₁ id) m) ≡ name m ∘ g
  name-natural m g = sym $ name-unique _ record
    { has-is-pb = subst-is-pullback refl
      (⟨⟩-unique _
        (pulll product.π₁∘factor ∙ pullr product.π₁∘factor ∙ pulll refl)
        (pulll product.π₂∘factor ∙ pullr product.π₂∘factor ∙ eliml refl))
      refl refl
      (rotate-pullback (pasting-left→outer-is-pullback
        (rotate-pullback (name-names m .is-pullback-along.has-is-pb))
        (pullbacks _ _ .Pullback.has-is-pb)
        ( pulll (sym (name-names m .is-pullback-along.square))
        ∙ pullr (pullbacks _ _ .Pullback.square)
        ∙ pulll refl)))
    }

  name-injective
    : ∀ {A B} (m m' : Subobject (B ⊗₀ A)) → name m ≡ name m' → m Sub.≅ m'
  name-injective m m' p = record
    { to   = record
      { map = name-names m' .is-pullback-along.universal p1
      ; sq  = sym (name-names m' .is-pullback-along.p₁∘universal ∙ introl refl)
      }
    ; from = record
      { map = name-names m .is-pullback-along.universal p2
      ; sq  = sym (name-names m .is-pullback-along.p₁∘universal ∙ introl refl)
      }
    ; inverses = record { invl = prop! ; invr = prop!  }
    }
    where abstract
      p1 : (name m' ⊗₁ id) ∘ m .map ≡ ∋ ∘ name-names m .is-pullback-along.top
      p1 = ap₂ _∘_ (ap (_⊗₁ id) (sym p)) refl ∙ name-names m .is-pullback-along.square

      p2 : (name m ⊗₁ id) ∘ m' .map ≡ ∋ ∘ name-names m' .is-pullback-along.top
      p2 = ap₂ _∘_ (ap (_⊗₁ id) p) refl ∙ name-names m' .is-pullback-along.square

  named-relation-injective
    : ∀ {A B} (m m' : Subobject (B ⊗₀ A)) {n}
    → names-relation m  n
    → names-relation m' n
    → m Sub.≅ m'
  named-relation-injective m m' p q = name-injective m m' $
    sym (name-unique m p) ∙ name-unique m' q

  graph : ∀ {A B} → Hom A B → Subobject (A ⊗₀ B)
  graph f .Sub.domain      = _
  graph f .Sub.map         = ⟨ id , f ⟩
  graph f .Sub.monic g h p =
    g                   ≡˘⟨ cancell π₁∘⟨⟩ ⟩
    π₁ ∘ ⟨ id , f ⟩ ∘ g ≡⟨ ap (π₁ ∘_) p ⟩
    π₁ ∘ ⟨ id , f ⟩ ∘ h ≡⟨ cancell π₁∘⟨⟩ ⟩
    h                   ∎

  diagonal : ∀ {A} → Subobject (A ⊗₀ A)
  diagonal = graph id

  singleton : ∀ {A} → Hom A (𝒫 A)
  singleton = name diagonal

  singleton-compose : ∀ {A B} (f : Hom A B) → names-relation (graph f) (singleton ∘ f)
  singleton-compose f =
    paste-is-pullback-along
      (record { has-is-pb = p })
      (name-names diagonal)
      (product.unique _
        (pulll π₁∘⟨⟩ ∙ pullr π₁∘⟨⟩ ∙ pulll refl)
        (pulll π₂∘⟨⟩ ∙ pullr π₂∘⟨⟩ ∙ eliml refl))
    where
      open is-pullback

      p : is-pullback ⟨ id , f ⟩ (f ⊗₁ id) f ⟨ id , id ⟩
      p .square       = sym $ ⟨⟩∘ _ ∙ sym (product.unique _
        (pulll π₁∘⟨⟩ ∙ pullr π₁∘⟨⟩ ∙ id-comm)
        (pulll π₂∘⟨⟩ ∙ pullr π₂∘⟨⟩))
      p .universal {p₁' = p₁'} p = π₁ ∘ p₁'
      p .p₁∘universal {p = p} =
        let
          a = sym (pulll (π₁∘⟨⟩)) ∙ ap (π₁ ∘_) p ∙ pulll π₁∘⟨⟩
          b = ap₂ _∘_ (introl refl) refl ∙ sym (pulll π₂∘⟨⟩) ∙ ap (π₂ ∘_) p ∙ pulll π₂∘⟨⟩
        in ⟨⟩∘ _
        ·· ap₂ ⟨_,_⟩ (idl _) (pulll refl ∙ a)
        ·· sym (product.unique _ refl b)
      p .p₂∘universal {p = p} = sym (extendl π₁∘⟨⟩) ∙ ap (π₁ ∘_) p ∙ pulll π₁∘⟨⟩ ∙ eliml refl
      p .unique p q   = sym (cancell π₁∘⟨⟩) ∙ ap (π₁ ∘_) p

  abstract
    singleton-monic : ∀ {A} → is-monic (singleton {A})
    singleton-monic g h x = done where
      rem₁ : names-relation (graph g) (singleton ∘ g)
      rem₁ = singleton-compose g

      rem₂ : names-relation (graph h) (singleton ∘ g)
      rem₂ = subst (names-relation (graph h)) (sym x) (singleton-compose h)

      rem₃ : graph g Sub.≅ graph h
      rem₃ = named-relation-injective _ _ rem₁ rem₂

      rem₃-is-id : rem₃ .Sub.to .map ≡ id
      rem₃-is-id =
        rem₃ .Sub.to .map                   ≡⟨ introl refl ⟩
        id ∘ rem₃ .Sub.to .map              ≡⟨ pushl (sym π₁∘⟨⟩) ⟩
        π₁ ∘ ⟨ id , h ⟩ ∘ rem₃ .Sub.to .map ≡⟨ ap (π₁ ∘_) (sym (rem₃ .Sub.to .sq) ∙ idl _) ⟩
        π₁ ∘ ⟨ id , g ⟩                     ≡⟨ π₁∘⟨⟩ ⟩
        id                                  ∎

      done : g ≡ h
      done = sym $
        h                                   ≡⟨ intror rem₃-is-id ⟩
        h ∘ rem₃ .Sub.to .map               ≡⟨ pushl (sym π₂∘⟨⟩) ⟩
        π₂ ∘ ⟨ id , h ⟩ ∘ rem₃ .Sub.to .map ≡⟨ ap (π₂ ∘_) (sym (rem₃ .Sub.to .sq) ∙ idl _) ⟩
        π₂ ∘ ⟨ id , g ⟩                     ≡⟨ π₂∘⟨⟩ ⟩
        g                                   ∎

  open Functor

  Power₁ : ∀ {A B} (f : Hom A B) → Subobject (𝒫 B ⊗₀ A)
  Power₁ f .Sub.domain = pullbacks (id ⊗₁ f) ∋ .Pullback.apex
  Power₁ f .Sub.map    = pullbacks (id ⊗₁ f) ∋ .Pullback.p₁
  Power₁ f .Sub.monic  = is-monic→pullback-is-monic (∋ₘ .monic) $
    rotate-pullback (pullbacks _ _ .Pullback.has-is-pb)

  -- Power : Functor (C ^op) C
  -- Power .F₀ A = 𝒫 A
  -- Power .F₁ h = name (Power₁ h)
  -- Power .F-id = name-ap-iso' _ _ id-iso (intror refl)
  --             ∙ name-named id
```
