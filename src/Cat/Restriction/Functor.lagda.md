<!--
```agda
open import Cat.Restriction.Base
open import Cat.Prelude

import Cat.Restriction.Reasoning
```
-->

```agda
module Cat.Restriction.Functor where
```

<!--
```agda
open Functor
```
-->

# Restriction functors

A functor $F : \cC \to \cD$ between [restriction categories] is a
**restriction functor** if $F (\restrict{f}) = \restrict{(F f)}$.

[restriction categories]: Cat.Restriction.Base.html

```agda
is-restriction-functor
  : ∀ {oc ℓc od ℓd} {C : Precategory oc ℓc} {D : Precategory od ℓd}
  → (F : Functor C D)
  → (C↓ : Restriction-category C)
  → (D↓ : Restriction-category D)
  → Type _
is-restriction-functor {C = C} {D = D} F C↓ D↓ =
  ∀ {x y} (f : C.Hom x y) → F .F₁ (f C.↓) ≡ (F .F₁ f D.↓)
  where
    module C = Cat.Restriction.Reasoning C↓
    module D = Cat.Restriction.Reasoning D↓
```

The identity functor is a restriction functor, and restriction functors
are closed under composition.

```agda
Id-restriction
  : ∀ {oc ℓc} {C : Precategory oc ℓc} {C↓ : Restriction-category C}
  → is-restriction-functor Id C↓ C↓
Id-restriction f = refl

F∘-restriction
  : ∀ {oc ℓc od ℓd oe ℓe}
  → {C : Precategory oc ℓc} {D : Precategory od ℓd} {E : Precategory oe ℓe}
  → {C↓ : Restriction-category C}
  → {D↓ : Restriction-category D}
  → {E↓ : Restriction-category E}
  → (F : Functor D E) (G : Functor C D)
  → is-restriction-functor F D↓ E↓ → is-restriction-functor G C↓ D↓
  → is-restriction-functor (F F∘ G) C↓ E↓
F∘-restriction F G F↓ G↓ f = ap (F .F₁) (G↓ f) ∙ F↓ (G .F₁ f)
```

# Properties of restriction functors

Let $F : \cC \to \cD$ be a restriction functor. Note that $F$ preserves
[total morphisms] and [restriction idempotents].

[total morphisms]: Cat.Restriction.Reasoning.html#total-morphisms
[restriction idempotents]: Cat.Restriction.Reasoning.html#restriction-idempotents

<!--
```agda
module is-restriction-functor
  {oc ℓc od ℓd} {C : Precategory oc ℓc} {D : Precategory od ℓd}
  (F : Functor C D)
  (C↓ : Restriction-category C)
  (D↓ : Restriction-category D)
  (F↓ : is-restriction-functor F C↓ D↓)
  where
  private
    module C = Cat.Restriction.Reasoning C↓
    module D = Cat.Restriction.Reasoning D↓
```
-->

```agda
  F-total : ∀ {x y} {f : C.Hom x y} → C.is-total f → D.is-total (F .F₁ f)
  F-total {f = f} f-total = sym (F↓ f) ·· ap (F .F₁) f-total ·· F .F-id

  F-restrict-idem
    : ∀ {x} {f : C.Hom x x}
    → C.is-restriction-idempotent f
    → D.is-restriction-idempotent (F .F₁ f)
  F-restrict-idem {f = f} f-ridem =
    F .F₁ f D.↓   ≡˘⟨ F↓ f ⟩
    F .F₁ (f C.↓) ≡⟨ ap (F .F₁) f-ridem ⟩
    F .F₁ f ∎
```

Furthermore, if $g$ refines $f$, then $F(g)$ refines $F(f)$.

```agda
  F-≤ : ∀ {x y} {f g : C.Hom x y} → f C.≤ g → (F .F₁ f) D.≤ (F .F₁ g)
  F-≤ {f = f} {g = g} f≤g =
    F .F₁ g D.∘ F .F₁ f D.↓   ≡⟨ ap (F .F₁ g D.∘_) (sym (F↓ f)) ⟩
    F .F₁ g D.∘ F .F₁ (f C.↓) ≡⟨ sym (F .F-∘ g (f C.↓)) ⟩
    F .F₁ (g C.∘ f C.↓) ≡⟨ ap (F .F₁) f≤g ⟩
    F .F₁ f ∎
```

Restriction functors also preserve restricted isomorphisms.

```agda
  F-restricted-inverses
    : ∀ {x y} {f : C.Hom x y} {g : C.Hom y x}
    → C.restricted-inverses f g
    → D.restricted-inverses (F .F₁ f) (F .F₁ g)
  F-restricted-inverses {f = f} {g = g} fg-inv = record
    { ↓-invl =
      F .F₁ f D.∘ F .F₁ g ≡˘⟨ F .F-∘ f g ⟩
      F .F₁ (f C.∘ g)     ≡⟨ ap (F .F₁) fg-inv.↓-invl ⟩
      F .F₁ (g C.↓)       ≡⟨ F↓ g ⟩
      F .F₁ g D.↓         ∎
    ; ↓-invr =
      F .F₁ g D.∘ F .F₁ f ≡˘⟨ F .F-∘ g f ⟩
      F .F₁ (g C.∘ f)     ≡⟨ ap (F .F₁) fg-inv.↓-invr ⟩
      F .F₁ (f C.↓)       ≡⟨ F↓ f ⟩
      F .F₁ f D.↓         ∎
    }
    where module fg-inv = C.restricted-inverses fg-inv

  F-restricted-invertible
    : ∀ {x y} {f : C.Hom x y}
    → C.is-restricted-invertible f
    → D.is-restricted-invertible (F .F₁ f)
  F-restricted-invertible f-inv = record
    { ↓-inv = F .F₁ f-inv.↓-inv
    ; ↓-inverses = F-restricted-inverses f-inv.↓-inverses
    }
    where module f-inv = C.is-restricted-invertible f-inv

  F-↓≅ : ∀ {x y} → x C.↓≅ y → F .F₀ x D.↓≅ F .F₀ y
  F-↓≅ f = record
    { ↓-to = F .F₁ f.↓-to
    ; ↓-from = F .F₁ f.↓-from
    ; ↓-inverses = F-restricted-inverses f.↓-inverses
    }
    where module f = C._↓≅_ f
```
