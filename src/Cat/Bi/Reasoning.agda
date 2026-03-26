open import Cat.Functor.Naturality
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as Fr
import Cat.Reasoning as Cr

module Cat.Bi.Reasoning {o ℓ ℓ'} (C : Prebicategory o ℓ ℓ') where

open Prebicategory C public hiding (module Hom)

module Hom {a b} = Cr (Hom a b) hiding (_∘_ ; Hom ; Ob)
module ⊗ {a b c} = compose {a} {b} {c}
module ▶ {a b c} {f} = Fr (postaction C {a} {b} {c} f)
module ◀ {a b c} {f} = Fr (preaction C {a} {b} {c} f)

open Hom hiding (id ; to ; from)
open Cr._≅_

open _=>_

private variable
  X Y Z : Ob
  f g h k : X ↦ Y
  α β γ : f ⇒ g

ρ≅ : f ≅ f ⊗ id
ρ≅ = isoⁿ→iso unitor-r _

λ≅ : f ≅ id ⊗ f
λ≅ = isoⁿ→iso unitor-l _

α≅ : (f ⊗ g) ⊗ h ≅ f ⊗ (g ⊗ h)
α≅ = isoⁿ→iso associator _

module ρ≅ {x y} {f : x ↦ y} = _≅_ (ρ≅ {f = f})
module λ≅ {x y} {f : x ↦ y} = _≅_ (λ≅ {f = f})
module α≅ {w x y z} {f : y ↦ z} {g : x ↦ y} {h : w ↦ x} = _≅_ (α≅ {f = f} {g = g} {h = h})

▶-distribr : h ▶ (α ∘ β) ≡ h ▶ α ∘ h ▶ β
▶-distribr = ▶.F-∘ _ _

◀-distribl : (α ∘ β) ◀ h ≡ α ◀ h ∘ β ◀ h
◀-distribl = ◀.F-∘ _ _

▶-assoc : ∀ {c} → postaction C {c = c} (f ⊗ g) ≅ⁿ postaction C f F∘ postaction C g
▶-assoc {f = f} {g = g} = to-natural-iso record
  { eta = λ x → α→ (f , g , x)
  ; inv = λ x → α← (f , g , x)
  ; eta∘inv = λ _ → α≅ .invl
  ; inv∘eta = λ _ → α≅ .invr
  ; natural = λ _ _ _ →
       ap₂ _∘_ (ap (f ▶_) (compose.rmap-◆ _) ∙ compose.rmap-◆ _) refl
    ∙∙ sym (α→nat _ _ _)
    ∙∙ ap₂ _∘_ refl (eliml (◀.elim (◀.eliml refl ∙ ▶.elim refl)))
  }

◀-assoc : ∀ {c} → preaction C {c = c} (f ⊗ g) ≅ⁿ preaction C g F∘ preaction C f
◀-assoc {f = f} {g = g} = to-natural-iso record
  { eta = λ x → α← (x , f , g)
  ; inv = λ x → α→ (x , f , g)
  ; eta∘inv = λ _ → α≅ .invr
  ; inv∘eta = λ _ → α≅ .invl
  ; natural = λ _ _ _ →
       ap₂ _∘_ (ap (_◀ g) (compose.lmap-◆ _) ∙ compose.lmap-◆ _) refl
    ∙∙ sym (α←nat _ _ _)
    ∙∙ ap₂ _∘_ refl (▶.elimr (◀.eliml refl ∙ ▶.elim refl))
  }

◀-▶-comm : preaction C f F∘ postaction C g ≅ⁿ postaction C g F∘ preaction C f
◀-▶-comm {f = f} {g = g} = to-natural-iso record
  { eta = λ x → α→ (g , x , f)
  ; inv = λ x → α← (g , x , f)
  ; eta∘inv = λ _ → α≅ .invl
  ; inv∘eta = λ _ → α≅ .invr
  ; natural = λ _ _ _ →
       ap₂ _∘_ (ap (g ▶_) (compose.lmap-◆ _) ∙ compose.rmap-◆ _) refl
    ∙∙ sym (α→nat _ _ _)
    ∙∙ ap₂ _∘_ refl (▶.elimr refl ∙ ap (_◀ f) (◀.eliml refl))
  }

α→◀ : α→ _ ∘ ((α ◆ β) ◀ f) ≡ (α ◆ β ◀ _) ∘ α→ _
α→◀ = cdr (compose.lmap-◆ _) ∙ α→nat _ _ _ ∙ cdar ▶.⟨ ▶.elimr refl ⟩

module ▶-assoc {a b c} {f : b ↦ c} {g : a ↦ b} {x} = Isoⁿ (▶-assoc  {f = f} {g = g} {c = x})
module ◀-assoc {a b c} {f : b ↦ c} {g : a ↦ b} {x} = Isoⁿ (◀-assoc  {f = f} {g = g} {c = x})
module ◀-▶-comm {a b c} {f : b ↦ c} {g : a ↦ b}    = Isoⁿ (◀-▶-comm {f = f} {g = g})

-- Proofs of triangle-α→, pentagon-α→, triangle-λ←, and λ←≡ρ← are taken from those in
-- Cat.Monoidal.Base.  The proof of triangle-λ← involves a prism diagram which is
-- shown in that module.
--
-- Below is the corresponding prism diagram for the triangle-ρ← identity.
-- \[\begin{tikzcd}
-- 	& {A\otimes (B\otimes (1 \otimes 1))} \\
-- 	{A\otimes ((B\otimes 1)\otimes 1)} & {(A \otimes B)\otimes (1 \otimes 1)} & {A\otimes (B \otimes 1)} \\
-- 	& {((A\otimes B)\otimes 1)\otimes 1} \\
-- 	{(A\otimes (B \otimes 1))\otimes 1} && {(A\otimes B)\otimes 1}
-- 	\arrow["{\alpha^{-1}}", dashed, from=1-2, to=2-2]
-- 	\arrow["{{A\otimes (B\otimes \lambda)}}", from=1-2, to=2-3]
-- 	\arrow["{{A\otimes \alpha}}", from=2-1, to=1-2]
-- 	\arrow["{{A\otimes (\rho \otimes 1)}}"'{pos=0.2}, curve={height=6pt}, from=2-1, to=2-3]
-- 	\arrow["{\alpha^{-1}}", from=2-1, to=4-1]
-- 	\arrow["{\alpha^{-1}}", dashed, from=2-2, to=3-2]
-- 	\arrow["{\alpha^{-1}}"', from=2-3, to=4-3]
-- 	\arrow["{{\rho \otimes 1}}"', dashed, from=3-2, to=4-3]
-- 	\arrow["{{\alpha^{-1} \otimes 1}}"', dashed, from=4-1, to=3-2]
-- 	\arrow["{{(A \otimes \rho)\otimes 1}}"', from=4-1, to=4-3]
-- \end{tikzcd}\]

triangle-inv : α← (f , id , g) ∘ f ▶ λ→ g ≡ ρ→ f ◀ g
triangle-inv {f = f} {g = g} = rswizzle
  (sym $ lswizzle (sym $ triangle f g) (◀.F-map-iso ρ≅ .invl))
  (▶.F-map-iso λ≅ .invr)

triangle-α→ : (f ▶ λ← g) ∘ α→ _ ≡ ρ← f ◀ g
triangle-α→ = rswizzle (sym $ triangle _ _) (α≅ .invr)

pentagon-α→
  : f ▶ α→ (g , h , k) ∘ α→ (f , g ⊗ h , k) ∘ α→ (f , g , h) ◀ k
  ≡ α→ (f , g , h ⊗ k) ∘ α→ (f ⊗ g , h , k)
pentagon-α→ = inverse-unique refl refl
  (▶.F-map-iso (α≅ Iso⁻¹) ∙Iso α≅ Iso⁻¹ ∙Iso ◀.F-map-iso (α≅ Iso⁻¹))
  (α≅ Iso⁻¹ ∙Iso α≅ Iso⁻¹)
  (sym (assoc _ _ _) ∙ pentagon _ _ _ _)

triangle-ρ← : ρ← (f ⊗ g) ∘ α← (f , g , id) ≡ f ▶ ρ← g
triangle-ρ← = push-eqⁿ (unitor-r ni⁻¹) $
  ◀-distribl ∙ ap to (Iso-prism base sq1 sq2 sq3)
  where
    base : ▶.F-map-iso α≅ ∙Iso ▶.F-map-iso (▶.F-map-iso (λ≅ Iso⁻¹))
         ≡ ▶.F-map-iso (◀.F-map-iso (ρ≅ Iso⁻¹))
    base = ≅-path (▶.collapse triangle-α→)

    sq1 : ▶.F-map-iso α≅ ∙Iso α≅ Iso⁻¹ ∙Iso α≅ Iso⁻¹ ≡ α≅ Iso⁻¹ ∙Iso ◀.F-map-iso (α≅ Iso⁻¹)
    sq1 = ≅-path (rswizzle (sym (pentagon _ _ _ _) ∙ assoc _ _ _)
      (▶.annihilate (α≅ .invr)))

    sq2 : ▶.F-map-iso (▶.F-map-iso (λ≅ Iso⁻¹)) ∙Iso α≅ Iso⁻¹
        ≡ (α≅ Iso⁻¹ ∙Iso α≅ Iso⁻¹) ∙Iso ◀.F-map-iso (ρ≅ Iso⁻¹)
    sq2 = ≅-path $ ▶-assoc .from .is-natural _ _ _ ∙ sym (pulll (triangle _ _))

    sq3 : ▶.F-map-iso (◀.F-map-iso (ρ≅ Iso⁻¹)) ∙Iso α≅ Iso⁻¹
        ≡ α≅ Iso⁻¹ ∙Iso ◀.F-map-iso (▶.F-map-iso (ρ≅ Iso⁻¹))
    sq3 = ≅-path (ap₂ _∘_ refl (ap (_ ▶_) (compose.lmap-◆ _) ∙ compose.rmap-◆ _) ∙ α←nat _ _ _ ∙ ap₂ _∘_ (▶.elimr refl ∙ ap (_◀ id) (◀.eliml refl)) refl)

triangle-ρ→ : ρ→ (f ⊗ g) ≡ α← (f , g , id) ∘ f ▶ ρ→ g
triangle-ρ→ {f = f} {g = g} =
  ρ→ (f ⊗ g)                                           ≡⟨ intror (sym ▶-distribr ∙ ▶.elim (ρ≅ .invr)) ⟩
  ρ→ (f ⊗ g) ∘ f ▶ ρ← g ∘ f ▶ ρ→ g                     ≡⟨ refl⟩∘⟨ pushl (sym triangle-ρ←) ⟩
  ρ→ (f ⊗ g) ∘ ρ← (f ⊗ g) ∘ α← (f , g , id) ∘ f ▶ ρ→ g ≡⟨ cancell (ρ≅ .invl) ⟩
  α← (f , g , id) ∘ f ▶ ρ→ g                           ∎

triangle-λ← : λ← (f ⊗ g) ∘ α→ (id , f , g) ≡ λ← f ◀ g
triangle-λ← {f = f} {g = g} = push-eqⁿ (unitor-l ni⁻¹) $
  ▶-distribr ∙ ap to (Iso-prism base sq1 sq2 sq3)
  where
    base : ◀.F-map-iso (α≅ Iso⁻¹) ∙Iso ◀.F-map-iso (◀.F-map-iso (ρ≅ Iso⁻¹))
         ≡ ◀.F-map-iso (▶.F-map-iso (λ≅ Iso⁻¹))
    base = ≅-path (◀.collapse (triangle _ _))

    sq1 : ◀.F-map-iso (α≅ Iso⁻¹) ∙Iso α≅ ∙Iso α≅ ≡ α≅ ∙Iso ▶.F-map-iso α≅
    sq1 = ≅-path (rswizzle (sym pentagon-α→ ∙ assoc _ _ _)
      (◀.annihilate (α≅ .invl)))

    sq2 : ◀.F-map-iso (◀.F-map-iso (ρ≅ Iso⁻¹)) ∙Iso α≅
        ≡ (α≅ ∙Iso α≅) ∙Iso ▶.F-map-iso (λ≅ Iso⁻¹)
    sq2 = ≅-path $ ◀-assoc .from .is-natural _ _ _ ∙ sym (pulll triangle-α→)

    sq3 : ◀.F-map-iso (▶.F-map-iso (λ≅ Iso⁻¹)) ∙Iso α≅
        ≡ α≅ ∙Iso ▶.F-map-iso (◀.F-map-iso (λ≅ Iso⁻¹))
    sq3 = ≅-path (ap₂ _∘_ refl (ap (_◀ _) (compose.rmap-◆ _) ∙ compose.lmap-◆ _) ∙ α→nat _ _ _ ∙ ap₂ _∘_ (◀.eliml refl ∙ ap (id ▶_) (▶.elimr refl)) refl)

triangle-λ→ : λ→ (f ⊗ g) ≡ α→ (id , f , g) ∘ λ→ f ◀ g
triangle-λ→ {f = f} {g = g} =
  λ→ (f ⊗ g)                                           ≡⟨ intror (◀.annihilate (λ≅ .invr)) ⟩
  λ→ (f ⊗ g) ∘ λ← f ◀ g ∘ λ→ f ◀ g                     ≡⟨ refl⟩∘⟨ pushl (sym triangle-λ←) ⟩
  λ→ (f ⊗ g) ∘ λ← (f ⊗ g) ∘ α→ (id , f , g) ∘ λ→ f ◀ g ≡⟨ cancell (λ≅ .invl) ⟩
  α→ (id , f , g) ∘ λ→ f ◀ g                           ∎

λ←≡ρ← : ∀ {A} → λ← (id {A}) ≡ ρ← id
λ←≡ρ← = push-eqⁿ (unitor-r ni⁻¹) $
  (λ← id ◀ id)       ≡˘⟨ triangle-λ← ⟩
  λ← _ ∘ α→ _        ≡⟨ (insertl (λ≅ .invl) ∙∙ refl⟩∘⟨ sym (λ←nat _) ∙∙ cancell (λ≅ .invl)) ⟩∘⟨refl ⟩
  (id ▶ λ← _) ∘ α→ _ ≡⟨ triangle-α→ ⟩
  (ρ← id ◀ id)       ∎

λ→≡ρ→ : ∀ {A} → λ→ (id {A}) ≡ ρ→ id
λ→≡ρ→ =
  λ→ id                 ≡⟨ intror (ρ≅ .invr) ⟩
  λ→ id ∘ ρ← id ∘ ρ→ id ≡˘⟨ refl⟩∘⟨ λ←≡ρ← ⟩∘⟨refl ⟩
  λ→ id ∘ λ← id ∘ ρ→ id ≡⟨ cancell (λ≅ .invl) ⟩
  ρ→ id                 ∎
