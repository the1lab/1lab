<!--
```agda
{-# OPTIONS -vtc.decl:5 -vtactic.extensionality:10 #-}
open import 1Lab.Rewrite

open import Cat.Functor.Naturality
open import Cat.Functor.Hom
open import Cat.Diagram.Coend.Sets
open import Cat.Instances.Product
open import Cat.Diagram.Coend
open import Cat.Monoidal.Base
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as Fr
import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Monoidal.Instances.Day
  {ℓ} {C : Precategory ℓ ℓ} (cmon : Monoidal-category C)
  where
```

```agda
open Monoidal-category cmon
private module ⊗ = Fr -⊗-

open make-natural-iso
open Cowedge
open Functor
open Cat C
open _=>_
```

# The Day convolution product

```agda
module Day (X Y : ⌞ PSh ℓ C ⌟) where
  Day-diagram : Ob → Functor ((C ×ᶜ C) ^op ×ᶜ (C ×ᶜ C)) (Sets ℓ)
  ∣ Day-diagram c .F₀ ((c₁⁻ , c₂⁻) , c₁⁺ , c₂⁺) ∣    = Hom c (c₁⁺ ⊗ c₂⁺) × (X ʻ c₁⁻) × (Y ʻ c₂⁻)
  Day-diagram c .F₀ ((c₁⁻ , c₂⁻) , c₁⁺ , c₂⁺) .is-tr = hlevel!

  Day-diagram c .F₁ ((f⁻ , g⁻) , f⁺ , g⁺) (h , x , y) = (f⁺ ⊗₁ g⁺) ∘ h , X .F₁ f⁻ x , Y .F₁ g⁻ y

  Day-diagram c .F-id    = ext λ h x y → eliml (-⊗- .F-id) , X .F-id #ₚ x , Y .F-id #ₚ y
  Day-diagram c .F-∘ f g = ext λ h x y → pushl (-⊗- .F-∘ _ _) , X .F-∘ _ _ #ₚ _ , Y .F-∘ _ _ #ₚ _

  opaque
    Day-coend : (c : Ob) → Coend (Day-diagram c)
    Day-coend c = Set-coend (Day-diagram c)

  private module Day c = Coend (Day-coend c)
  open Day using (nadir) public

  opaque
    unfolding Day-coend

    day : {i a b : Ob} (h : Hom i (a ⊗ b)) (x : X ʻ a) (y : Y ʻ b) → ⌞ Day.nadir i ⌟
    day h x y = inc ((_ , _) , h , x , y)

    day-ap
      : {i a b : Ob} {h h' : Hom i (a ⊗ b)} {x x' : X ʻ a} {y y' : Y ʻ b}
      → h ≡ h' → x ≡ x' → y ≡ y' → day h x y ≡ day h' x' y'
    day-ap {a = a} {b} p q r i = inc ((a , b) , p i , q i , r i)

    day-apₘ : ∀ {i a b} {h h' : Hom i (a ⊗ b)} {x y} → h ≡ h' → day h x y ≡ day h' x y
    day-apₘ p = day-ap p refl refl

    day-glue
      : {i a b a' b' : Ob} {f : Hom a' a} {g : Hom b' b} {h : Hom i (a' ⊗ b')} {x : X ʻ a} {y : Y ʻ b}
      → {fgh : Hom i (a ⊗ b)} (p : fgh ≡ (f ⊗₁ g) ∘ h)
      → day fgh x y ≡ day h (X .F₁ f x) (Y .F₁ g y)
    day-glue {i} {a} {b} {a'} {b'} {f} {g} {h} {x} {y} {fgh} p =
      inc ((a , b) , fgh , x , y)                              ≡⟨ day-ap p (sym (X .F-id) #ₚ x) (sym (Y .F-id) #ₚ y) ⟩
      inc ((a , b) , (f ⊗₁ g) ∘ h , X .F₁ id x , Y .F₁ id y)   ≡⟨ Coeq.glue {f = dimapl (Day-diagram i)} {g = dimapr (Day-diagram i)} ((a , b) , (a' , b') , (f , g) , h , x , y) ⟩
      inc ((a' , b') , (id ⊗₁ id) ∘ h , X .F₁ f x , Y .F₁ g y) ≡⟨ day-apₘ (eliml ⊗.F-id) ⟩
      inc ((a' , b') , h , X .F₁ f x , Y .F₁ g y)              ∎

    factor : ∀ {i} (W : Cowedge (Day-diagram i)) → ⌞ Day.nadir i ⌟ → ⌞ W .nadir ⌟
    factor W = Day.factor _ W

    factor-day
      : ∀ {i a b} {W : Cowedge (Day-diagram i)} {h : Hom i (a ⊗ b)} {x : X ʻ a} {y : Y ʻ b}
      → factor W (day h x y) ≡rw W .ψ (a , b) (h , x , y)
    factor-day = idrw

  {-# REWRITE factor-day #-}

  Extensional-day-map
    : ∀ {i ℓ' ℓr} {C : Type ℓ'} {@(tactic hlevel-tactic-worker) c-set : is-set C}
    → ⦃ sf : ∀ {a b} → Extensional ((h : Hom i (a ⊗ b)) (x : X ʻ a) (y : Y ʻ b) → C) ℓr ⦄
    → Extensional (⌞ Day.nadir i ⌟ → C) (ℓ ⊔ ℓr)
  Extensional-day-map {i} {C = C} {c-set} ⦃ sf ⦄ = done where
    instance
      _ : H-Level C 2
      _ = basic-instance 2 c-set

    T : Type _
    T = {a b : Ob} (h : Hom i (a ⊗ b)) (x : X ʻ a) (y : Y ʻ b) → C

    unday : (⌞ Day.nadir i ⌟ → C) → T
    unday f h x y = f (day h x y)

    opaque
      unfolding Day-coend day

      to-p : ∀ {f g} → Path T (unday f) (unday g) → f ≡ g
      to-p p = ext λ (a , b) h x y i → p i {a} {b} h x y

    done : Extensional (⌞ Day.nadir i ⌟ → C) _
    done = injection→extensional (hlevel 2) to-p (Extensional-Π' ⦃ Extensional-Π' ⦃ sf ⦄ ⦄)

  private instance
    _ : ∀ {i ℓ'} {C : Type ℓ'} → Extensionality (⌞ Day.nadir i ⌟ → C)
    _ = record { lemma = quote Extensional-day-map }

  day-swap
    : ∀ {i a b a' b'} {f : Hom a' a} {g : Hom b' b} {h : Hom i (a' ⊗ b')}
        {a'' b''} {f' : Hom a'' a} {g' : Hom b'' b} {h' : Hom i (a'' ⊗ b'')}
        {x : X ʻ a} {y : Y ʻ b}
    → (f ⊗₁ g) ∘ h ≡ (f' ⊗₁ g') ∘ h'
    → day h (X .F₁ f x) (Y .F₁ g y) ≡ day h' (X .F₁ f' x) (Y .F₁ g' y)
  day-swap p = sym (day-glue refl) ·· day-apₘ p ·· day-glue refl

  Day-cowedge : ∀ {x} {y} → Hom y x → Cowedge (Day-diagram x)
  Day-cowedge {y = y} h .nadir = Day.nadir y
  Day-cowedge h .ψ (a , b) (f , x , y) = day (f ∘ h) x y
  Day-cowedge h .extranatural {a , b} {a' , b'} (f , g) = funext λ (i , x , y) →
    day (((f ⊗₁ g) ∘ i) ∘ h) (X .F₁ id x) (Y .F₁ id y) ≡⟨ day-ap refl (X .F-id #ₚ x) (Y .F-id #ₚ y) ⟩
    day (((f ⊗₁ g) ∘ i) ∘ h) x y                       ≡⟨ day-glue (sym (assoc _ _ _)) ⟩
    day (i ∘ h) (X .F₁ f x) (Y .F₁ g y)                ≡⟨ day-apₘ (introl ⊗.F-id ∙ assoc _ _ _) ⟩
    day (((id ⊗₁ id) ∘ i) ∘ h) (X .F₁ f x) (Y .F₁ g y) ∎

  Day : ⌞ PSh ℓ C ⌟
  Day .F₀ c = Day.nadir c
  Day .F₁ {x} {y} h v = factor (Day-cowedge h) v
  Day .F-id    = ext λ h x y → day-apₘ (idr h)
  Day .F-∘ f g = ext λ h x y → day-apₘ (assoc h g f)


module _ {X Y} where
  open Day X Y
    using    (day ; day-ap ; day-apₘ ; day-swap ; Extensional-day-map ; day-glue)
    renaming (factor to Day-rec)
    public

instance
  extensionality-day-map
    : ∀ {X Y i ℓ'} {C : Type ℓ'} → Extensionality (⌞ Day.nadir X Y i ⌟ → C)
  extensionality-day-map = record { lemma = quote Extensional-day-map }

open Day using (Day ; Day-diagram)

Day-bifunctor-cowedge
  : ∀ {X Y X' Y' : ⌞ PSh ℓ C ⌟} {i}
  → X => X'
  → Y => Y'
  → Cowedge (Day-diagram X Y i)
Day-bifunctor-cowedge {X} {Y} {X'} {Y'} {i} F G = go where
  private module D = Day X' Y'
  go : Cowedge (Day-diagram X Y i)
  go .nadir           = D.nadir i
  go .ψ c (h , x , y) = D.day h (F .η _ x) (G .η _ y)
  go .extranatural (f , g) = ext λ h x y →
    D.day ((f ⊗₁ g) ∘ h)   (F .η _ (X .F₁ id x))   (G .η _ (Y .F₁ id y))   ≡⟨ D.day-ap refl (F .is-natural _ _ id #ₚ _) (G .is-natural _ _ id #ₚ _) ⟩
    D.day ((f ⊗₁ g) ∘ h)   (X' .F₁ id (F .η _ x))  (Y' .F₁ id (G .η _ y))  ≡⟨ D.day-swap (extendl (eliml ⊗.F-id ∙ intror ⊗.F-id)) ⟩
    D.day ((id ⊗₁ id) ∘ h) (X' .F₁ f (F .η _ x))   (Y' .F₁ g (G .η _ y))   ≡˘⟨ D.day-ap refl (F .is-natural _ _ f #ₚ _) (G .is-natural _ _ g #ₚ _) ⟩
    D.day ((id ⊗₁ id) ∘ h) (F .η _ (X .F₁ f x))    (G .η _ (Y .F₁ g y))    ∎

Day-map : ∀ {X X' Y Y'} (F : X => X') (G : Y => Y') → Day X Y => Day X' Y'
Day-map F G .η i = Day-rec (Day-bifunctor-cowedge F G)
Day-map F G .is-natural x y f = trivial!

Day-bifunctor : Functor (PSh ℓ C ×ᶜ PSh ℓ C) (PSh ℓ C)
Day-bifunctor .F₀ (X , Y) = Day X Y
Day-bifunctor .F₁ (F , G) = Day-map F G
Day-bifunctor .F-id    = trivial!
Day-bifunctor .F-∘ f g = trivial!

module _ (X : ⌞ PSh ℓ C ⌟) where
  idr-to-cowedge : ∀ x → Cowedge (Day-diagram X (よ₀ C Unit) x)
  idr-to-cowedge i .nadir = X # i
  idr-to-cowedge i .ψ (a , b) (h , x , y) = X .F₁ (ρ← ∘ (id ⊗₁ y) ∘ h) x
  idr-to-cowedge i .extranatural {a , b} {a' , b'} (f , g) = ext λ h x y →
    X .F₁ (ρ← ∘ (id ⊗₁ y ∘ id) ∘ (f ⊗₁ g) ∘ h) (X .F₁ id x) ≡⟨ ap₂ (X .F₁) (ap (ρ← ∘_) (⊗.pulll (ap₂ _,_ (idl f) (ap (_∘ g) (idr y))))) refl ⟩
    X .F₁ (ρ← ∘ (f ⊗₁ y ∘ g) ∘ h) (X .F₁ id x)              ≡⟨ ap₂ (X .F₁) (ap (ρ← ∘_) (⊗.pushl (ap₂ _,_ (intror refl) (introl refl)))) refl ⟩
    X .F₁ (ρ← ∘ (f ⊗₁ id) ∘ (id ⊗₁ y ∘ g) ∘ h) (X .F₁ id x) ≡⟨ ap₂ (X .F₁) (extendl (unitor-r .Isoⁿ.from .is-natural a a' f)) refl ⟩
    X .F₁ (f ∘ ρ← ∘ (id ⊗₁ y ∘ g) ∘ h) (X .F₁ id x)         ≡⟨ X .F-∘ _ _ #ₚ _ ⟩
    X .F₁ (ρ← ∘ (id ⊗₁ y ∘ g) ∘ h) (X .F₁ f (X .F₁ id x))   ≡⟨ ap₂ (X .F₁) (ap (ρ← ∘_) (ap₂ _∘_ refl (introl ⊗.F-id))) (ap (X .F₁ f) (X .F-id #ₚ x)) ⟩
    X .F₁ (ρ← ∘ (id ⊗₁ y ∘ g) ∘ (id ⊗₁ id) ∘ h) (X .F₁ f x) ∎

  Day-idr : Day X (よ₀ C Unit) ≅ⁿ X
  Day-idr = to-natural-iso mk where
    mk : make-natural-iso (Day X (よ₀ C Unit)) X
    mk .eta x   = Day-rec (idr-to-cowedge x)
    mk .inv x a = day ρ→ a id
    mk .eta∘inv x = ext λ a → ap₂ (X .F₁) (ap (ρ← ∘_) (eliml ⊗.F-id) ∙ unitor-r .Isoⁿ.invr ηₚ _) refl ∙ (X .F-id #ₚ a)
    mk .inv∘eta i = ext λ h x y →
      day ρ→ (X .F₁ (ρ← ∘ (id ⊗₁ y) ∘ h) x) id          ≡⟨ day-ap refl refl (introl refl) ⟩
      day ρ→ (X .F₁ (ρ← ∘ (id ⊗₁ y) ∘ h) x) (id ∘ id)   ≡⟨ day-swap (sym (unitor-r .Isoⁿ.to .is-natural _ _ _) ∙ cancell (unitor-r .Isoⁿ.invl ηₚ _)) ⟩
      day h (X .F₁ id x) (id ∘ y)                       ≡⟨ day-ap refl (X .F-id #ₚ x) (idl y) ⟩
      day h x y                                         ∎
    mk .natural x y f = ext λ h x y →
      X .F₁ f (X .F₁ (ρ← ∘ (id ⊗₁ y) ∘ h) x) ≡⟨ sym (X .F-∘ _ _) #ₚ _ ⟩
      X .F₁ ((ρ← ∘ (id ⊗₁ y) ∘ h) ∘ f) x     ≡⟨ ap₂ (X .F₁) (pullr (pullr refl)) refl ⟩
      X .F₁ (ρ← ∘ (id ⊗₁ y) ∘ h ∘ f) x       ∎

module _ (Y : ⌞ PSh ℓ C ⌟) where
  idl-to-cowedge : ∀ x → Cowedge (Day-diagram (よ₀ C Unit) Y x)
  idl-to-cowedge i .nadir = Y # i
  idl-to-cowedge i .ψ (a , b) (h , x , y) = Y .F₁ (λ← ∘ (x ⊗₁ id) ∘ h) y
  idl-to-cowedge i .extranatural {a , b} {a' , b'} (f , g) = ext λ h x y →
       ap₂ (Y .F₁) (ap (λ← ∘_) (⊗.extendl (ap₂ _,_ (ap (_∘ f) (idr x) ∙ introl refl) id-comm-sym)) ∙ extendl (unitor-l .Isoⁿ.from .is-natural _ _ _)) (Y .F-id #ₚ y)
    ·· (Y .F-∘ _ _ #ₚ y)
    ·· ap₂ (Y .F₁) (ap (λ← ∘_) (ap₂ _∘_ refl (introl ⊗.F-id))) refl

  Day-idl : Day (よ₀ C Unit) Y ≅ⁿ Y
  Day-idl = to-natural-iso mk where
    mk : make-natural-iso (Day (よ₀ C Unit) Y) Y
    mk .eta x = Day-rec (idl-to-cowedge x)
    mk .inv x a = day λ→ id a
    mk .eta∘inv x = ext λ a → ap₂ (Y .F₁) (ap (λ← ∘_) (eliml ⊗.F-id) ∙ unitor-l .Isoⁿ.invr ηₚ _) refl ∙ (Y .F-id #ₚ a)
    mk .inv∘eta i = ext λ h x y →
      day λ→ id (Y .F₁ (λ← ∘ (x ⊗₁ id) ∘ h) y)        ≡⟨ day-ap refl (introl refl) refl ⟩
      day λ→ (id ∘ id) (Y .F₁ (λ← ∘ (x ⊗₁ id) ∘ h) y) ≡⟨ day-swap (sym (unitor-l .Isoⁿ.to .is-natural _ _ _) ∙ cancell (unitor-l .Isoⁿ.invl ηₚ _)) ⟩
      day h (id ∘ x) (Y .F₁ id y)                     ≡⟨ day-ap refl (idl x) (Y .F-id #ₚ y) ⟩
      day h x y                                       ∎
    mk .natural = λ x y f → ext λ h x y →
      Y .F₁ f (Y .F₁ (λ← ∘ (x ⊗₁ id) ∘ h) y) ≡˘⟨ Y .F-∘ _ _ #ₚ _ ⟩
      Y .F₁ ((λ← ∘ (x ⊗₁ id) ∘ h) ∘ f) y     ≡⟨ ap₂ (Y .F₁) (pullr (pullr refl)) refl ⟩
      Y .F₁ (λ← ∘ (x ⊗₁ id) ∘ h ∘ f) y       ∎

module _ (X Y Z : ⌞ PSh ℓ C ⌟) where
  assoc-to₀ : ∀ i {a b} (h : Hom i (a ⊗ b)) (z : Z ʻ b) → Cowedge (Day-diagram X Y a)
  assoc-to₀ i h z .nadir = Day.nadir X (Day Y Z) i
  assoc-to₀ i h z .ψ (a' , b') (h' , x , y) = day (α→ _ _ _ ∘ (h' ⊗₁ id) ∘ h) x (day id y z)
  assoc-to₀ i h z .extranatural (f , g) = ext λ h' x y →
    day (α→ _ _ _ ∘ ((f ⊗₁ g) ∘ h' ⊗₁ id) ∘ h) (X .F₁ id x) (day id (Y .F₁ id y) z)  ≡⟨ day-ap (ap (α→ _ _ _ ∘_) (⊗.pushl (ap₂ _,_ refl (introl refl)))) (X .F-id #ₚ x) (day-ap refl (Y .F-id #ₚ y) refl) ⟩
    day (α→ _ _ _ ∘ ((f ⊗₁ g) ⊗₁ id) ∘ (h' ⊗₁ id) ∘ h) x (day id y z)                ≡⟨ day-apₘ (extendl (associator .Isoⁿ.to .is-natural _ _ _)) ⟩
    day ((f ⊗₁ (g ⊗₁ id)) ∘ α→ _ _ _ ∘ (h' ⊗₁ id) ∘ h) x (day id y z)                ≡⟨ day-glue refl ⟩
    day (α→ _ _ _ ∘ (h' ⊗₁ id) ∘ h) (X .F₁ f x) (day (id ∘ (g ⊗₁ id)) y z)           ≡⟨ day-ap (ap (α→ _ _ _ ∘_) (ap (_∘ h) (ap₂ _⊗₁_ (introl ⊗.F-id) refl))) refl (day-apₘ id-comm-sym ·· day-glue refl ·· day-ap refl refl (Z .F-id #ₚ z)) ⟩
    day (α→ _ _ _ ∘ ((id ⊗₁ id) ∘ h' ⊗₁ id) ∘ h) (X .F₁ f x) (day id (Y .F₁ g y) z)  ∎

  assoc-to-cowedge : ∀ i → Cowedge (Day-diagram (Day X Y) Z i)
  assoc-to-cowedge i .nadir = Day.nadir X (Day Y Z) i
  assoc-to-cowedge i .ψ (a , b) (h , x , y) = Day-rec (assoc-to₀ i h y) x
  assoc-to-cowedge i .extranatural (f , g) = ext λ h h' x y z →
    day (α→ _ _ _ ∘ (h' ∘ id ⊗₁ id) ∘ (f ⊗₁ g) ∘ h) x (day id y (Z .F₁ id z))   ≡⟨ day-ap (ap (α→ _ _ _ ∘_) (⊗.extendl (ap₂ _,_ (ap (_∘ f) (idr h') ∙ introl ⊗.F-id) id-comm-sym))) refl (day-ap refl refl (Z .F-id #ₚ z)) ⟩
    day (α→ _ _ _ ∘ ((id ⊗₁ id) ⊗₁ g) ∘ (h' ∘ f ⊗₁ id) ∘ h) x (day id y z)      ≡⟨ day-apₘ (extendl (associator .Isoⁿ.to .is-natural _ _ _)) ⟩
    day ((id ⊗₁ (id ⊗₁ g)) ∘ α→ _ _ _ ∘ (h' ∘ f ⊗₁ id) ∘ h) x (day id y z)      ≡⟨ day-glue refl ⟩
    day (α→ _ _ _ ∘ (h' ∘ f ⊗₁ id) ∘ h) (X .F₁ id x) (day (id ∘ (id ⊗₁ g)) y z) ≡⟨ day-ap (ap (α→ _ _ _ ∘_) (ap₂ _∘_ refl (introl ⊗.F-id))) (X .F-id #ₚ x) (day-glue id-comm-sym ∙ day-ap refl (Y .F-id #ₚ y) refl) ⟩
    day (α→ _ _ _ ∘ (h' ∘ f ⊗₁ id) ∘ (id ⊗₁ id) ∘ h) x (day id y (Z .F₁ g z))   ∎

  assoc-from₀ : ∀ i {a b} (h : Hom i (a ⊗ b)) (x : X ʻ a) → Cowedge (Day-diagram Y Z b)
  assoc-from₀ i h x .nadir = Day.nadir (Day X Y) Z i
  assoc-from₀ i h x .ψ (a' , b') (h' , y , z) = day (α← _ _ _ ∘ (id ⊗₁ h') ∘ h) (day id x y) z
  assoc-from₀ i h x .extranatural (f , g) = ext λ h' y z →
    day (α← _ _ _ ∘ (id ⊗₁ ((f ⊗₁ g) ∘ h')) ∘ h) (day id x (Y .F₁ id y)) (Z .F₁ id z) ≡⟨ day-ap (extendl (pushr (ap₂ _⊗₁_ (introl refl) refl ∙ ⊗.F-∘ _ _) ·· pullr refl ·· extendl (associator .Isoⁿ.from .is-natural _ _ _))) (day-ap refl refl (Y .F-id #ₚ y)) (Z .F-id #ₚ z) ⟩
    day (((id ⊗₁ f) ⊗₁ g) ∘ (α← _ _ _ ∘ (id ⊗₁ h')) ∘ h) (day id x y) z               ≡⟨ day-glue refl ⟩
    day ((α← _ _ _ ∘ (id ⊗₁ h')) ∘ h) (day (id ∘ (id ⊗₁ f)) x y) (Z .F₁ g z)          ≡⟨ day-ap (pullr (ap (_∘ h) (ap₂ _⊗₁_ refl (introl ⊗.F-id)))) (day-glue id-comm-sym ∙ day-ap refl (X .F-id #ₚ x) refl) refl ⟩
    day (α← _ _ _ ∘ (id ⊗₁ ((id ⊗₁ id) ∘ h')) ∘ h) (day id x (Y .F₁ f y)) (Z .F₁ g z) ∎

  assoc-from-cowedge : ∀ i → Cowedge (Day-diagram X (Day Y Z) i)
  assoc-from-cowedge i .nadir = Day.nadir (Day X Y) Z i
  assoc-from-cowedge i .ψ (a , b) (h , x , y) = Day-rec (assoc-from₀ i h x) y
  assoc-from-cowedge i .extranatural (f , g) = ext λ h x h' y z →
    day (α← _ _ _ ∘ (id ⊗₁ h' ∘ id) ∘ (f ⊗₁ g) ∘ h) (day id (X .F₁ id x) y) z   ≡⟨ day-ap (ap (α← _ _ _ ∘_) (⊗.extendl (ap₂ _,_ id-comm-sym (ap (_∘ g) (idr h') ∙ introl ⊗.F-id)))) (day-ap refl (X .F-id #ₚ _) refl) refl ⟩
    day (α← _ _ _ ∘ (f ⊗₁ (id ⊗₁ id)) ∘ (id ⊗₁ h' ∘ g) ∘ h) (day id x y) z      ≡⟨ day-apₘ (extendl (associator .Isoⁿ.from .is-natural _ _ _)) ⟩
    day (((f ⊗₁ id) ⊗₁ id) ∘ α← _ _ _ ∘ (id ⊗₁ h' ∘ g) ∘ h) (day id x y) z      ≡⟨ day-glue refl ⟩
    day (α← _ _ _ ∘ (id ⊗₁ h' ∘ g) ∘ h) (day (id ∘ (f ⊗₁ id)) x y) (Z .F₁ id z) ≡⟨ day-ap (ap (α← _ _ _ ∘_) (ap₂ _∘_ refl (introl ⊗.F-id))) (day-glue id-comm-sym ∙ day-ap refl refl (Y .F-id #ₚ y)) (Z .F-id #ₚ z) ⟩
    day (α← _ _ _ ∘ (id ⊗₁ h' ∘ g) ∘ (id ⊗₁ id) ∘ h) (day id (X .F₁ f x) y) z   ∎

  Day-assoc : Day (Day X Y) Z ≅ⁿ Day X (Day Y Z)
  Day-assoc = to-natural-iso mk where
    mk : make-natural-iso (Day (Day X Y) Z) (Day X (Day Y Z))
    mk .eta x = Day-rec (assoc-to-cowedge x)
    mk .inv x = Day-rec (assoc-from-cowedge x)
    mk .eta∘inv x = ext λ h x h' y z →
      day (α→ _ _ _ ∘ (id ⊗₁ id) ∘ α← _ _ _ ∘ (id ⊗₁ h') ∘ h) x (day id y z) ≡⟨ day-apₘ (pulll (elimr ⊗.F-id) ∙ cancell (associator .Isoⁿ.invl ηₚ _)) ⟩
      day ((id ⊗₁ h') ∘ h) x (day id y z)                                    ≡⟨ day-glue refl ⟩
      day h (X .F₁ id x) (day (id ∘ h') y z)                                 ≡⟨ day-ap refl (X .F-id #ₚ x) (day-apₘ (idl h')) ⟩
      day h x (day h' y z)                                                   ∎
    mk .inv∘eta x = ext λ h h' x y z →
      day (α← _ _ _ ∘ (id ⊗₁ id) ∘ α→ _ _ _ ∘ (h' ⊗₁ id) ∘ h) (day id x y) z ≡⟨ day-apₘ (pulll (elimr ⊗.F-id) ∙ cancell (associator .Isoⁿ.invr ηₚ _)) ⟩
      day ((h' ⊗₁ id) ∘ h) (day id x y) z                                    ≡⟨ day-glue refl ⟩
      day h (day (id ∘ h') x y) (Z .F₁ id z)                                 ≡⟨ day-ap refl (day-apₘ (idl h')) (Z .F-id #ₚ z) ⟩
      day h (day h' x y) z                                                   ∎
    mk .natural x y f = ext λ h h' x y z →
      day ((α→ _ _ _ ∘ (h' ⊗₁ id) ∘ h) ∘ f) x (day id y z) ≡⟨ day-ap (pullr (pullr refl)) refl refl ⟩
      day (α→ _ _ _ ∘ (h' ⊗₁ id) ∘ h ∘ f) x (day id y z)   ∎

private module M = Monoidal-category

abstract
  day-triangle : ∀ {A B : ⌞ PSh ℓ C ⌟} → Day-map (Day-idr A .Isoⁿ.to) idnt ∘nt Day-assoc A (よ₀ C Unit) B .Isoⁿ.from ≡ Day-map idnt (Day-idl B .Isoⁿ.to)
  day-triangle {A} {B} = ext λ i h x h' y z →
    day (α← _ _ _ ∘ (id ⊗₁ h') ∘ h) (A .F₁ (ρ← ∘ (id ⊗₁ y) ∘ id) x) z         ≡⟨ day-ap refl (ap₂ (A .F₁) (ap (ρ← ∘_) (idr _)) refl) (sym (B .F-id #ₚ z)) ⟩
    day (α← _ _ _ ∘ (id ⊗₁ h') ∘ h) (A .F₁ (ρ← ∘ (id ⊗₁ y)) x) (B .F₁ id z)   ≡⟨ sym (day-glue refl) ⟩
    day ((ρ← ∘ (id ⊗₁ y) ⊗₁ id) ∘ α← _ _ _ ∘ (id ⊗₁ h') ∘ h) x z              ≡⟨ day-apₘ (⊗.pushl (ap₂ _,_ refl (introl refl))) ⟩
    day ((ρ← ⊗₁ id) ∘ ((id ⊗₁ y) ⊗₁ id) ∘ α← _ _ _ ∘ (id ⊗₁ h') ∘ h) x z      ≡⟨ day-apₘ (ap₂ _∘_ refl (extendl (sym (associator .Isoⁿ.from .is-natural _ _ _)))) ⟩
    day ((ρ← ⊗₁ id) ∘ α← _ _ _ ∘ (id ⊗₁ (y ⊗₁ id)) ∘ (id ⊗₁ h') ∘ h) x z      ≡⟨ day-apₘ (pulll triangle) ⟩
    day ((id ⊗₁ λ←) ∘ (id ⊗₁ (y ⊗₁ id)) ∘ (id ⊗₁ h') ∘ h) x z                 ≡⟨ day-apₘ (pulll (sym (⊗.F-∘ _ _)) ∙ pulll (sym (⊗.F-∘ _ _)) ∙ ap (_∘ h) (ap₂ _⊗₁_ (eliml (eliml refl)) (pullr refl))) ⟩
    day ((id ⊗₁ (λ← ∘ (y ⊗₁ id) ∘ h')) ∘ h) x z                               ≡⟨ day-glue refl ⟩
    day h (A .F₁ id x) (B .F₁ (λ← ∘ (y ⊗₁ id) ∘ h') z)                        ≡⟨ day-ap refl (A .F-id #ₚ x) refl ⟩
    day h x (B .F₁ (λ← ∘ (y ⊗₁ id) ∘ h') z)                                   ∎

  day-pentagon
    : ∀ {A B C D : ⌞ PSh ℓ C ⌟}
    → Day-map (Day-assoc A B C .Isoⁿ.from) idnt
      ∘nt Day-assoc A (Day B C) D .Isoⁿ.from
      ∘nt Day-map idnt (Day-assoc B C D .Isoⁿ.from)
    ≡ Day-assoc (Day A B) C D .Isoⁿ.from
      ∘nt Day-assoc A B (Day C D) .Isoⁿ.from
  day-pentagon {D = D} = ext λ i h a h' b h'' c d →
    let
      it =
        (α← _ _ _ ⊗₁ id) ∘ α← _ _ _ ∘ (id ⊗₁ α← _ _ _ ∘ (id ⊗₁ h'') ∘ h') ∘ h         ≡⟨ ap₂ _∘_ refl (ap₂ _∘_ refl (⊗.pushl (ap₂ _,_ (intror refl) refl))) ⟩
        (α← _ _ _ ⊗₁ id) ∘ α← _ _ _ ∘ (id ⊗₁ α← _ _ _) ∘ (id ⊗₁ (id ⊗₁ h'') ∘ h') ∘ h ≡⟨ pulll refl ∙ extendl (pullr refl ∙ pentagon) ⟩
        α← _ _ _ ∘ α← _ _ _ ∘ (id ⊗₁ (id ⊗₁ h'') ∘ h') ∘ h                            ≡⟨ ap₂ _∘_ refl (ap₂ _∘_ refl (⊗.pushl (ap₂ _,_ (intror refl) refl))) ⟩
        α← _ _ _ ∘ α← _ _ _ ∘ (id ⊗₁ (id ⊗₁ h'')) ∘ (id ⊗₁ h') ∘ h                    ≡⟨ ap₂ _∘_ refl (extendl (associator .Isoⁿ.from .is-natural _ _ _)) ⟩
        α← _ _ _ ∘ ((id ⊗₁ id) ⊗₁ h'') ∘ α← _ _ _ ∘ (id ⊗₁ h') ∘ h                    ≡⟨ ap₂ _∘_ refl (ap₂ _∘_ (ap (_⊗₁ h'') ⊗.F-id) refl) ⟩
        (α← _ _ _ ∘ (id ⊗₁ h'') ∘ α← _ _ _ ∘ (id ⊗₁ h') ∘ h)                          ∎
    in
      day (α← _ _ _ ∘ (id ⊗₁ (α← _ _ _) ∘ (id ⊗₁ h'') ∘ h') ∘ h) (day (α← _ _ _ ∘ (id ⊗₁ id) ∘ id) (day id a b) c) d  ≡⟨ day-ap refl (day-ap (elimr (eliml ⊗.F-id) ∙ introl refl) refl refl) (sym (D .F-id #ₚ d)) ⟩
      day (α← _ _ _ ∘ (id ⊗₁ (α← _ _ _) ∘ (id ⊗₁ h'') ∘ h') ∘ h) (day (id ∘ α← _ _ _) (day id a b) c) (D .F₁ id d)    ≡⟨ sym (day-glue refl) ⟩
      day ((α← _ _ _ ⊗₁ id) ∘ α← _ _ _ ∘ (id ⊗₁ (α← _ _ _) ∘ (id ⊗₁ h'') ∘ h') ∘ h) (day id (day id a b) c) d         ≡⟨ day-apₘ it ⟩
      day (α← _ _ _ ∘ (id ⊗₁ h'') ∘ α← _ _ _ ∘ (id ⊗₁ h') ∘ h) (day id (day id a b) c) d                              ∎

Day-monoidal : Monoidal-category (PSh ℓ C)
Day-monoidal .M.-⊗-      = Day-bifunctor
Day-monoidal .M.Unit     = よ₀ C Unit
Day-monoidal .M.unitor-l = to-natural-iso mk-λ where
  mk-λ : make-natural-iso _ _
  mk-λ .eta x = Day-idl x .Isoⁿ.from
  mk-λ .inv x = Day-idl x .Isoⁿ.to
  mk-λ .eta∘inv x = Day-idl x .Isoⁿ.invr
  mk-λ .inv∘eta x = Day-idl x .Isoⁿ.invl
  mk-λ .natural x y f = trivial!
Day-monoidal .M.unitor-r = to-natural-iso mk-ρ where
  mk-ρ : make-natural-iso _ _
  mk-ρ .eta x = Day-idr x .Isoⁿ.from
  mk-ρ .inv x = Day-idr x .Isoⁿ.to
  mk-ρ .eta∘inv x = Day-idr x .Isoⁿ.invr
  mk-ρ .inv∘eta x = Day-idr x .Isoⁿ.invl
  mk-ρ .natural x y f = trivial!
Day-monoidal .M.associator = to-natural-iso mk-α where
  mk-α : make-natural-iso _ _
  mk-α .eta (x , y , z) = Day-assoc x y z .Isoⁿ.to
  mk-α .inv (x , y , z) = Day-assoc x y z .Isoⁿ.from
  mk-α .eta∘inv (x , y , z) = Day-assoc x y z .Isoⁿ.invl
  mk-α .inv∘eta (x , y , z) = Day-assoc x y z .Isoⁿ.invr
  mk-α .natural x y f = trivial!
Day-monoidal .M.triangle {A} {B} = day-triangle
Day-monoidal .M.pentagon {A} {B} {C} {D} = day-pentagon
```
