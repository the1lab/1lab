open import 1Lab.Prelude

open import Data.List.Membership
open import Data.Finset.Base
open import Data.Fin.Finite
open import Data.Nat.Base
open import Data.Sum.Base
open import Data.Dec

import 1Lab.Reflection

open 1Lab.Reflection using (Idiom-TC ; lit ; nat ; con₀ ; List ; [] ; _∷_)

module Data.Finset.Properties where

private variable
  ℓ ℓ' ℓ'' : Level
  A B C : Type ℓ

∈ᶠˢ-map : (f : A → B) {x : B} (xs : Finset A) → x ∈ mapᶠˢ f xs → ∃[ (y , _) ∈ fibreᵢ f x ] y ∈ xs
∈ᶠˢ-map f {x} xs w = Finset-elim-prop (λ xs → x ∈ mapᶠˢ f xs → ∃[ (y , _) ∈ fibreᵢ f x ] y ∈ xs)
  (λ w → absurd (¬mem-[] w))
  (λ y ind → ∈ᶠˢ-split (λ { p → inc ((y , symᵢ p) , hereₛ) }) λ w → case ind w of λ x p h → inc ((x , p) , thereₛ h))
  xs w

map-∈ᶠˢ : ∀ (f : A → B) {x} (xs : Finset A) → x ∈ᶠˢ xs → f x ∈ᶠˢ mapᶠˢ f xs
map-∈ᶠˢ f {x} = ∈ᶠˢ-elim (λ xs _ → f x ∈ᶠˢ map f xs) hereₛ (λ q → thereₛ)

map-∈ᶠˢ' : ∀ (f : A → B) {x y} (xs : Finset A) → f x ≡ y → x ∈ᶠˢ xs → y ∈ᶠˢ mapᶠˢ f xs
map-∈ᶠˢ' f {x} {y} xs p = ∈ᶠˢ-elim (λ xs _ → y ∈ᶠˢ map f xs) (hereₛ' (Id≃path.from (sym p))) (λ q → thereₛ) xs

filter-∈ᶠˢ : ∀ {P : A → Type ℓ} ⦃ d : ∀ {x} → Dec (P x) ⦄ {x : A} xs → x ∈ᶠˢ xs → P x → x ∈ᶠˢ filter P xs
filter-∈ᶠˢ {P = P} ⦃ d ⦄ {x} xs mem px = ∈ᶠˢ-elim (λ xs _ → x ∈ᶠˢ filter P xs)
  (λ {xs} → case d {x} return (λ p → x ∈ᶠˢ cons-if p x (filter P xs)) of λ { (yes _) → hereₛ ; (no ¬px) → absurd (¬px px)})
  (λ {y} {xs} q ind → case d {y} return (λ p → x ∈ᶠˢ cons-if p y (filter P xs)) of λ { (yes _) → thereₛ ind ; (no ¬px) → ind })
  xs mem

∈ᶠˢ-filter : ∀ {P : A → Type ℓ} ⦃ d : ∀ {x} → Dec (P x) ⦄ {x : A} xs → x ∈ᶠˢ filter P xs → x ∈ xs × ∥ P x ∥
∈ᶠˢ-filter {P = P} ⦃ d = d ⦄ {x = x} = Finset-elim-prop (λ xs → x ∈ filter P xs → x ∈ xs × ∥ P x ∥)
  (λ w → absurd (¬mem-[] w))
  (λ y {xs} ind → case d {y} return (λ p → x ∈ᶠˢ cons-if p y (filter P xs) → x ∈ (y ∷ xs) × ∥ P x ∥) of λ where
    (yes py) → ∈ᶠˢ-split (λ p → hereₛ' p , inc (substᵢ P (symᵢ p) py)) λ w → case ind w of λ a b → thereₛ a , inc b
    (no ¬py) q → case ind q of λ a b → thereₛ a , inc b)

uncons : (x : A) (xs : Finset A) → x ∈ᶠˢ xs → xs ≡ x ∷ xs
uncons x = Finset-elim-prop _ (λ x → absurd (¬mem-[] x)) λ y {xs} ih → ∈ᶠˢ-split
  (λ { reflᵢ → sym (∷-dup _ _) })
  (λ w → ap (y ∷_) (ih w) ∙ ∷-swap _ _ _)

unionl-∈ᶠˢ : (x : A) (xs ys : Finset A) → x ∈ᶠˢ xs → x ∈ᶠˢ (xs <> ys)
unionl-∈ᶠˢ x xs ys p = ∈ᶠˢ-elim (λ xs _ → x ∈ᶠˢ (xs <> ys)) hereₛ (λ q x → thereₛ x) xs p

unionr-∈ᶠˢ : (x : A) (xs ys : Finset A) → x ∈ᶠˢ ys → x ∈ᶠˢ (xs <> ys)
unionr-∈ᶠˢ x xs ys p = Finset-elim-prop (λ xs → x ∈ᶠˢ (xs <> ys)) p (λ x p → thereₛ p) xs

∈ᶠˢ-union : (x : A) (xs ys : Finset A) → x ∈ᶠˢ (xs <> ys) → ∥ (x ∈ᶠˢ xs) ⊎ (x ∈ᶠˢ ys) ∥
∈ᶠˢ-union x = Finset-elim-prop _ (λ ys w → inc (inr w)) λ x {xs} ind ys →
  ∈ᶠˢ-split (λ p → inc (inl (hereₛ' p)))
    λ w → case ind ys w of λ where
      (inl h) → inc (inl (thereₛ h))
      (inr t) → inc (inr t)

sigma-∈ᶠˢ
  : ∀ {ℓ ℓ'} {A : Type ℓ} {P : A → Type ℓ'} {x y}
  → ∀ (f : ∀ x → Finset (P x)) xs
  → x ∈ᶠˢ xs → y ∈ᶠˢ f x → (x , y) ∈ᶠˢ sigma xs f
sigma-∈ᶠˢ {P = P} {x = x₀} {y = y₀} f xs mx my = ∈ᶠˢ-elim (λ xs _ → (y : P x₀) → y ∈ f x₀ → (x₀ , y) ∈ sigma xs f)
  (λ {xs} y ym → unionl-∈ᶠˢ (x₀ , y) (map (x₀ ,_) (f x₀)) (sigma xs f) (map-∈ᶠˢ (x₀ ,_) (f x₀) ym))
  (λ {y} {xs} q ind py ym → unionr-∈ᶠˢ (x₀ , py) (map (y ,_) (f y)) (sigma xs f) (ind py ym))
  xs mx y₀ my

∈ᶠˢ-sigma
  : ∀ {ℓ ℓ'} {A : Type ℓ} {P : A → Type ℓ'} {x y} (f : ∀ x → Finset (P x)) xs
  → (x , y) ∈ᶠˢ sigma xs f → x ∈ xs × y ∈ f x
∈ᶠˢ-sigma {P = P} {x = x} {y} f = Finset-elim-prop (λ xs → (x , y) ∈ᶠˢ sigma xs f → x ∈ xs × y ∈ f x)
  (λ w → absurd (¬mem-[] w))
  (λ x' {xs} ind w → case ∈ᶠˢ-union (x , y) (map (x' ,_) (f x')) (sigma xs f) w of λ where
    (inl w) → case ∈ᶠˢ-map (x' ,_) (f x') w of λ px' pf mem →
      let (p , q) = id-Σ (symᵢ pf) in
      Jᵢ (λ x' p → ∀ px' (q : Id-over P p y px') → px' ∈ᶠˢ f x' → (x ∈ᶠˢ (x' ∷ xs)) × (y ∈ᶠˢ f x))
         (λ px'' → Jᵢ (λ px'' _ → px'' ∈ f x → (x ∈ (x ∷ xs)) × (y ∈ f x)) (hereₛ ,_))
         p px' q mem
    (inr w) → case ind w of λ h1 h2 → thereₛ h1 , h2)

intersection-∈ᶠˢ : ⦃ _ : Discrete A ⦄ (x : A) (xs ys : Finset A) → x ∈ xs → x ∈ ys → x ∈ intersection xs ys
intersection-∈ᶠˢ x xs ys mxs mys = ∈ᶠˢ-elim (λ xs _ → x ∈ intersection xs ys)
  (λ {xs} → caseᵈ x ∈ ys return (λ p → x ∈ cons-if p x (intersection xs ys)) of λ where
    (yes _)   → hereₛ
    (no ¬mys) → absurd (¬mys mys))
  (λ {y} {xs} w q → there-cons-if (holds? _) y x (intersection xs ys) q)
  xs mxs

∈ᶠˢ-intersection : ⦃ d : Discrete A ⦄ (x : A) (xs ys : Finset A) → x ∈ intersection xs ys → (x ∈ xs) × (x ∈ ys)
∈ᶠˢ-intersection x xs ys w = Finset-elim-prop (λ xs → x ∈ intersection xs ys → x ∈ xs × x ∈ ys)
  (λ w → absurd (¬mem-[] w))
  (λ y {tl} ind → caseᵈ (y ∈ ys) return (λ p → x ∈ cons-if p y (intersection tl ys) → x ∈ (y ∷ tl) × x ∈ ys) of λ where
    (yes q) → ∈ᶠˢ-split (λ p → substᵢ (λ e → x ∈ᶠˢ (e ∷ tl)) p hereₛ , substᵢ (_∈ᶠˢ ys) (symᵢ p) q) λ w → case ind w of λ a b → thereₛ a , b
    (no ¬p) mem → case ind mem of λ a b → thereₛ a , b)
  xs w

∈ᶠˢ-from-list : ∀ {x : A} {xs} → x ∈ᶠˢ from-list xs → ∥ x ∈ₗ xs ∥
∈ᶠˢ-from-list {xs = []} p = absurd (¬mem-[] p)
∈ᶠˢ-from-list {xs = x ∷ xs} = ∈ᶠˢ-split (λ p → inc (here p)) (λ w → there <$> ∈ᶠˢ-from-list w)

from-list-∈ᶠˢ : ∀ {x : A} {xs} → x ∈ₗ xs → x ∈ᶠˢ from-list xs
from-list-∈ᶠˢ (here p)  = hereₛ' p
from-list-∈ᶠˢ (there x) = thereₛ (from-list-∈ᶠˢ x)

instance
  Dec-All
    : ∀ {P : A → Type ℓ} ⦃ _ : ∀ {x} → H-Level (P x) 1 ⦄ ⦃ d : ∀ {x} → Dec (P x) ⦄ {xs : Finset A}
    → Dec (All P xs)
  Dec-All {P = P} {xs} = Finset-elim-prop (λ xs → Dec (All P xs)) (yes all-nil)
    (λ { x (yes xs) → caseᵈ P x of λ { (yes x) → yes (all-cons x xs) ; (no ¬x) → no (λ xxs → ¬x (from-all _ xxs hereₛ) )}
       ; _ (no ¬xs) → no (λ xxs → ¬xs (to-all _ (λ x w → from-all _ xxs (thereₛ w))))
       })
    xs

abstract
  subset→is-union : (xs ys : Finset A) → xs ⊆ ys → ys ≡ (xs <> ys)
  subset→is-union = Finset-elim-prop _ (λ ys p → refl) λ x {xs} ih ys sube →
    ys             ≡⟨ uncons x ys (sube x hereₛ) ⟩
    x ∷ ys         ≡⟨ ap (x ∷_) (ih ys λ x x∈xs → sube x (thereₛ x∈xs)) ⟩
    x ∷ (xs <> ys) ∎

  finset-ext : {xs ys : Finset A} → xs ⊆ ys → ys ⊆ xs → xs ≡ ys
  finset-ext {xs = xs} {ys} p1 p2 =
    let
      p : xs ≡ (ys <> xs)
      p = subset→is-union ys xs p2

      q : ys ≡ (xs <> ys)
      q = subset→is-union xs ys p1
    in p ∙∙ union-comm ys xs ∙∙ sym q

instance
  Discrete-Finset : ⦃ _ : Discrete A ⦄ → Discrete (Finset A)
  Discrete-Finset {x = xs} {ys} = case holds? (All (_∈ᶠˢ ys) xs × All (_∈ᶠˢ xs) ys) of λ where
    (yes (s1 , s2)) → yes $ finset-ext (λ a → from-all _ s1) (λ a → from-all _ s2)
    (no ¬sub)       → no λ p → ¬sub (to-all xs (λ a → subst (a ∈_) p) , to-all ys (λ a → subst (a ∈_) (sym p)))

Finite→finset : Finite A → Finset A
Finite→finset {A = A} = ∥-∥-rec-set (hlevel 2) (λ l → from-list (Listing.univ l)) const where abstract
  const : (x y : Listing A) → from-list (Listing.univ x) ≡ from-list (Listing.univ y)
  const x y = finset-ext
    (λ a _ → from-list-∈ᶠˢ (Listing.find y a))
    (λ a _ → from-list-∈ᶠˢ (Listing.find x a))

Finite→finset-has : (x : Finite A) (y : A) → y ∈ᶠˢ Finite→finset x
Finite→finset-has = elim! λ x y → from-list-∈ᶠˢ (Listing.find x y)

abstract
  map-union
    : {A : Type ℓ} {B : Type ℓ'} (xs ys : Finset A) (f : A → B)
    → map f (xs <> ys) ≡ map f xs <> map f ys
  map-union = Finset-elim-prop _ (λ ys f → refl) (λ x ih ys f → ap (f x ∷_) (ih ys f))

  map-map
    : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (xs : Finset A) (f : B → C) (g : A → B)
    → map f (map g xs) ≡ map (f ∘ g) xs
  map-map = Finset-elim-prop _ (λ f g → refl) (λ x ih f g → ap (f (g x) ∷_) (ih f g))

private
  powercons : A → Finset (Finset A) → Finset (Finset A)
  powercons x xs = xs <> map (x ∷_) xs

private abstract
  powercons-dup : (x : A) (xs : Finset (Finset A)) → powercons x (powercons x xs) ≡ powercons x xs
  powercons-dup x xs =
    (xs <> map (x ∷_) xs) <> ⌜ map (x ∷_) (xs <> map (x ∷_) xs) ⌝              ≡⟨ ap! (map-union xs (map (x ∷_) xs) (x ∷_)) ⟩
    (xs <> map (x ∷_) xs) <> (map (x ∷_) xs <> ⌜ map (x ∷_) (map (x ∷_) xs) ⌝) ≡⟨ ap! (map-map xs (x ∷_) (x ∷_) ∙ ap (λ e → map e xs) (funext λ a → ∷-dup x a)) ⟩
    (xs <> map (x ∷_) xs) <> ⌜ map (x ∷_) xs <> map (x ∷_) xs ⌝                ≡⟨ ap! (union-idem (map (x ∷_) xs)) ⟩
    (xs <> map (x ∷_) xs) <> map (x ∷_) xs                                     ≡˘⟨ union-assoc xs (map (x ∷_) xs) (map (x ∷_) xs) ⟩
    xs <> map (x ∷_) xs <> map (x ∷_) xs                                       ≡⟨ ap (xs <>_) (union-idem (map (x ∷_) xs)) ⟩
    xs <> map (x ∷_) xs                                                        ∎

  powercons-swap : (x : A) (y : A) (xs : Finset (Finset A)) → powercons x (powercons y xs) ≡ powercons y (powercons x xs)
  powercons-swap x y xs =
    let
      p1 =
        (xs <> map (y ∷_) xs) <> ⌜ map (x ∷_) (xs <> map (y ∷_) xs) ⌝            ≡⟨ ap! (map-union xs (map (y ∷_) xs) (x ∷_)) ⟩
        (xs <> map (y ∷_) xs) <> (map (x ∷_) xs <> map (x ∷_) (map (y ∷_) xs))   ≡˘⟨ union-assoc xs (map (y ∷_) xs) _ ⟩
        xs <> (map (y ∷_) xs <> (map (x ∷_) xs) <> (map (x ∷_) (map (y ∷_) xs))) ≡⟨⟩
        xs <> map (y ∷_) xs <> map (x ∷_) xs <> map (x ∷_) (map (y ∷_) xs)       ∎

      p2 =
        (xs <> map (x ∷_) xs) <> ⌜ map (y ∷_) (xs <> map (x ∷_) xs) ⌝          ≡⟨ ap! (map-union xs (map (x ∷_) xs) (y ∷_)) ⟩
        (xs <> map (x ∷_) xs) <> (map (y ∷_) xs) <> map (y ∷_) (map (x ∷_) xs) ≡˘⟨ union-assoc xs (map (x ∷_) xs) _ ⟩
        xs <> map (x ∷_) xs <> map (y ∷_) xs <> map (y ∷_) (map (x ∷_) xs)     ≡⟨ ap (xs <>_) (union-assoc (map (x ∷_) xs) (map (y ∷_) xs) _) ⟩
        xs <> ((map (x ∷_) xs <> map (y ∷_) xs)) <> map (y ∷_) (map (x ∷_) xs) ≡⟨ ap (xs <>_) (ap₂ _<>_ (union-comm (map (x ∷_) xs) (map (y ∷_) xs)) (map-map xs (y ∷_) (x ∷_) ∙∙ ap (λ e → map e xs) (funext (∷-swap y x)) ∙∙ sym (map-map xs (x ∷_) (y ∷_)))) ⟩
        xs <> ((map (y ∷_) xs <> map (x ∷_) xs)) <> map (x ∷_) (map (y ∷_) xs) ≡⟨ ap (xs <>_) (sym (union-assoc (map (y ∷_) xs) (map (x ∷_) xs) _)) ⟩
        xs <> map (y ∷_) xs <> map (x ∷_) xs <> map (x ∷_) (map (y ∷_) xs)     ∎
    in p1 ∙ sym p2

powerset : Finset A → Finset (Finset A)
powerset []                = [] ∷ []
powerset (x ∷ xs)          = powercons x (powerset xs)
powerset (∷-dup x xs i)    = powercons-dup x (powerset xs) i
powerset (∷-swap x y xs i) = powercons-swap x y (powerset xs) i
powerset (squash x y p q i j) = hlevel 2 (powerset x) (powerset y) (λ i → powerset (p i)) (λ i → powerset (q i)) i j

∈ᶠˢ-powerset : (xs ys : Finset A) → ys ∈ powerset xs → ys ⊆ xs
∈ᶠˢ-powerset = Finset-elim-prop _
  (λ ys → ∈ᶠˢ-split (λ { reflᵢ a p → p }) λ m → absurd (¬mem-[] m))
  λ x {xs} ih ys mem → case ∈ᶠˢ-union _ (powerset xs) (map (x ∷_) (powerset xs)) mem of λ where
    (inl h) y m → thereₛ (ih ys h y m)
    (inr t) y m → case ∈ᶠˢ-map (x ∷_) (powerset xs) t of λ where
      ys' p n → ∈ᶠˢ-split {P = λ _ → y ∈ᶠˢ (x ∷ xs)} hereₛ'
        (λ w → thereₛ (ih ys' n y w))
        (substᵢ (y ∈ᶠˢ_) (symᵢ p) m)

delete : ⦃ _ : Discrete A ⦄ → A → Finset A → Finset A
delete x xs = filter (x ≠_) xs

powerset-∈ᶠˢ : ⦃ _ : Discrete A ⦄ (xs ys : Finset A) → ys ⊆ xs → ys ∈ powerset xs
powerset-∈ᶠˢ = Finset-elim-prop _
  (λ ys sube → hereₛ' (Id≃path.from (finset-ext sube (λ a m → absurd (¬mem-[] m)))))
  λ x {xs} ih ys sube → caseᵈ x ∈ ys of λ where
    (yes x∈ys) →
      let
        ys' = delete x ys

        p : x ∷ ys' ≡ ys
        p = finset-ext
          (λ a m → ∈ᶠˢ-split {P = λ _ → a ∈ ys} (λ p → substᵢ (_∈ ys) (symᵢ p) x∈ys) (λ w → case ∈ᶠˢ-filter {P = x ≠_} ys w of λ p _ → p) m)
          λ a b → case a ≡ᵢ? x of λ { (yes p) → hereₛ' p ; (no ¬q) → thereₛ (filter-∈ᶠˢ ys b λ a → ¬q (Id≃path.from (sym a))) }

        s' : delete x ys ⊆ xs
        s' a m =
          let (m' , a≠x) = ∈ᶠˢ-filter ys m
           in ∈ᶠˢ-split {P = λ _ → a ∈ xs} (λ p → case a≠x of λ ¬x=a → absurd (¬x=a (Id≃path.to (symᵢ p)))) (λ w → w) (sube a m')
      in unionr-∈ᶠˢ _ (powerset xs) _ $ map-∈ᶠˢ' (x ∷_) (powerset xs) p (ih ys' s')
    (no x∉ys) → unionl-∈ᶠˢ _ (powerset xs) _ $ ih ys λ a m → ∈ᶠˢ-split {P = λ _ → a ∈ xs}
      (λ a=x → absurd (x∉ys (substᵢ (_∈ ys) a=x m))) (λ w → w) (sube a m)
