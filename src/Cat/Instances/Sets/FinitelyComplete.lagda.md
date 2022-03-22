```agda
open import Cat.Diagram.Limit.Finite
open import Cat.Prelude

module Cat.Instances.Sets.FinitelyComplete {ℓ} where
```

<!--
```agda
open import Cat.Diagram.Equaliser (Sets ℓ)
open import Cat.Diagram.Pullback (Sets ℓ)
open import Cat.Diagram.Terminal (Sets ℓ)
open import Cat.Diagram.Product (Sets ℓ)
open import Cat.Reasoning (Sets ℓ)

private variable
  A B : Set ℓ
  f g : Hom A B

open Terminal
open is-product
open Product
open is-pullback
open Pullback
open is-equaliser
open Equaliser
```
-->

# Finite set-limits

We prove that the category of `Sets`{.Agda} admits finite limits. The
terminal object is given by the 1-point set:

```agda
Sets-terminal : Terminal
Sets-terminal .Terminal.top = Lift _  ⊤ , is-prop→is-set (λ _ _ → refl)
Sets-terminal .Terminal.has⊤ _ = fun-is-hlevel 0 (contr (lift tt) λ x i → lift tt)
```

Products are given by product sets:

```agda
Sets-products : (A B : Set ℓ) → Product A B
Sets-products A B .apex = (∣ A ∣ × ∣ B ∣) , ×-is-hlevel 2 (A .is-tr) (B .is-tr)
Sets-products A B .π₁ = fst
Sets-products A B .π₂ = snd
Sets-products A B .has-is-product .⟨_,_⟩ f g x = f x , g x
Sets-products A B .has-is-product .π₁∘factor = refl
Sets-products A B .has-is-product .π₂∘factor = refl
Sets-products A B .has-is-product .unique o p q i x = p i x , q i x
```

Equalisers are given by carving out the subset of $A$ where $f$ and $g$ agree
using $\Sigma$:

```agda
Sets-equalisers : (f g : Hom A B) → Equaliser {A = A} {B = B} f g
Sets-equalisers {A = A} {B = B} f g = eq where
  eq : Equaliser f g
  eq .apex = Σ[ x ∈ ∣ A ∣ ] (f x ≡ g x) , Σ-is-hlevel 2 (A .is-tr) λ _ → is-prop→is-set (B .is-tr _ _)
  eq .equ = fst
  eq .has-is-eq .equal = funext snd
  eq .has-is-eq .limiting {e′ = e′} p x = e′ x , happly p x
  eq .has-is-eq .universal = refl
  eq .has-is-eq .unique {p = p} q =
    funext λ x → Σ-prop-path (λ _ → B .is-tr _ _) (happly (sym q) x)
```

Pullbacks are the same, but carving out a subset of $A \times B$.

```agda
Sets-pullbacks : ∀ {A B C} (f : Hom A C) (g : Hom B C)
               → Pullback {X = A} {Y = B} {Z = C} f g
Sets-pullbacks {A = A} {B = B} {C = C} f g = pb where
  pb : Pullback f g
  pb .apex .∣_∣ = Σ[ x ∈ ∣ A ∣ ] Σ[ y ∈ ∣ B ∣ ] (f x ≡ g y)
  pb .apex .is-tr =
    Σ-is-hlevel 2 (A .is-tr) λ _ →
    Σ-is-hlevel 2 (B .is-tr) λ _ →
    is-prop→is-set (C .is-tr _ _)
  pb .p₁ (x , _ , _) = x
  pb .p₂ (_ , y , _) = y
  pb .has-is-pb .square = funext (snd ⊙ snd)
  pb .has-is-pb .limiting {p₁' = p₁'} {p₂'} p a = p₁' a , p₂' a , happly p a
  pb .has-is-pb .p₁∘limiting = refl
  pb .has-is-pb .p₂∘limiting = refl
  pb .has-is-pb .unique {p = p} {lim' = lim'} q r i x =
    q i x , r i x ,
    λ j → is-set→squarep (λ i j → C .is-tr)
      (λ j → f (q j x)) (λ j → lim' x .snd .snd j) (happly p x) (λ j → g (r j x)) i j
```

Hence, `Sets`{.Agda} is finitely complete:

```agda
open Finitely-complete

Sets-finitely-complete : Finitely-complete (Sets ℓ)
Sets-finitely-complete .terminal = Sets-terminal
Sets-finitely-complete .products = Sets-products
Sets-finitely-complete .equalisers = Sets-equalisers
Sets-finitely-complete .pullbacks = Sets-pullbacks
```
