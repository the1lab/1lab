```agda
open import Cat.FinitelyComplete
open import Cat.Prelude

module Cat.FinitelyComplete.Instances.Sets {ℓ} where
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
open IsProduct
open Product
open IsPullback
open Pullback
open IsEqualiser
open Equaliser
```
-->

# Finite set-limits

We prove that the category of `Sets`{.Agda} admits finite limits. The
terminal object is given by the 1-point set:

```agda
Sets-terminal : Terminal
Sets-terminal .Terminal.top = Lift _  ⊤ , isProp→isSet (λ _ _ → refl)
Sets-terminal .Terminal.has⊤ _ = isHLevel→ 0 (contr (lift tt) λ x i → lift tt)
```

Products are given by product sets:

```agda
Sets-products : (A B : Set ℓ) → Product A B
Sets-products A B .apex = (A .fst × B .fst) , isHLevel× 2 (A .snd) (B .snd)
Sets-products A B .π₁ = fst
Sets-products A B .π₂ = snd
Sets-products A B .hasIsProduct .⟨_,_⟩ f g x = f x , g x
Sets-products A B .hasIsProduct .π₁∘factor = refl
Sets-products A B .hasIsProduct .π₂∘factor = refl
Sets-products A B .hasIsProduct .unique o p q i x = p i x , q i x
```

Equalisers are given by carving out the subset of $A$ where $f$ and $g$ agree
using $\Sigma$:

```agda
Sets-equalisers : (f g : Hom A B) → Equaliser {A = A} {B = B} f g
Sets-equalisers {A = A , As} {B = B , Bs} f g = eq where
  eq : Equaliser f g
  eq .apex = Σ[ x ∈ A ] (f x ≡ g x) , isHLevelΣ 2 As λ _ → isProp→isSet (Bs _ _)
  eq .equ = fst
  eq .hasIsEq .equal = funext snd
  eq .hasIsEq .limiting {e′ = e′} p x = e′ x , happly p x
  eq .hasIsEq .universal = refl
  eq .hasIsEq .unique {p = p} q = 
    funext λ x → Σ≡Prop (λ _ → Bs _ _) (happly (sym q) x)
```

Pullbacks are the same, but carving out a subset of $A \times B$.

```agda
Sets-pullbacks : ∀ {A B C} (f : Hom A C) (g : Hom B C) 
               → Pullback {X = A} {Y = B} {Z = C} f g
Sets-pullbacks {A = A , As} {B = B , Bs} {C = C , Cs} f g = pb where
  pb : Pullback f g
  pb .apex .fst = Σ[ x ∈ A ] Σ[ y ∈ B ] (f x ≡ g y)
  pb .apex .snd = isHLevelΣ 2 As λ _ → isHLevelΣ 2 Bs λ _ → isProp→isSet (Cs _ _)
  pb .p₁ (x , _ , _) = x
  pb .p₂ (_ , y , _) = y
  pb .hasIsPb .square = funext (snd ⊙ snd)
  pb .hasIsPb .limiting {p₁' = p₁'} {p₂'} p a = p₁' a , p₂' a , happly p a
  pb .hasIsPb .p₁∘limiting = refl
  pb .hasIsPb .p₂∘limiting = refl
  pb .hasIsPb .unique {p = p} {lim' = lim'} q r i x = 
    q i x , r i x , 
    λ j → isSet→SquareP (λ i j → Cs) 
      (λ j → f (q j x)) (λ j → lim' x .snd .snd j) (happly p x) (λ j → g (r j x)) i j
```

Hence, `Sets`{.Agda} is finitely complete:

```agda
open FinitelyComplete

FinitelyComplete-Sets : FinitelyComplete (Sets ℓ)
FinitelyComplete-Sets .terminal = Sets-terminal
FinitelyComplete-Sets .products = Sets-products
FinitelyComplete-Sets .equalisers = Sets-equalisers
FinitelyComplete-Sets .pullbacks = Sets-pullbacks
```
