<!--
```agda
open import Cat.CartesianClosed.Locally
open import Cat.Instances.Sets.Complete
open import Cat.Diagram.Exponential
open import Cat.Functor.Pullback
open import Cat.Functor.Adjoint
open import Cat.Instances.Slice
open import Cat.Prelude
```
-->

```agda
module Cat.Instances.Sets.CartesianClosed {ℓ} where
```

<!--
```agda
open Functor
open /-Obj
open /-Hom
open _⊣_
open _=>_
```
-->

# Sets is (locally) cartesian closed

We show that the category of Sets is [locally cartesian closed], i.e.
that every map $f : A \to B$ of Sets induces a functor $\prod_f :
\Sets/A \to \Sets/B$, which is [[right adjoint]] to the [[pullback
functor]] $f^* : \Sets/B \to \Sets/A$.

[locally cartesian closed]: Cat.CartesianClosed.Locally.html

⚠️⚠️⚠️

```agda
module _ {A B : Set ℓ} (func : ∣ A ∣ → ∣ B ∣) where
  Sets-Π : Functor (Slice (Sets ℓ) A) (Slice (Sets ℓ) B)
  Sets-Π .F₀ ob .domain =
    el! (Σ[ y ∈ ∣ B ∣ ] ((f : fibre func y) → fibre (ob .map) (f .fst)))

  Sets-Π .F₀ ob .map g = g .fst

  Sets-Π .F₁ hom .map (i , fibs) = i , go where
    go : ∀ _ → _
    go (x , fx=i) = hom .map (fibs (x , fx=i) .fst) ,
      happly (hom .commutes) _ ∙ (fibs (x , fx=i) .snd)
  Sets-Π .F₁ hom .commutes = refl
```

<!--
```agda
  Sets-Π .F-id = ext λ x y → Σ-pathp refl
    (funext λ x → Σ-pathp refl (A .is-tr _ _ _ _))
  Sets-Π .F-∘ f g = ext λ x y → Σ-pathp refl
    (funext λ x → Σ-pathp refl (A .is-tr _ _ _ _))
```
-->

```agda
Sets-lcc : Locally-cartesian-closed (Sets ℓ)
Sets-lcc = dependent-product→lcc (Sets ℓ) Sets-finitely-complete Sets-Π adj where
  adj : ∀ {a b : Set ℓ} (f : ∣ a ∣ → ∣ b ∣) → Base-change _ {X = b} {Y = a} f ⊣ Sets-Π f
  adj f .unit .η x .map y = x .map y , λ f → (_ , _ , sym (f .snd)) , refl
  adj f .counit .η x .map ((a , g) , b , p) = g (b , sym p) .fst
  adj f .unit .η x .commutes = refl
  adj {a} {b} f .unit .is-natural x y g =
    /-Hom-path (funext λ x → Σ-pathp (happly (g .commutes) _)
      (funext-dep (λ p → Σ-pathp (Σ-pathp refl (Σ-pathp (λ i → p i .fst)
        (is-set→squarep (λ i j → b .is-tr) _ _ _ _)))
        (is-set→squarep (λ i j → a .is-tr) _ _ _ _))))
  adj f .counit .η x .commutes = funext λ where
    ((a , g) , b , p) → g (b , sym p) .snd
  adj {a} {b} f .counit .is-natural x y g =
    /-Hom-path (funext λ x → ap (g .map ⊙ fst ⊙ x .fst .snd)
      (Σ-pathp refl (b .is-tr _ _ _ _)))
  adj {a} {b} f .zig {A} =
    /-Hom-path (funext λ x → Σ-pathp refl (Σ-pathp refl (b .is-tr _ _ _ _)))
  adj {a} {b} f .zag =
    /-Hom-path (funext (λ x → Σ-pathp refl
      (funext λ x → Σ-pathp refl (a .is-tr _ _ _ _))))
```
