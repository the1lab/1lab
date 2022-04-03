```agda
open import Cat.CartesianClosed.Locally
open import Cat.Instances.Sets.Complete
open import Cat.Functor.Pullback
open import Cat.Functor.Adjoint
open import Cat.Instances.Slice
open import Cat.Prelude

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
\sets/A \to \sets/B$, which is right adjoint to the [base change]
functor $f^* : \sets/B \to \sets/A$.

[locally cartesian closed]: Cat.CartesianClosed.Locally.html
[base change]: Cat.Functor.Pullback.html

⚠️⚠️⚠️

```agda
module _ {A B : Set ℓ} (func : ∣ A ∣ → ∣ B ∣) where
  Sets-Π : Functor (Slice (Sets ℓ) A) (Slice (Sets ℓ) B)
  Sets-Π .F₀ ob .domain =
      (Σ[ y ∈ ∣ B ∣ ] ((f : fibre func y) → fibre (ob .map) (f .fst)))
    , Σ-is-hlevel 2 (B .is-tr) λ _ →
      Π-is-hlevel 2 λ _ →
      Σ-is-hlevel 2 (ob .domain .is-tr) λ _ → is-prop→is-set (A .is-tr _ _)

  Sets-Π .F₀ ob .map g = g .fst

  Sets-Π .F₁ hom .map (i , fibs) = i , go where
    go : ∀ _ → _
    go (x , fx=i) = hom .map (fibs (x , fx=i) .fst) ,
      happly (hom .commutes) _ ∙ (fibs (x , fx=i) .snd)
  Sets-Π .F₁ hom .commutes = refl
```

<!--
```agda
  Sets-Π .F-id = /-Hom-path
    (funext λ x → Σ-pathp refl (funext λ x → Σ-pathp refl (A .is-tr _ _ _ _)))
  Sets-Π .F-∘ f g = /-Hom-path
    (funext λ x → Σ-pathp refl (funext λ x → Σ-pathp refl (A .is-tr _ _ _ _)))
```
-->

```agda
open is-lcc
Sets-lcc : is-lcc (Sets ℓ)
Sets-lcc .finitely-complete = Sets-finitely-complete
Sets-lcc .Πf = Sets-Π
Sets-lcc .f*⊣Πf f .unit .η x .map y = x .map y , λ f → (_ , _ , sym (f .snd)) , refl
Sets-lcc .f*⊣Πf f .counit .η x .map ((a , g) , b , p) = g (b , sym p) .fst
```

<!--
```agda
Sets-lcc .f*⊣Πf f .unit .η x .commutes = refl
Sets-lcc .f*⊣Πf {a} {b} f .unit .is-natural x y g =
  /-Hom-path (funext λ x → Σ-pathp (happly (g .commutes) _)
    (funext-dep (λ p → Σ-pathp-dep (Σ-pathp refl (Σ-pathp (λ i → p i .fst)
      (is-set→squarep (λ i j → b .is-tr) _ _ _ _)))
      (is-set→squarep (λ i j → a .is-tr) _ _ _ _))))
Sets-lcc .f*⊣Πf f .counit .η x .commutes = funext λ where
  ((a , g) , b , p) → g (b , sym p) .snd
Sets-lcc .f*⊣Πf {a} {b} f .counit .is-natural x y g =
  /-Hom-path (funext λ x → ap (g .map ⊙ fst ⊙ x .fst .snd)
    (Σ-pathp refl (b .is-tr _ _ _ _)))
Sets-lcc .f*⊣Πf {a} {b} f .zig {A} =
  /-Hom-path (funext λ x → Σ-pathp refl (Σ-pathp refl (b .is-tr _ _ _ _)))
Sets-lcc .f*⊣Πf {a} {b} f .zag =
  /-Hom-path (funext (λ x → Σ-pathp refl
    (funext λ x → Σ-pathp refl (a .is-tr _ _ _ _))))
```
-->
