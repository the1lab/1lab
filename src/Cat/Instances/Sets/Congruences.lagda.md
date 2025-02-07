<!--
```agda
open import Cat.Instances.Sets.Complete
open import Cat.Diagram.Coequaliser
open import Cat.Diagram.Pullback
open import Cat.Prelude

import Cat.Diagram.Congruence
```
-->

```agda
module Cat.Instances.Sets.Congruences {ℓ} where
```

# Sets has effective quotients

<!--
```agda
open Cat.Diagram.Congruence (Sets-finitely-complete {ℓ = ℓ})
private
  unit : Set ℓ
  unit = el (Lift ℓ ⊤) λ x y p q i j → lift tt
```
-->

The hardest part of proving that Sets has [effective quotients] is the
proof that [quotients are effective], which we can entirely reuse here.
The code here mostly mediates between the notion of "[congruence] on a
Set" and "equivalence relation on a Set". Thus, it is presented without
comment.

[effective quotients]: Cat.Diagram.Congruence.html#effective-congruences
[quotients are effective]: Data.Set.Coequaliser.html#effectivity
[congruence]: Cat.Diagram.Congruence.html

```agda
Sets-effective-congruences : ∀ {A} (R : Congruence-on A) → is-effective-congruence R
Sets-effective-congruences {A = A} R = epi where
  module R = Congruence-on R
  open is-effective-congruence

  rel : ∣ A ∣ → ∣ A ∣ → _
  rel x y = fibre R.inclusion (x , y)

  rel-refl : ∀ {x} → rel x x
  rel-refl {x} =
    R.has-refl x , Σ-pathp (happly R.refl-p₁ _) (happly R.refl-p₂ _)

  rel-sym : ∀ {x y} → rel x y → rel y x
  rel-sym (r , p) = R.has-sym r ,
    Σ-pathp (happly R.sym-p₁ _ ∙ ap snd p) (happly R.sym-p₂ _ ∙ ap fst p)

  rel-trans : ∀ {x y z} → rel x y → rel y z → rel x z
  rel-trans (r , p) (s , q) = R.has-trans (s , r , ap fst q ∙ sym (ap snd p)) ,
    Σ-pathp (ap fst (happly (sym R.trans-factors) _) ∙ ap fst p)
            (ap snd (happly (sym R.trans-factors) _) ∙ ap snd q)

  rel-prop : ∀ x y → is-prop (rel x y)
  rel-prop _ _ (r , s) (q , p) = Σ-prop-path!
    (happly (R.has-is-monic {c = unit} (λ _ → r) (λ _ → q) (funext λ _ → s ∙ sym p)) _)

  open Congruence hiding (quotient)
  undo : ∀ {x y} → inc x ≡ inc y → rel x y
  undo = effective λ where
    ._∼_ → rel
    .has-is-prop x y → rel-prop x y
    .reflᶜ → rel-refl
    ._∙ᶜ_ → rel-trans
    .symᶜ → rel-sym

  open is-coequaliser
  open is-pullback

  epi : is-effective-congruence R
  epi .A/R            = el (∣ A ∣ / rel) squash
  epi .quotient       = inc

  epi .has-quotient .coequal = funext λ { x → quot (x , refl) }

  epi .has-quotient .universal {F = F} {e' = e'} path =
    Quot-elim (λ _ → F .is-tr) e'
      λ { x y (r , q) → ap e' (ap fst (sym q))
                     ·· happly path r
                     ·· ap e' (ap snd q)
        }

  epi .has-quotient .factors = refl

  epi .has-quotient .unique {F = F} path =
    funext (Coeq-elim-prop (λ x → F .is-tr _ _) (happly path))

  epi .has-kernel-pair .square = funext λ { x → quot (x , refl) }

  epi .has-kernel-pair .universal path x = undo (happly path x) .fst

  epi .has-kernel-pair .p₁∘universal {p = path} =
    funext (λ x → ap fst (undo (happly path x) .snd))

  epi .has-kernel-pair .p₂∘universal {p = path} =
    funext (λ x → ap snd (undo (happly path x) .snd))

  epi .has-kernel-pair .unique {p = p} q r = funext λ x →
    let p = sym ( undo (happly p x) .snd
                ∙ Σ-pathp (happly (sym q) _) (happly (sym r) _))
     in happly (R.has-is-monic {c = unit} _ _ (funext λ _ → p)) _
```
