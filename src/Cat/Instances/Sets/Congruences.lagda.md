```agda
open import Cat.Instances.Sets.Complete
open import Cat.Diagram.Coequaliser
open import Cat.Diagram.Pullback
open import Cat.Prelude

import Cat.Diagram.Congruence

module Cat.Instances.Sets.Congruences {ℓ} where
```

# Sets has effective quotients

<!--
```agda
open Cat.Diagram.Congruence (Sets-finitely-complete {ℓ = ℓ})
private
  unit : Set ℓ
  unit = Lift ℓ ⊤ , λ x y p q i j → lift tt
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
Sets-effective-congruences {A = A} R = eff where
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
  rel-prop _ _ (r , s) (q , p) =
    Σ-path
      (happly (R.has-is-monic {c = unit} m1 m2 (funext λ _ → s ∙ sym p)) _)
      (×-is-hlevel 2 (A .is-tr) (A .is-tr) _ _ _ _)
    where
      m1 m2 : Precategory.Hom (Sets ℓ) unit R.domain
      m1 _ = r
      m2 _ = q

  undo : ∀ {x y} → inc x ≡ inc y → rel x y
  undo = equiv→inverse (effective rel-prop rel-refl rel-trans rel-sym)

  open is-coequaliser
  open is-pullback

  eff : is-effective-congruence R
  eff .A/R            = ∣ A ∣ / rel , squash
  eff .quotient       = inc

  eff .has-quotient .coequal = funext λ { x → quot (x , refl) }

  eff .has-quotient .coequalise {F = F} {e′ = e′} path =
    Quot-elim (λ _ → F .is-tr) e′
      λ { x y (r , q) → ap e′ (ap fst (sym q))
                     ·· happly path r
                     ·· ap e′ (ap snd q)
        }

  eff .has-quotient .universal = refl

  eff .has-quotient .unique {F = F} path =
    funext (Coeq-elim-prop (λ x → F .is-tr _ _) (sym ⊙ happly path))

  eff .is-kernel-pair .square = funext λ { x → quot (x , refl) }

  eff .is-kernel-pair .limiting path x = undo (happly path x) .fst

  eff .is-kernel-pair .p₁∘limiting {p = path} =
    funext (λ x → ap fst (undo (happly path x) .snd))

  eff .is-kernel-pair .p₂∘limiting {p = path} =
    funext (λ x → ap snd (undo (happly path x) .snd))

  eff .is-kernel-pair .unique {p = p} q r = funext λ x →
    let p = sym ( undo (happly p x) .snd
                ∙ Σ-pathp (happly (sym q) _) (happly (sym r) _))
     in happly (R.has-is-monic {c = unit} _ _ (funext λ _ → p)) _
```
