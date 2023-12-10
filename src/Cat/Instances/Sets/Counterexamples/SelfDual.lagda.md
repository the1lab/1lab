<!--
```agda
open import Cat.Prelude
open import Cat.Instances.Sets using (Sets^op-is-category)
open import Cat.Instances.Sets.Cocomplete using (Sets-initial)
open import Cat.Diagram.Initial
```
-->

```agda
module Cat.Instances.Sets.Counterexamples.SelfDual {ℓ} where
```

We show that the category of Sets is not self-dual, that is, there cannot exit a path between `Sets`{.Agda} and `Sets`{.Agda} `^op`{.Agda}.

```agda
import Cat.Reasoning (Sets ℓ) as Sets
import Cat.Reasoning (Sets ℓ ^op) as Sets^op
```

As a warm up: `Sets^op` has an `Initial`{.Agda} object.

```agda
Sets^op-initial : Initial (Sets ℓ ^op)
Sets^op-initial .Initial.bot = el! (Lift _ ⊤)
Sets^op-initial .Initial.has⊥ x = hlevel!
```
To show our goal, we find a categorical property that holds in `Sets`{.Agda} but _not_ in the opposite category.
Note that `Sets`{.Agda} has an initial object (`⊥`{.Agda}) for which all morphisms into `⊥`{.Agda} are isomorphisms,
but the initial object in the opposite category (`⊤`{.Agda}) does not have this property.
```agda
private

  HomInto→Iso : ∀ {o h} (C : Precategory o h) → C .Precategory.Ob → Type _
  HomInto→Iso C A = ∀ X → Hom X A → X ≅ A
    where
      open import Cat.Morphism C

  HomIntoInitial→Iso : ∀ {o h} (C : Precategory o h) → Type _
  HomIntoInitial→Iso C = Σ[ I ∈ Initial C ] HomInto→Iso C (I .Initial.bot)

  HoldsInSets : HomIntoInitial→Iso (Sets ℓ)
  HoldsInSets = Sets-initial , λ where 
    X f .Sets.to → f
    X f .Sets.from () 
    X f .Sets.inverses .Sets.Inverses.invl → ext λ ()
    X f .Sets.inverses .Sets.Inverses.invr → ext λ x → absurd (f x .Lift.lower)

  ¬HoldsInSets^op : ¬ HomIntoInitial→Iso (Sets ℓ ^op)
  ¬HoldsInSets^op (I , mk-iso) = true≠false $ lift-inj $ bad _ _
    where
      open Initial
      open import Data.Bool
      open import Cat.Morphism
```
`Sets`{.Agda} `^op`{.Agda} is univalent, so all initial objects have a path to `⊤`{.Agda}. Using our hypothesis
we can conclude that any Set `A` for which we can write a function `⊤ → A`{.Agda} (a.k.a any inhabited Set), we have an isomorphism between `A` and `⊤`{.Agda} .
```agda
      I≡⊤ : I ≡ Sets^op-initial
      I≡⊤ = ⊥-is-prop _ Sets^op-is-category _ _

      to-iso-⊤ : (A : Set ℓ) → (Lift ℓ ⊤ → ∣ A ∣) → A Sets^op.≅ el! (Lift ℓ ⊤)
      to-iso-⊤ = subst (λ I → HomInto→Iso _ (I .bot)) I≡⊤ mk-iso
```
For instance, we can show that `Bool`{.Agda} and `⊤`{.Agda} are isomorphic, but this entails that `Bool`{.Agda} is a proposition, something we know to be false.
```agda
      Bool≅⊤ : el! (Lift ℓ Bool) Sets^op.≅ el! (Lift ℓ ⊤)
      Bool≅⊤ = to-iso-⊤ (el! (Lift _ Bool)) λ _ → lift true

      bad : is-prop (Lift ℓ Bool)
      bad = subst (is-prop ⊙ ∣_∣) (sym (Univalent.iso→path Sets^op-is-category Bool≅⊤)) hlevel!
```

We've shown that a property holds in `Sets`{.Agda}, but not in `Sets`{.Agda} `^op`{.Agda}, but a path between them means this property must hold in `Sets`{.Agda} `^op`{.Agda} as well,
so we have a contradiction!

```agda
Sets≠Sets^op : ¬ (Sets ℓ ≡ Sets ℓ ^op)
Sets≠Sets^op p = ¬HoldsInSets^op (subst HomIntoInitial→Iso p HoldsInSets)

```
  