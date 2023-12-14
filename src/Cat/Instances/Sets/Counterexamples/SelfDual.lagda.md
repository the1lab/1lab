<!--
```agda
open import Cat.Instances.Sets.Cocomplete using (Sets-initial)
open import Cat.Diagram.Initial
open import Cat.Instances.Sets using (Sets^op-is-category)
open import Cat.Prelude

open import Data.Bool
```
-->

```agda
module Cat.Instances.Sets.Counterexamples.SelfDual {ℓ} where
```
# Sets is not self-dual

We show that the category of Sets is not self-dual, that is, there cannot exit a path between `Sets`{.Agda} and `Sets`{.Agda} `^op`{.Agda}.

```agda
import Cat.Reasoning (Sets ℓ) as Sets
import Cat.Reasoning (Sets ℓ ^op) as Sets^op
```


To show our goal, we need to find a categorical property that holds in `Sets`{.Agda} but _not_ in `Sets`{.Agda} `^op`{.Agda}.
First we note that both `Sets`{.Agda} and `Sets`{.Agda} `^op`{.Agda} have an initial object.

In `Sets`{.Agda}:
  
```agda
_ : Initial (Sets ℓ)
_ = Sets-initial
```


In `Sets`{.Agda} `^op`{.Agda}:

```agda
Sets^op-initial : Initial (Sets ℓ ^op)
Sets^op-initial .Initial.bot = el! (Lift _ ⊤)
Sets^op-initial .Initial.has⊥ x = hlevel!
```
<!--
```agda
_ = ⊥
``` 
-->

Now we can observe an interesting property of the initial object of `Sets`{.Agda}: every morphism into it is in fact an *iso*morphism.
Intuitively, if you can write a function $X \to \bot$  then $X$ must itself be empty.

```agda
hom-into→iso : ∀ {o h} (C : Precategory o h) → C .Precategory.Ob → Type _
hom-into→iso C A = ∀ X → Hom X A → X ≅ A
  where
    open import Cat.Morphism C

hom-into-initial→iso : ∀ {o h} (C : Precategory o h) → Type _
hom-into-initial→iso C = Σ[ I ∈ Initial C ] hom-into→iso C (I .Initial.bot)

holds-in-Sets : hom-into-initial→iso (Sets ℓ)
holds-in-Sets = Sets-initial , λ where 
  X f .Sets.to → f
  X f .Sets.from () 
  X f .Sets.inverses .Sets.Inverses.invl → ext λ ()
  X f .Sets.inverses .Sets.Inverses.invr → ext λ x → absurd (f x .Lift.lower)
```

<!-- 
```agda
_ = true≠false
```
-->

Crucially, this is property is not shared by the initial object of `Sets`{.Agda} `^op`{.Agda}! Unfolding definitions, it says 
that any function $\top \to X$ is an isomorphism, or equivalently, every inhabited set is contractible. But is this is certainly false:
`Bool`{.Agda} is inhabited, but not contractible, since `true≠false`{.Agda}.


```agda
¬holds-in-Sets^op : ¬ hom-into-initial→iso (Sets ℓ ^op)
¬holds-in-Sets^op (I , mk-iso) = true≠false $ true≡false
  where
    open Initial
    open import Cat.Morphism
```

`Sets`{.Agda} `^op`{.Agda} is univalent, so we invoke the propositionality of its initial object to let us work with `⊤`{.Agda}, for convenience.

```agda
    I≡⊤ : I ≡ Sets^op-initial
    I≡⊤ = ⊥-is-prop _ Sets^op-is-category _ _

    to-iso-⊤ : (A : Set ℓ) → (Lift ℓ ⊤ → ⌞ A ⌟) → A Sets^op.≅ el! (Lift ℓ ⊤)
    to-iso-⊤ = subst (λ I → hom-into→iso _ (I .bot)) I≡⊤ mk-iso
```

Using our ill-fated hypothesis, we can construct an iso between `Bool`{.Agda} and `⊤`{.Agda} from a function $\top \to$ `Bool`{.Agda}. From this
we conclude that `Bool`{.Agda} is contractible, from which we obtain (modulo `lift`{.Agda}ing) a proof of `true`{.Agda} `≡`{.Agda} `false`{.Agda}.

```agda
    Bool≅⊤ : el! (Lift ℓ Bool) Sets^op.≅ el! (Lift ℓ ⊤)
    Bool≅⊤ = to-iso-⊤ (el! (Lift _ Bool)) λ _ → lift true

    Bool-is-contr : is-contr (Lift ℓ Bool)
    Bool-is-contr = subst (is-contr ⊙ ∣_∣) (sym (Univalent.iso→path Sets^op-is-category Bool≅⊤)) hlevel!
    
    true≡false : true ≡ false
    true≡false = lift-inj $ is-contr→is-prop Bool-is-contr _ _
    
```

We've shown that a categorical property holds in `Sets`{.Agda} and fails in `Sets`{.Agda} `^op`{.Agda}, but paths between categories preserve categorical properties,
so we have a contradiction!

```agda
Sets≠Sets^op : ¬ (Sets ℓ ≡ Sets ℓ ^op)
Sets≠Sets^op p = ¬holds-in-Sets^op (subst hom-into-initial→iso p holds-in-Sets)
```
  
