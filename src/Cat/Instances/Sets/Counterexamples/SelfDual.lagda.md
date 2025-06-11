<!--
```agda
open import Cat.Instances.Sets.Cocomplete using (Sets-initial)
open import Cat.Diagram.Initial.Strict
open import Cat.Diagram.Initial
open import Cat.Instances.Sets using (Sets^op-is-category)
open import Cat.Morphism
open import Cat.Prelude

open import Data.Bool
```
-->

```agda
module Cat.Instances.Sets.Counterexamples.SelfDual {ℓ} where
```
# Sets is not self-dual

We show that the category of sets is not self-dual, that is, there cannot exist a path between $\Sets$ and $\Sets\op$.

```agda
import Cat.Reasoning (Sets ℓ) as Sets
import Cat.Reasoning (Sets ℓ ^op) as Sets^op
```


To show our goal, we need to find a categorical property that holds in $\Sets$ but _not_ in $\Sets\op$.
First we note that both $\Sets$ and $\Sets\op$ have an initial object.

In $\Sets$:

```agda
_ : Initial (Sets ℓ)
_ = Sets-initial
```


In $\Sets\op$:

<!--
```agda
open Initial
open Strict-initial
open Sets.is-invertible
open Sets.Inverses
```
-->

```agda
Sets^op-initial : Initial (Sets ℓ ^op)
Sets^op-initial .bot = el! (Lift _ ⊤)
Sets^op-initial .has⊥ x = hlevel 0
```
<!--
```agda
_ = ⊥
```
-->

Now we can observe an interesting property of the initial object of $\Sets$: it is
[[strict|strict initial object]], meaning every morphism into it is in fact an *iso*morphism.
Intuitively, if you can write a function $X \to \bot$ then $X$ must itself be empty.

```agda
Sets-strict-initial : Strict-initial (Sets ℓ)
Sets-strict-initial .initial = Sets-initial
Sets-strict-initial .has-is-strict x f .inv ()
Sets-strict-initial .has-is-strict x f .inverses .invl = ext λ ()
Sets-strict-initial .has-is-strict x f .inverses .invr = ext λ x → absurd (f x .lower)
```

<!--
```agda
_ = true≠false
```
-->

Crucially, this property is not shared by the initial object of $\Sets\op$! Unfolding definitions, it says
that any function $\top \to X$ is an isomorphism, or equivalently, every inhabited set is contractible. But is this is certainly false:
`Bool`{.Agda} is inhabited, but not contractible, since `true≠false`{.Agda}.

```agda
¬Sets^op-strict-initial : ¬ Strict-initial (Sets ℓ ^op)
¬Sets^op-strict-initial si = true≠false true≡false
  where
```

$\Sets\op$ is univalent, so we invoke the propositionality of its initial object to let us work with `⊤`{.Agda}, for convenience.

```agda
    si≡⊤ : si .initial ≡ Sets^op-initial
    si≡⊤ = ⊥-is-prop _ Sets^op-is-category _ _

    to-iso-⊤ : (A : Set ℓ) → (Lift ℓ ⊤ → ⌞ A ⌟) → A Sets^op.≅ el! (Lift ℓ ⊤)
    to-iso-⊤ A f = invertible→iso _ _ (subst (is-strict-initial (Sets ℓ ^op)) si≡⊤ (si .has-is-strict) A f)
```

Using our ill-fated hypothesis, we can construct an iso between `Bool`{.Agda} and `⊤`{.Agda} from a function $\top \to$ `Bool`{.Agda}. From this
we conclude that `Bool`{.Agda} is contractible, from which we obtain (modulo `lift`{.Agda}ing) a proof of `true`{.Agda} `≡`{.Agda} `false`{.Agda}.

```agda
    Bool≅⊤ : el! (Lift ℓ Bool) Sets^op.≅ el! (Lift ℓ ⊤)
    Bool≅⊤ = to-iso-⊤ (el! (Lift _ Bool)) λ _ → lift true

    Bool-is-contr : is-contr (Lift ℓ Bool)
    Bool-is-contr = subst (is-contr ⊙ ∣_∣) (sym (Univalent.iso→path Sets^op-is-category Bool≅⊤)) (hlevel 0)

    true≡false : true ≡ false
    true≡false = lift-inj $ is-contr→is-prop Bool-is-contr _ _
```

We've shown that a categorical property holds in $\Sets$ and fails in $\Sets\op$, but paths between categories preserve categorical properties,
so we have a contradiction!

```agda
Sets≠Sets^op : ¬ (Sets ℓ ≡ Sets ℓ ^op)
Sets≠Sets^op p = ¬Sets^op-strict-initial (subst Strict-initial p Sets-strict-initial)
```
