<!--
```agda
open import Cat.Prelude

open import Data.Sum

open import Order.Diagram.Glb
open import Order.Diagram.Lub
open import Order.Base
```
-->

```agda
module Order.Instances.Props where
```

# Propositions

In the [[posetal|poset]] world, what plays the role of the [category of
sets] is the poset of _propositions_ --- our $\le$ relations take values
in propositions, much like the category of sets is where the [$\hom$
functor] takes values.

[category of sets]: Cat.Base.html#the-precategory-of-sets
[$\hom$ functor]: Cat.Functor.Hom.html

Unlike “the” category of sets, which is actually a bunch of categories
(depending on the universe level of the types we're considering), there
is a single poset of propositions --- this is the principle of
[_propositional resizing_], which we assume throughout.

[_propositional resizing_]: 1Lab.Resizing.html

```agda
Props : Poset lzero lzero
Props .Poset.Ob = Ω
Props .Poset._≤_ P Q = ∣ P ∣ → ∣ Q ∣
Props .Poset.≤-thin = hlevel!
Props .Poset.≤-refl x = x
Props .Poset.≤-trans g f x = f (g x)
Props .Poset.≤-antisym = Ω-ua
```

```agda
Props-has-top : Top Props
Props-has-top .Top.top = ⊤Ω
Props-has-top .Top.has-top _ _ = tt

Props-has-bot : Bottom Props
Props-has-bot .Bottom.bot = ⊥Ω
Props-has-bot .Bottom.has-bottom _ ()

Props-has-joins : ∀ P Q → Join Props P Q
Props-has-joins P Q .Join.lub = P ∨Ω Q
Props-has-joins P Q .Join.has-join .is-join.l≤join = pure ⊙ inl
Props-has-joins P Q .Join.has-join .is-join.r≤join = pure ⊙ inr
Props-has-joins P Q .Join.has-join .is-join.least R l r = ∥-∥-rec! [ l , r ]

Props-has-meets : ∀ P Q → Meet Props P Q
Props-has-meets P Q .Meet.glb = P ∧Ω Q
Props-has-meets P Q .Meet.has-meet .is-meet.meet≤l = fst
Props-has-meets P Q .Meet.has-meet .is-meet.meet≤r = snd
Props-has-meets P Q .Meet.has-meet .is-meet.greatest R l r x = (l x) , (r x)

Props-has-glbs : ∀ {ℓ} {I : Type ℓ} → (Ps : I → Ω) → Glb Props Ps
Props-has-glbs {I = I} Ps .Glb.glb = ∀Ω I Ps
Props-has-glbs Ps .Glb.has-glb .is-glb.glb≤fam i f = (out! f) i
Props-has-glbs Ps .Glb.has-glb .is-glb.greatest R k x = inc (λ i → k i x)

Props-has-lubs : ∀ {ℓ} {I : Type ℓ} → (Ps : I → Ω) → Lub Props Ps
Props-has-lubs {I = I} Ps .Lub.lub = ∃Ω I Ps
Props-has-lubs Ps .Lub.has-lub .is-lub.fam≤lub i pi = inc (i , pi)
Props-has-lubs Ps .Lub.has-lub .is-lub.least R k x = □-rec! (λ { (i , pi) → k i pi }) x
```
