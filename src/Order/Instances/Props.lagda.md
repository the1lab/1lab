<!--
```agda
open import Cat.Prelude

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
