```agda
open import Cat.Order.Base
open import Cat.Prelude

module Cat.Order.Instances.Props where
```

# Propositions

In the [posetal] world, what plays the role of the [category of sets] is
the poset of _propositions_ --- our $\le$ relations take values in
propositions, much like the category of sets is where the [$\hom$
functor] takes values.

[posetal]: Cat.Order.Base.html
[category of sets]: Cat.Base.html#the-precategory-of-sets
[$\hom$ functor]: Cat.Functor.Hom.html

Unlike “the” category of sets, which is actually a bunch of categories,
there is a single poset of propositions --- this is the principle of
[_propositional resizing_], which we assume throughout.

[_propositional resizing_]: 1Lab.Resizing.html

```agda
open is-partial-order
open Poset-on

Props : Poset lzero lzero
Props = to-poset Ω λ where
  .make-poset.rel P Q     → ∣ P ∣ → ∣ Q ∣
  .make-poset.id x        → x
  .make-poset.thin        → hlevel!
  .make-poset.trans g f x → f (g x)
  .make-poset.antisym     → Ω-ua
```
