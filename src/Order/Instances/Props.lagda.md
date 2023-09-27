<!--
```agda
open import Cat.Prelude

open import Data.Sum.Base

open import Order.Diagram.Lub
open import Order.Diagram.Glb
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
open is-partial-order
open Poset-on

Props : Poset lzero lzero
Props = to-poset Ω mk-Ω where
  mk-Ω : make-poset lzero Ω
  mk-Ω .make-poset.rel P Q     = ∣ P ∣ → ∣ Q ∣
  mk-Ω .make-poset.id x        = x
  mk-Ω .make-poset.thin        = hlevel!
  mk-Ω .make-poset.trans g f x = f (g x)
  mk-Ω .make-poset.antisym     = Ω-ua
```

```agda
open Meet
open Join
open Glb
open Lub
open is-meet
open is-join
open is-lub
open is-glb

Props-lub : ∀ {ℓ} {I : Type ℓ} → (F : I → Ω) → Lub Props F
Props-lub {I = I} F .lub = elΩ (Σ[ i ∈ I ] ⌞ F i ⌟)
Props-lub F .has-lub .fam≤lub i α = inc (i , α)
Props-lub F .has-lub .least ub′ f = □-rec! λ (x , y) → f x y

Props-glb : ∀ {ℓ} {I : Type ℓ} → (F : I → Ω) → Glb Props F
Props-glb {I = I} F .glb               = elΩ ((i : I) → ⌞ F i ⌟)
Props-glb F .has-glb .glb≤fam i α      = out! α i
Props-glb F .has-glb .greatest ub′ f x = inc λ i → f i x

Props-meet : ∀ (a b : Ω) → Meet Props a b
∣ Props-meet a b .glb ∣ = ⌞ a ⌟ × ⌞ b ⌟
Props-meet a b .glb .is-tr = hlevel!
Props-meet a b .has-meet .meet≤l = fst
Props-meet a b .has-meet .meet≤r = snd
Props-meet a b .has-meet .greatest lb′ f g x = f x , g x

Props-join : ∀ (a b : Ω) → Join Props a b
Props-join a b .lub = elΩ (⌞ a ⌟ ⊎ ⌞ b ⌟)
Props-join a b .has-join .l≤join = □.inc ⊙ inl
Props-join a b .has-join .r≤join = □.inc ⊙ inr
Props-join a b .has-join .least ub′ f g = □-rec! [ f , g ]
```
