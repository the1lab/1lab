---
description: |
  Reasoning combinators for natural transformations
---
<!--
```agda
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->
```agda
module Cat.Natural.Reasoning
  {o ℓ o' ℓ'}
  {𝒞 : Precategory o ℓ} {𝒟 : Precategory o' ℓ'}
  {F G : Functor 𝒞 𝒟}
  (α : F => G)
  where
```

<!--
```agda
private
  module 𝒞 = Cat.Reasoning  𝒞
  module 𝒟 = Cat.Reasoning 𝒟
  module F = Cat.Functor.Reasoning F
  module G = Cat.Functor.Reasoning G
open _=>_ α public

private variable
  A B C : 𝒞.Ob
  X Y Z : 𝒟.Ob
  a b c : 𝒞.Hom A B
  f g h : 𝒟.Hom X Y
```
-->

# Reasoning combinators for natural transformations

## Lenses

Our first set of reasoning combinators let you re-arrange goals by
conjugating with naturality. The mnemonic here is that `naturall`{.Agda}
lets you move the natural transformation left.

```agda
naturall
  : η _ 𝒟.∘ F.₁ a ≡ η _ 𝒟.∘ F.₁ b
  → G.₁ a 𝒟.∘ η _ ≡ G.₁ b 𝒟.∘ η _
naturall p = sym (is-natural _ _ _) ·· p ·· is-natural _ _ _

naturalr
  : G.₁ a 𝒟.∘ η _ ≡ G.₁ b 𝒟.∘ η _
  → η _ 𝒟.∘ F.₁ a ≡ η _ 𝒟.∘ F.₁ b
naturalr p = is-natural _ _ _ ·· p ·· sym (is-natural _ _ _)
```

We also provide a pair of combinators that simultaneously apply naturality
and focus on a subexpression.

```agda
viewr
  : G.₁ a ≡ G.₁ b
  → η _ 𝒟.∘ F.₁ a ≡ η _ 𝒟.∘ F.₁ b
viewr p = naturalr (ap (𝒟._∘ η _) p)

viewl
  : F.₁ a ≡ F.₁ b
  → G.₁ a 𝒟.∘ η _ ≡ G.₁ b 𝒟.∘ η _
viewl p = naturall (ap (η _ 𝒟.∘_) p)
```


## Commuting `η` through composites

```agda
pulll
  : (p : η _ 𝒟.∘ f ≡ g)
  → η _ 𝒟.∘ F.₁ a 𝒟.∘ f ≡ G.₁ a 𝒟.∘ g
pulll p = 𝒟.pulll (is-natural _ _ _) ∙ 𝒟.pullr p

pullr
  : (p : f 𝒟.∘ η _ ≡ g)
  → (f 𝒟.∘ G.₁ a) 𝒟.∘ η _ ≡ g 𝒟.∘ F.₁ a
pullr p = 𝒟.pullr (sym (is-natural _ _ _)) ∙ 𝒟.pulll p
```

```agda
popl
  : (p : η _ 𝒟.∘ F.₁ b ≡ f)
  → η _ 𝒟.∘ F.₁ (a 𝒞.∘ b) ≡ G.₁ a 𝒟.∘ f
popl p =  F.popl (is-natural _ _ _) ∙ 𝒟.pullr p

popr
  : (p : G.₁ a 𝒟.∘ η _ ≡ f)
  → G.₁ (a 𝒞.∘ b) 𝒟.∘ η _ ≡ f 𝒟.∘ F.₁ b
popr p = G.popr (sym (is-natural _ _ _)) ∙ 𝒟.pulll p
```

```agda
shiftl
  : (p : F.₁ a 𝒟.∘ f ≡ g)
  → G.₁ a 𝒟.∘ η _ 𝒟.∘ f ≡ η _ 𝒟.∘ g
shiftl p = 𝒟.pulll (sym (is-natural _ _ _)) ∙ 𝒟.pullr p

shiftr
  : (p : f 𝒟.∘ G.₁ a ≡ g)
  → (f 𝒟.∘ η _) 𝒟.∘ F.₁ a ≡ g 𝒟.∘ η _
shiftr p = 𝒟.pullr (is-natural _ _ _) ∙ 𝒟.pulll p
```


## Cancellations

```agda
cancell
  : (p : η _ 𝒟.∘ f ≡ 𝒟.id)
  → η _ 𝒟.∘ F.₁ a 𝒟.∘ f ≡ G.₁ a
cancell p = 𝒟.pulll (is-natural _ _ _) ∙ 𝒟.cancelr p

cancelr
  : (p : f 𝒟.∘ η _ ≡ 𝒟.id)
  → (f 𝒟.∘ G.₁ a) 𝒟.∘ η _ ≡ F.₁ a
cancelr p = 𝒟.pullr (sym (is-natural _ _ _)) ∙ 𝒟.cancell p
```
