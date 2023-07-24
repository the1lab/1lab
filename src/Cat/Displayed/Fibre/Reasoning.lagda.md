<!--
```agda
open import Cat.Prelude

open import Cat.Displayed.Base
open import Cat.Displayed.Fibre

import Cat.Reasoning
import Cat.Displayed.Reasoning
```
-->

```agda
module Cat.Displayed.Fibre.Reasoning
  {o ℓ o′ ℓ′} {B : Precategory o ℓ}
  (E : Displayed B o′ ℓ′)
  where
```

<!--
```agda
private
  module B = Cat.Reasoning B
  open Displayed E
  open Cat.Displayed.Reasoning E
  module Fib {x} = Cat.Reasoning (Fibre E x)
  open Fib
```
-->


## Reasoning in Fibre Categories

```agda
  private variable
    a b c d x y z : B.Ob
    x′ x″ y′ z′ z″ : Ob[ x ]
    a′ b′ c′ d′ : Ob[ a ]
    f g h i j k : B.Hom x y
    f′ g′ h′ i′ j′ k′ : Hom[ f ] x′ y′

  opaque
    pullrf
      : {p : B.id B.∘ h ≡ i}
      → g′ ∘′ h′ ≡[ p ] i′
      → (f′ Fib.∘ g′) ∘′ h′ ≡[ p ∙ sym (B.idl _) ] f′ ∘′ i′
    pullrf p′ = cast[] $ to-pathp⁻ (whisker-l (B.idl _)) ∙[] pullr[] _ p′

  opaque
    pulllf
      : {p : f B.∘ B.id ≡ i}
      → f′ ∘′ g′ ≡[ p ] i′
      → f′ ∘′ (g′ Fib.∘ h′) ≡[ p ∙ sym (B.idr _) ] i′ ∘′ h′
    pulllf p′ = cast[] $ to-pathp⁻ (whisker-r (B.idl _)) ∙[] pulll[] _ p′

  opaque
    extendrf
      : {p : B.id B.∘ i ≡ B.id B.∘ k}
      → g′ ∘′ i′ ≡[ p ] h′ ∘′ k′
      → (f′ Fib.∘ g′) ∘′ i′ ≡[ p ] (f′ Fib.∘ h′) ∘′ k′
    extendrf {k = k} p′ = cast[] $
      to-pathp⁻ (whisker-l (B.idl _))
      ∙[] extendr[] _ p′
      ∙[] to-pathp (unwhisker-l (ap (B._∘ k) (B.idl _)) (B.idl _))

  opaque
    extendlf
      : {p : f B.∘ B.id ≡ g B.∘ B.id}
      → f′ ∘′ h′ ≡[ p ] g′ ∘′ k′
      → f′ ∘′ (h′ Fib.∘ i′) ≡[ p ] g′ ∘′ (k′ Fib.∘ i′)
    extendlf {g = g} p′ = cast[] $
      to-pathp⁻ (whisker-r (B.idl _))
      ∙[] extendl[] _ p′
      ∙[] to-pathp (unwhisker-r (ap (g B.∘_) (B.idl _)) (B.idl _))
```
