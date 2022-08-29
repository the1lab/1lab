```agda
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning as CR

module Cat.Displayed.Functor where
```

# Displayed and fibred functors

If you have a pair of categories $\ca{E}, \ca{F}$ \r{displayed over} a
common base \r{category} $\ca{B}$, it makes immediate sense to talk
about \r{functors} $F : \ca{E} \to \ca{F}$: you'd have an assignment of
objects $F_x : \ca{E}^*(x) \to \ca{F}^*(x)$ and an assignment of
morphisms

$$
F_{a,b,f} : (a' \to_f b') \to (F_a(a') \to_f F_b(b'))\text{,}
$$

which makes sense because $F_a(a')$ lies over $a$, just as $a'$ did,
that a morphism $F_a(a') \to F_b(b')$ is allowed to lie over a morphism
$f : a \to b$. But, in the spirit of relativising category theory, it
makes more sense to consider functors between categories displayed over
_different_ bases, as in

~~~{.quiver}
\[\begin{tikzcd}
  {\mathcal{E}} && {\mathcal{F}} \\
  \\
  {\mathcal{A}} && {\mathcal{B}\text{,}}
  \arrow["{\mathbf{F}}", from=1-1, to=1-3]
  \arrow["{F}"', from=3-1, to=3-3]
  \arrow[category over, from=1-3, to=3-3]
  \arrow[category over, from=1-1, to=3-1]
\end{tikzcd}\]
~~~

with our displayed functor $\bf{F} : \ca{E} \to \ca{F}$ lying over an
ordinary functor $F : \ca{A} \to \ca{B}$ to mediate between the bases.

<!--
```agda
module
  _ {o ℓ o′ ℓ′ o₂ ℓ₂ o₂′ ℓ₂′}
    {A : Precategory o ℓ}
    {B : Precategory o₂ ℓ₂}
    (ℰ : Displayed A o′ ℓ′)
    (ℱ : Displayed B o₂′ ℓ₂′)
    (F : Functor A B)
  where
  private
    module F = Functor F
    module A = CR A
    module B = CR B
    module ℰ = Displayed ℰ
    module ℱ = Displayed ℱ
    lvl : Level
    lvl = o ⊔ o′ ⊔ o₂′ ⊔ ℓ ⊔ ℓ′ ⊔ ℓ₂′
```
-->

```agda
  record Displayed-functor : Type lvl where
    field
      F₀′ : ∀ {x} (o : ℰ.Ob[ x ]) → ℱ.Ob[ F.₀ x ]
      F₁′ : ∀ {a b} {f : A.Hom a b} {a′ b′}
          → ℰ.Hom[ f ] a′ b′ → ℱ.Hom[ F.₁ f ] (F₀′ a′) (F₀′ b′)
```

In order to state the displayed functoriality laws, we require
functoriality for our mediating functor $F$. Functors between categories
displayed over the same base can be recovered as the "vertical displayed
functors", i.e., those lying over the identity functor.

```agda
      F-id′ : ∀ {x} {o : ℰ.Ob[ x ]}
            → PathP (λ i → ℱ.Hom[ F.F-id i ] (F₀′ o) (F₀′ o))
                    (F₁′ ℰ.id′) ℱ.id′
      F-∘′ : ∀ {a b c} {f : A.Hom b c} {g : A.Hom a b} {a′ b′ c′}
               {f′ : ℰ.Hom[ f ] b′ c′} {g′ : ℰ.Hom[ g ] a′ b′}
           → PathP (λ i → ℱ.Hom[ F.F-∘ f g i ] (F₀′ a′) (F₀′ c′))
                   (F₁′ (f′ ℰ.∘′ g′))
                   (F₁′ f′ ℱ.∘′ F₁′ g′)
```

Note that, if $\ca{E}$ and $\ca{F}$ are \r{fibred categories} over their
bases (rather than just _displayed_ categories), then the appropriate
notion of 1-cell are displayed functors that take Cartesian morphisms to
Cartesian morphisms:

```agda
  record Fibred-functor : Type (lvl ⊔ o₂ ⊔ ℓ₂) where
    field
      disp : Displayed-functor

    open Displayed-functor disp public

    field
      F-cartesian
        : ∀ {a b a′ b′} {f : A.Hom a b} (f′ : ℰ.Hom[ f ] a′ b′)
        → Cartesian ℰ f f′ → Cartesian ℱ (F.₁ f) (F₁′ f′)
```
