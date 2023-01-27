```agda
open import Cat.Displayed.Base
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Total.Op
open import Cat.Prelude

import Cat.Reasoning
import Cat.Displayed.Morphism
import Cat.Displayed.Morphism.Duality
import Cat.Displayed.Reasoning as DR

module Cat.Displayed.Cocartesian
  {o ℓ o′ ℓ′} {ℬ : Precategory o ℓ} (ℰ : Displayed ℬ o′ ℓ′) where

open Cat.Reasoning ℬ
open Displayed ℰ
open Cat.Displayed.Morphism ℰ
open Cat.Displayed.Morphism.Duality ℰ
open DR ℰ
```

# Cocartesian morphisms and Opfibrations

[Cartesian fibrations] provide a way of describing pseudofunctorial
families of categories $\ca{B}^{op} \to \Cat$ purely in terms of
displayed structure. It's then natural to ask: what about
*covariant* pseudofunctorial families of categories? Such pseudofunctors
can be encoded by dualising cartesian fibrations.

[Cartesian fibrations]: Cat.Displayed.Cartesian.html

To do this, we must first dualise the notion of a cartesian map to a
**cocartesian map**. Fix a map $a \to b$ in $\ca{B}$, objects $a'$
and $b'$ displayed over $a$ and $b$ resp., and a map $f' : a' \to_f b'$
over $f$. We say that $f'$ is **cocartesian** if it has the shape of a
"pushout diagram", in contrast to the cartesian maps "pullback diagrams".

~~~{.quiver}
\[\begin{tikzcd}
  {a'} && {b'} \\
  \\
  a && b
  \arrow["{f'}"', from=1-1, to=1-3]
  \arrow["f", from=3-1, to=3-3]
  \arrow[lies over, from=1-1, to=3-1]
  \arrow[lies over, from=1-3, to=3-3]
\end{tikzcd}\]
~~~

```agda
record Cocartesian
  {a b a′ b′} (f : Hom a b) (f′ : Hom[ f ] a′ b′)
  : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′)
  where
  no-eta-equality
```

Concretely, let $u : \ca{B}$ and $u'$ be displayed over $u$. Furthermore,
suppose we have a map $m : b \to u$ (highlighted in violet below), along
with a map $h' : a' \to_{mf} u'$ displayed over $m \cdot f$ (highlighted
in red). For $f'$ to be cocartesian, every such situation must give rise
to a unique universal factorisation of $h'$ through a map $b' \to_{m} u'$
(highlighted in green).

~~~{.quiver}
\begin{tikzcd}
	&&& \textcolor{rgb,255:red,124;green,50;blue,189}{u'} \\
	{a'} && {b'} \\
	&&& \textcolor{rgb,255:red,124;green,50;blue,189}{u} \\
	a && b
	\arrow[lies over, from=2-1, to=4-1]
	\arrow["f", from=4-1, to=4-3]
	\arrow[lies over, from=2-3, to=4-3]
	\arrow["{f'}", from=2-1, to=2-3]
	\arrow["{m'}", color={rgb,255:red,153;green,92;blue,214}, from=4-3, to=3-4]
	\arrow["{\exists!}"', color={rgb,255:red,92;green,214;blue,92}, dashed, from=2-3, to=1-4]
	\arrow[lies over, color={rgb,255:red,153;green,92;blue,214}, from=1-4, to=3-4]
	\arrow["{h'}", color={rgb,255:red,214;green,92;blue,92}, curve={height=-12pt}, from=2-1, to=1-4]
\end{tikzcd}
~~~

```agda
  field
    universal
      : ∀ {u u′} (m : Hom b u) (h′ : Hom[ m ∘ f ] a′ u′)
      → Hom[ m ] b′ u′
    commutes
      : ∀ {u u′} (m : Hom b u) (h′ : Hom[ m ∘ f ] a′ u′)
      → universal m h′ ∘′ f′ ≡ h′
    unique
      : ∀ {u u′} {m : Hom b u} {h′ : Hom[ m ∘ f ] a′ u′}
      → (m′ : Hom[ m ] b′ u′) → m′ ∘′ f′ ≡ h′
      → m′ ≡ universal m h′
```

As in the cartesian case, we provide helper functions for working
with morphisms that are propositionally displayed over a composite.

```agda
  universal′ : ∀ {u u′} {m : Hom b u} {k : Hom a u}
             → (p : m ∘ f ≡ k) (h′ : Hom[ k ] a′ u′)
             → Hom[ m ] b′ u′
  universal′ {u′ = u′} p h′ = universal _ (coe1→0 (λ i → Hom[ p i ] a′ u′) h′)

  commutesp : ∀ {u u′} {m : Hom b u} {k : Hom a u} 
            → (p : m ∘ f ≡ k) (h′ : Hom[ k ] a′ u′)
            → universal′ p h′ ∘′ f′ ≡[ p ] h′ 
  commutesp {u′ = u′} p h′ =
    to-pathp⁻ (commutes _ (coe1→0 (λ i → Hom[ p i ] a′ u′) h′))

  universalp : ∀ {u u′} {m₁ m₂ : Hom b u} {k : Hom a u}
             → (p : m₁ ∘ f ≡ k) (q : m₁ ≡ m₂) (r : m₂ ∘ f ≡ k)
             → (h′ : Hom[ k ] a′ u′)
             → universal′ p h′ ≡[ q ] universal′ r h′
  universalp {u = u} p q r h′ i =
    universal′ (is-set→squarep (λ _ _ → Hom-set a u) (ap (_∘ f) q) p r refl i) h′

  uniquep : ∀ {u u′} {m₁ m₂ : Hom b u} {k : Hom a u}
          → (p : m₁ ∘ f ≡ k) (q : m₁ ≡ m₂) (r : m₂ ∘ f ≡ k)
          → {h′ : Hom[ k ] a′ u′}
          → (m′ : Hom[ m₁ ] b′ u′)
          → m′ ∘′ f′ ≡[ p ] h′ → m′ ≡[ q ] universal′ r h′
  uniquep p q r {h′ = h′} m′ s  =
    to-pathp⁻ (unique m′ (from-pathp⁻ s) ∙ from-pathp⁻ (universalp p q r h′))
```

## Duality

As noted before, cocartesian maps are dual to cartesian maps. We
can make this correspondence precise by showing that cartesian maps
in the total opposite of $\ca{E}$ are cocartesian maps, and vice versa.

```agda
cartesian^op→cocartesian
  : ∀ {x y} {f : Hom x y} {x′ y′} {f′ : Hom[ f ] x′ y′}
  → Cartesian (ℰ ^total-op) f f′
  → Cocartesian f f′
cartesian^op→cocartesian cart^op .Cocartesian.universal m h′ =
  Cartesian.universal cart^op m h′
cartesian^op→cocartesian cart^op .Cocartesian.commutes m h′ =
  Cartesian.commutes cart^op m h′
cartesian^op→cocartesian cart^op .Cocartesian.unique m′ p =
  Cartesian.unique cart^op m′ p

cocartesian→cartesian^op
  : ∀ {x y} {f : Hom x y} {x′ y′} {f′ : Hom[ f ] x′ y′}
  → Cocartesian f f′
  → Cartesian (ℰ ^total-op) f f′
cocartesian→cartesian^op cocart .Cartesian.universal m h′ =
  Cocartesian.universal cocart m h′
cocartesian→cartesian^op cocart .Cartesian.commutes m h′ =
  Cocartesian.commutes cocart m h′
cocartesian→cartesian^op cocart .Cartesian.unique m′ p =
  Cocartesian.unique cocart m′ p
```

Furthermore, these 2 functions form an equivalence, which we can extend
to a path via univalence.

```agda
cartesian^op→cocartesian-is-equiv
  : ∀ {x y} {f : Hom x y} {x′ y′} {f′ : Hom[ f ] x′ y′}
  → is-equiv (cartesian^op→cocartesian {f′ = f′})
cartesian^op→cocartesian-is-equiv {f′ = f′} =
  is-iso→is-equiv $ iso cocartesian→cartesian^op cocart-invl cocart-invr
  where
    cocart-invl
      : ∀ f
      → cartesian^op→cocartesian {f′ = f′} (cocartesian→cartesian^op f) ≡ f
    cocart-invl f i .Cocartesian.universal m h′ = Cocartesian.universal f m h′
    cocart-invl f i .Cocartesian.commutes m h′ = Cocartesian.commutes f m h′
    cocart-invl f i .Cocartesian.unique m′ p = Cocartesian.unique f m′ p

    cocart-invr
      : ∀ f
      → cocartesian→cartesian^op {f′ = f′} (cartesian^op→cocartesian f) ≡ f
    cocart-invr f i .Cartesian.universal m h′ = Cartesian.universal f m h′
    cocart-invr f i .Cartesian.commutes m h′ = Cartesian.commutes f m h′
    cocart-invr f i .Cartesian.unique m′ p = Cartesian.unique f m′ p

cartesian^op≡cocartesian
  : ∀ {x y} {f : Hom x y} {x′ y′} {f′ : Hom[ f ] x′ y′}
  → Cartesian (ℰ ^total-op) f f′ ≡ Cocartesian f f′
cartesian^op≡cocartesian =
  ua (cartesian^op→cocartesian , cartesian^op→cocartesian-is-equiv)
```

## Properties of Cocartesian Morphisms

<details>
<summary>
We shall now prove some properties of cocartesian morphisms. These
are all dual to the properties that we've proved about cartesian
morphisms, so we will appeal to duality to prove them!
</summary>

```agda
cocartesian-∘
  : ∀ {x y z} {f : Hom y z} {g : Hom x y}
  → ∀ {x′ y′ z′} {f′ : Hom[ f ] y′ z′} {g′ : Hom[ g ] x′ y′}
  → Cocartesian f f′ → Cocartesian g g′
  → Cocartesian (f ∘ g) (f′ ∘′ g′)
cocartesian-∘ f-cocart g-cocart =
  cartesian^op→cocartesian $
  cartesian-∘ _
    (cocartesian→cartesian^op g-cocart)
    (cocartesian→cartesian^op f-cocart)

cocartesian-id : ∀ {x x′} → Cocartesian id (id′ {x} {x′})
cocartesian-id = cartesian^op→cocartesian (cartesian-id _)

invertible→cocartesian
  : ∀ {x y} {f : Hom x y} {x′ y′} {f′ : Hom[ f ] x′ y′}
  → (f-inv : is-invertible f)
  → is-invertible[ f-inv ] f′
  → Cocartesian f f′
invertible→cocartesian f-inv f′-inv =
  cartesian^op→cocartesian $
  invertible→cartesian _ _ (invertible[]→invertible[]^op f′-inv)

cocartesian→weak-epic
  : ∀ {x y} {f : Hom x y}
  → ∀ {x′ y′} {f′ : Hom[ f ] x′ y′}
  → Cocartesian f f′
  → is-weak-epic f′
cocartesian→weak-epic cocart =
  cartesian→weak-monic (ℰ ^total-op) (cocartesian→cartesian^op cocart)

cocartesian-codomain-unique
  : ∀ {x y} {f : Hom x y}
  → ∀ {x′ y′ y″} {f′ : Hom[ f ] x′ y′} {f″ : Hom[ f ] x′ y″}
  → Cocartesian f f′
  → Cocartesian f f″
  → y′ ≅↓ y″
cocartesian-codomain-unique f′-cocart f″-cocart =
  vert-iso^op→vert-iso $
  cartesian-domain-unique (ℰ ^total-op)
    (cocartesian→cartesian^op f″-cocart)
    (cocartesian→cartesian^op f′-cocart)

cocartesian-vert-section-stable
  : ∀ {x y} {f : Hom x y}
  → ∀ {x′ y′ y″} {f′ : Hom[ f ] x′ y′} {f″ : Hom[ f ] x′ y″} {ϕ : Hom[ id ] y″ y′}
  → Cocartesian f f′
  → has-retract↓ ϕ
  → ϕ ∘′ f″ ≡[ idl _ ] f′
  → Cocartesian f f″
cocartesian-vert-section-stable cocart ret factor =
  cartesian^op→cocartesian $
  cartesian-vert-retraction-stable (ℰ ^total-op)
    (cocartesian→cartesian^op cocart)
    (vert-retract→vert-section^op ret)
    factor

cocartesian-pasting
  : ∀ {x y z} {f : Hom y z} {g : Hom x y}
  → ∀ {x′ y′ z′} {f′ : Hom[ f ] y′ z′} {g′ : Hom[ g ] x′ y′}
  → Cocartesian g g′
  → Cocartesian (f ∘ g) (f′ ∘′ g′)
  → Cocartesian f f′
cocartesian-pasting g-cocart fg-cocart =
  cartesian^op→cocartesian $
  cartesian-pasting (ℰ ^total-op)
    (cocartesian→cartesian^op g-cocart)
    (cocartesian→cartesian^op fg-cocart)

vertical+cocartesian→invertible
  : ∀ {x} {x′ x″ : Ob[ x ]} {f′ : Hom[ id ] x′ x″}
  → Cocartesian id f′
  → is-invertible↓ f′
vertical+cocartesian→invertible cocart =
  vert-invertible^op→vert-invertible $
  vertical+cartesian→invertible (ℰ ^total-op)
    (cocartesian→cartesian^op cocart)
```
</details>

## Cocartesian Lifts

We call an object $b'$ over $b$ together with a cartesian arrow
$f' : a \to_{f} b'$ a **cocartesian lift** of $f$.

```agda
record Cocartesian-lift {x y} (f : Hom x y) (x′ : Ob[ x ]) : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′)
  where
  no-eta-equality
  field
    {y′} : Ob[ y ]
    lifting : Hom[ f ] x′ y′
    cocartesian : Cocartesian f lifting
  open Cocartesian cocartesian public
```

<details>
<summary>
We also can apply duality to cocartesian lifts.
</summary>
```agda
cartesian-lift^op→cocartesian-lift
  : ∀ {x y} {f : Hom x y} {x′ : Ob[ x ]}
  → Cartesian-lift (ℰ ^total-op) f x′
  → Cocartesian-lift f x′
cartesian-lift^op→cocartesian-lift cart .Cocartesian-lift.y′ =
  Cartesian-lift.x′ cart
cartesian-lift^op→cocartesian-lift cart .Cocartesian-lift.lifting =
  Cartesian-lift.lifting cart
cartesian-lift^op→cocartesian-lift cart .Cocartesian-lift.cocartesian =
  cartesian^op→cocartesian (Cartesian-lift.cartesian cart)

cocartesian-lift→cartesian-lift^op
  : ∀ {x y} {f : Hom x y} {x′ : Ob[ x ]}
  → Cocartesian-lift f x′
  → Cartesian-lift (ℰ ^total-op) f x′
cocartesian-lift→cartesian-lift^op cocart .Cartesian-lift.x′ =
  Cocartesian-lift.y′ cocart
cocartesian-lift→cartesian-lift^op cocart .Cartesian-lift.lifting =
  Cocartesian-lift.lifting cocart
cocartesian-lift→cartesian-lift^op cocart .Cartesian-lift.cartesian =
  cocartesian→cartesian^op (Cocartesian-lift.cocartesian cocart)
```
</details>

We can use this notion to define cocartesian fibrations (sometimes
referred to as opfibrations).

```agda
record Cocartesian-fibration : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  no-eta-equality
  field
    has-lift : ∀ {x y} (f : Hom x y) (x′ : Ob[ x ]) → Cocartesian-lift f x′
```
<details>
<summary>
As expected, opfibrations are dual to fibrations.
</summary>
```agda
fibration^op→opfibration : Cartesian-fibration (ℰ ^total-op) → Cocartesian-fibration
fibration^op→opfibration fib .Cocartesian-fibration.has-lift f x′ =
  cartesian-lift^op→cocartesian-lift (Cartesian-fibration.has-lift fib f x′)

opfibration→fibration^op : Cocartesian-fibration → Cartesian-fibration (ℰ ^total-op)
opfibration→fibration^op opfib .Cartesian-fibration.has-lift f y′ =
  cocartesian-lift→cartesian-lift^op (Cocartesian-fibration.has-lift opfib f y′)
```
</details>
