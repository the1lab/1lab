```agda
open import Cat.Displayed.Base
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Weak
open import Cat.Displayed.Total.Op
open import Cat.Prelude

import Cat.Displayed.Cocartesian as Cocart
import Cat.Displayed.Morphism
import Cat.Displayed.Morphism.Duality
import Cat.Displayed.Reasoning

module Cat.Displayed.Cocartesian.Weak
  {o ℓ o′ ℓ′}
  {ℬ : Precategory o ℓ}
  (ℰ : Displayed ℬ o′ ℓ′)
  where
```

<!--
```agda
open Precategory ℬ
open Displayed ℰ
open Cocart ℰ
open Cat.Displayed.Morphism ℰ
open Cat.Displayed.Morphism.Duality ℰ
open Cat.Displayed.Reasoning ℰ
```
-->

# Weak Cocartesian Morphisms

We can define a weaker notion of [cocartesian morphism] much like we can
with their [cartesian counterparts].

[cocartesian morphism]: Cat.Displayed.Cocartesian.html
[cartesian counterparts]: Cat.Displayed.Cartesian.Weak.html

```agda
record Weak-cocartesian
  {a b a′ b′} (f : Hom a b) (f′ : Hom[ f ] a′ b′)
  : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′)
  where
  no-eta-equality
  field
    universal : ∀ {x′} → (g′ : Hom[ f ] a′ x′) → Hom[ id ] b′ x′
    commutes  : ∀ {x′} → (g′ : Hom[ f ] a′ x′) → universal g′ ∘′ f′ ≡[ idl _ ] g′
    unique    : ∀ {x′} {g′ : Hom[ f ] a′ x′}
              → (h′ : Hom[ id ] b′ x′)
              → h′ ∘′ f′ ≡[ idl _ ] g′
              → h′ ≡ universal g′
```

## Duality


Weak cartesian maps in the total opposite category are equivalent to
weak cocartesian maps.

```agda
weak-co-cartesian→weak-cocartesian
  : ∀ {x y} {f : Hom x y} {x′ y′} {f′ : Hom[ f ] x′ y′}
  → Weak-cartesian (ℰ ^total-op) f f′
  → Weak-cocartesian f f′

weak-cocartesian→weak-co-cartesian
  : ∀ {x y} {f : Hom x y} {x′ y′} {f′ : Hom[ f ] x′ y′}
  → Weak-cocartesian f f′
  → Weak-cartesian (ℰ ^total-op) f f′
```

<details>
<summary>These functions just shuffle data around, so we omit their
definitions.
</summary>

```agda
weak-co-cartesian→weak-cocartesian wcart .Weak-cocartesian.universal =
  Weak-cartesian.universal wcart
weak-co-cartesian→weak-cocartesian wcart .Weak-cocartesian.commutes =
  Weak-cartesian.commutes wcart
weak-co-cartesian→weak-cocartesian wcart .Weak-cocartesian.unique =
  Weak-cartesian.unique wcart

weak-cocartesian→weak-co-cartesian wcocart .Weak-cartesian.universal =
  Weak-cocartesian.universal wcocart
weak-cocartesian→weak-co-cartesian wcocart .Weak-cartesian.commutes =
  Weak-cocartesian.commutes wcocart
weak-cocartesian→weak-co-cartesian wcocart .Weak-cartesian.unique =
  Weak-cocartesian.unique wcocart
```
</details>

Weak cocartesian maps satisfy the dual properties of weak cartesian maps.

```agda
weak-cocartesian-codomain-unique
  : ∀ {x y} {f : Hom x y}
  → ∀ {x′ y′ y″} {f′ : Hom[ f ] x′ y′} {f″ : Hom[ f ] x′ y″}
  → Weak-cocartesian f f′
  → Weak-cocartesian f f″
  → y′ ≅↓ y″

cocartesian→weak-cocartesian
  : ∀ {x y x′ y′} {f : Hom x y} {f′ : Hom[ f ] x′ y′}
  → Cocartesian f f′
  → Weak-cocartesian f f′

weak-cocartesian→cocartesian
  : ∀ {x y x′ y′} {f : Hom x y} {f′ : Hom[ f ] x′ y′}
  → Cocartesian-fibration
  → Weak-cocartesian f f′
  → Cocartesian f f′
```

<details>
<summary>The proofs consist of tedious applications of duality.
</summary>

```agda
weak-cocartesian-codomain-unique f′-cocart f″-cocart =
  vertical-co-iso→vertical-iso $
  weak-cartesian-domain-unique (ℰ ^total-op)
    (weak-cocartesian→weak-co-cartesian f″-cocart)
    (weak-cocartesian→weak-co-cartesian f′-cocart)

cocartesian→weak-cocartesian cocart =
  weak-co-cartesian→weak-cocartesian $
  cartesian→weak-cartesian (ℰ ^total-op) $
  cocartesian→co-cartesian cocart

weak-cocartesian→cocartesian opfib wcocart =
  co-cartesian→cocartesian $
  weak-cartesian→cartesian (ℰ ^total-op)
    (opfibration→op-fibration opfib)
    (weak-cocartesian→weak-co-cartesian wcocart)
```
</details>

Notably, if $\ca{E}$ is a cartesian fibration, then all weak cocartesian
morphisms are cocartesian.

```agda
fibration+weak-cocartesian→cocartesian
  : ∀ {x y x′ y′} {f : Hom x y} {f′ : Hom[ f ] x′ y′}
  → Cartesian-fibration ℰ
  → Weak-cocartesian f f′
  → Cocartesian f f′
fibration+weak-cocartesian→cocartesian {x} {y} {x′} {y′} {f} {f′} fib weak = cocart
  where
    open Cartesian-fibration fib
    module weak = Weak-cocartesian weak
```

To see show this, we need to construct a unique factorization of some
morphism $h' : x' \to_{mf} u'$, as depicted in the following diagram

~~~{.quiver .tall-2}
\begin{tikzcd}
  && {} && {u'} \\
  {x'} && {y'} \\
  &&&& u \\
  x && y
  \arrow[lies over, from=2-1, to=4-1]
  \arrow[lies over, from=2-3, to=4-3]
  \arrow["{f'}"{description}, from=2-1, to=2-3]
  \arrow["f"{description}, from=4-1, to=4-3]
  \arrow["m", from=4-3, to=3-5]
  \arrow[color={rgb,255:red,92;green,214;blue,92}, dashed, from=2-3, to=1-5]
  \arrow["{h'}", curve={height=-30pt}, from=2-1, to=1-5]
  \arrow[lies over, from=1-5, to=3-5]
\end{tikzcd}
~~~

We start by taking the cartesian lift of $m$ to obtain the map $m^{*}$,
which we have highlighted in red.

~~~{.quiver .tall-2}
\begin{tikzcd}
  && \textcolor{rgb,255:red,214;green,92;blue,92}{y^{*}} && {u'} \\
  {x'} && {y'} \\
  &&&& u \\
  x && y
  \arrow[lies over, from=2-1, to=4-1]
  \arrow[lies over, from=2-3, to=4-3]
  \arrow["{f'}"{description}, from=2-1, to=2-3]
  \arrow["f"{description}, from=4-1, to=4-3]
  \arrow["m", from=4-3, to=3-5]
  \arrow[color={rgb,255:red,92;green,214;blue,92}, dashed, from=2-3, to=1-5]
  \arrow["{h'}", curve={height=-50pt}, from=2-1, to=1-5]
  \arrow[lies over, from=1-5, to=3-5]
  \arrow["{m^{*}}", color={rgb,255:red,214;green,92;blue,92}, from=1-3, to=1-5]
\end{tikzcd}
~~~

```agda
    module Morphisms {u} {u′ : Ob[ u ]} (m : Hom y u) (h′ : Hom[ m ∘ f ] x′ u′) where
      y* : Ob[ y ]
      y* = Cartesian-lift.x′ (has-lift m u′)

      m* : Hom[ m ] y* u′
      m* =  Cartesian-lift.lifting (has-lift m u′)

      module m* = Cartesian (Cartesian-lift.cartesian (has-lift m u′))
```

Next, we can construct the morphism $h^{*}$ (highlighted in red) as the
universal factorisation of $h'$ through $m^{*}$.

~~~{.quiver .tall-2}
\begin{tikzcd}
  && {y^{*}} && {u'} \\
  {x'} && {y'} \\
  &&&& u \\
  x && y
  \arrow[lies over, from=2-1, to=4-1]
  \arrow[lies over, from=2-3, to=4-3]
  \arrow["{f'}"{description}, from=2-1, to=2-3]
  \arrow["f"{description}, from=4-1, to=4-3]
  \arrow["m", from=4-3, to=3-5]
  \arrow[color={rgb,255:red,92;green,214;blue,92}, dashed, from=2-3, to=1-5]
  \arrow["{h'}", curve={height=-50pt}, from=2-1, to=1-5]
  \arrow[lies over, from=1-5, to=3-5]
  \arrow["{m^{*}}", from=1-3, to=1-5]
  \arrow["{h^{*}}", color={rgb,255:red,214;green,92;blue,92}, from=2-1, to=1-3]
\end{tikzcd}
~~~

```agda
      h* : Hom[ f ] x′ y*
      h* = m*.universal f h′
```

Finally, we can construct a vertical morphism $h^{**} : y' \to y^{*}$,
as $f'$ is weakly cartesian.

```agda
      h** : Hom[ id ] y′ y*
      h** = weak.universal h*
```

~~~{.quiver .tall-2}
\begin{tikzcd}
  && {y^{*}} && {u'} \\
  {x'} && {y'} \\
  &&&& u \\
  x && y
  \arrow[lies over, from=2-1, to=4-1]
  \arrow[lies over, from=2-3, to=4-3]
  \arrow["{f'}"{description}, from=2-1, to=2-3]
  \arrow["f"{description}, from=4-1, to=4-3]
  \arrow["m", from=4-3, to=3-5]
  \arrow[color={rgb,255:red,92;green,214;blue,92}, dashed, from=2-3, to=1-5]
  \arrow["{h'}", curve={height=-50pt}, from=2-1, to=1-5]
  \arrow[lies over, from=1-5, to=3-5]
  \arrow["{m^{*}}", from=1-3, to=1-5]
  \arrow["{h^{*}}", from=2-1, to=1-3]
  \arrow["{h^{**}}", color={rgb,255:red,214;green,92;blue,92}, from=2-3, to=1-3]
\end{tikzcd}
~~~

Composing $m^{*}$ and $h^{**}$ gives the desired factorisation.

```agda
    cocart : Cocartesian f f′
    cocart .Cocart.Cocartesian.universal m h′ =
      hom[ idr _ ] (m* ∘′ h**)
      where open Morphisms m h′
```

Showing that $m^{*} \cdot h^{**} = h'$ is best understood diagramatically;
both the $m^{*} \cdot h^{*} = h'$ and $h^{**} \cdot f' = h^{*}$ cells
commute.

```agda
    cocart .Cocart.Cocartesian.commutes m h′ =
      hom[] (m* ∘′ h**) ∘′ f′   ≡˘⟨ yank _ _ _ ⟩
      m* ∘′ hom[] (h** ∘′ f′)   ≡⟨ ap (m* ∘′_) (from-pathp (weak.commutes _)) ⟩
      m* ∘′ m*.universal f h′                 ≡⟨ m*.commutes f h′ ⟩
      h′ ∎
      where open Morphisms m h′
```

Uniqueness is somewhat more delicate. We need to show that the blue cell
in the following diagram commutes.

~~~{.quiver .tall-2}
\begin{tikzcd}
  && {y^{*}} && {u'} \\
  {x'} && {y'} \\
  &&&& u \\
  x && y
  \arrow[lies over, from=2-1, to=4-1]
  \arrow[lies over, from=2-3, to=4-3]
  \arrow["{f'}"{description}, from=2-1, to=2-3]
  \arrow["f"{description}, from=4-1, to=4-3]
  \arrow["m", from=4-3, to=3-5]
  \arrow["{m'}"', color={rgb,255:red,92;green,92;blue,214}, from=2-3, to=1-5]
  \arrow["{h'}", curve={height=-50pt}, from=2-1, to=1-5]
  \arrow[lies over, from=1-5, to=3-5]
  \arrow["{m^{*}}", color={rgb,255:red,92;green,92;blue,214}, from=1-3, to=1-5]
  \arrow["{h^{*}}", from=2-1, to=1-3]
  \arrow["{h^{**}}", color={rgb,255:red,92;green,92;blue,214}, from=2-3, to=1-3]
\end{tikzcd}
~~~

As a general fact, every morphism in a cartesian fibration factors into
a composite of a cartesian and vertical morphism, obtained by taking
the universal factorisation of $m' : y' \to{m \cdot i} u'$. We shall
denote this morphism as $id*$.

~~~{.quiver .tall-2}
\begin{tikzcd}
  && {y^{*}} && {u'} \\
  {x'} && {y'} \\
  &&&& u \\
  x && y
  \arrow[lies over, from=2-1, to=4-1]
  \arrow[lies over, from=2-3, to=4-3]
  \arrow["{f'}"{description}, from=2-1, to=2-3]
  \arrow["f"{description}, from=4-1, to=4-3]
  \arrow["m", from=4-3, to=3-5]
  \arrow["{m'}"', from=2-3, to=1-5]
  \arrow["{h'}", curve={height=-50pt}, from=2-1, to=1-5]
  \arrow[lies over, from=1-5, to=3-5]
  \arrow["{m^{*}}", from=1-3, to=1-5]
  \arrow["{h^{*}}", from=2-1, to=1-3]
  \arrow["{h^{**}}", curve={height=-6pt}, from=2-3, to=1-3]
  \arrow["{id^{*}}"', color={rgb,255:red,214;green,92;blue,92}, curve={height=6pt}, from=2-3, to=1-3]
\end{tikzcd}
~~~

However, $h^{**}$ is the *unique* vertical map that factorises $f'$
through $h^{*}$, so it suffices to show that the cell highlighted in
blue commutes.

~~~{.quiver .tall-2}
\begin{tikzcd}
  && {y^{*}} && {u'} \\
  {x'} && {y'} \\
  &&&& u \\
  x && y
  \arrow[lies over, from=2-1, to=4-1]
  \arrow[lies over, from=2-3, to=4-3]
  \arrow["{f'}"{description}, color={rgb,255:red,92;green,92;blue,214}, from=2-1, to=2-3]
  \arrow["f"{description}, from=4-1, to=4-3]
  \arrow["m", from=4-3, to=3-5]
  \arrow["{m'}"', from=2-3, to=1-5]
  \arrow["{h'}", curve={height=-50pt}, from=2-1, to=1-5]
  \arrow[lies over, from=1-5, to=3-5]
  \arrow["{m^{*}}", from=1-3, to=1-5]
  \arrow["{h^{*}}", color={rgb,255:red,92;green,92;blue,214}, from=2-1, to=1-3]
  \arrow["{h^{**}}", curve={height=-6pt}, from=2-3, to=1-3]
  \arrow["{id^{*}}"', color={rgb,255:red,92;green,92;blue,214}, curve={height=6pt}, from=2-3, to=1-3]
\end{tikzcd}
~~~

$h^{*}$ is the unique vertical map that factorises $h'$ through $m'$,
and $h' = m' \cdot f'$ by our hypothesis, so it suffices to show that
$m^{*} \cdot id^{*} \cdot f' = m' \cdot f'$. This commutes because
$m^{*}$ is cartesian, thus finishing the proof.

```agda
    cocart .Cocart.Cocartesian.unique {m = m} {h′ = h′} m′ p =
      m′                ≡⟨ from-pathp⁻ (symP (m*.commutesp (idr _) m′)) ⟩
      hom[] (m* ∘′ id*) ≡⟨ hom[]⟩⟨ ap (m* ∘′_) (weak.unique _ (to-pathp $ m*.unique _ path )) ⟩
      hom[] (m* ∘′ h**) ∎
      where
        open Morphisms m h′

        id* : Hom[ id ] y′ y*
        id* = m*.universal′ (idr _) m′

        path : m* ∘′ hom[ idl _ ] (id* ∘′ f′) ≡ h′
        path =
          m* ∘′ hom[] (id* ∘′ f′) ≡⟨ whisker-r _ ⟩
          hom[] (m* ∘′ id* ∘′ f′) ≡⟨ cancel _ (ap (m ∘_) (idl _)) (pulll′ (idr _) (m*.commutesp (idr _) m′)) ⟩
          m′ ∘′ f′                ≡⟨ p ⟩
          h′ ∎
```

## Weak cocartesian lifts

We can also define the dual to [weak cartesian lifts].

[weak cartesian lifts]: Cat.Displayed.Cartesian.Weak.html#Weak-cartesian-lift

```agda
record Weak-cocartesian-lift
  {x y} (f : Hom x y) (x′ : Ob[ x ]) : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′)
  where
  no-eta-equality
  field
    {y′}    : Ob[ y ]
    lifting : Hom[ f ] x′ y′
    weak-cocartesian : Weak-cocartesian f lifting

  open Weak-cocartesian weak-cocartesian public
```

As expected, weak cocartesian lifts are dual to weak cartesian lifts.

```agda
weak-co-cartesian-lift→weak-cocartesian-lift
  : ∀ {x y} {f : Hom x y} {x′ : Ob[ x ]}
  → Weak-cartesian-lift (ℰ ^total-op) f x′
  → Weak-cocartesian-lift f x′

weak-cocartesian-lift→weak-co-cartesian-lift
  : ∀ {x y} {f : Hom x y} {x′ : Ob[ x ]}
  → Weak-cocartesian-lift f x′
  → Weak-cartesian-lift (ℰ ^total-op) f x′
```

<details>
<summary>We omit the proofs, as they are even more applications of
duality.
</summary>

```agda
weak-co-cartesian-lift→weak-cocartesian-lift wlift .Weak-cocartesian-lift.y′ =
  Weak-cartesian-lift.x′ wlift
weak-co-cartesian-lift→weak-cocartesian-lift wlift .Weak-cocartesian-lift.lifting =
  Weak-cartesian-lift.lifting wlift
weak-co-cartesian-lift→weak-cocartesian-lift wlift .Weak-cocartesian-lift.weak-cocartesian =
  weak-co-cartesian→weak-cocartesian (Weak-cartesian-lift.weak-cartesian wlift)

weak-cocartesian-lift→weak-co-cartesian-lift wlift .Weak-cartesian-lift.x′ =
  Weak-cocartesian-lift.y′ wlift
weak-cocartesian-lift→weak-co-cartesian-lift wlift .Weak-cartesian-lift.lifting =
  Weak-cocartesian-lift.lifting wlift
weak-cocartesian-lift→weak-co-cartesian-lift wlift .Weak-cartesian-lift.weak-cartesian =
  weak-cocartesian→weak-co-cartesian (Weak-cocartesian-lift.weak-cocartesian wlift)
```
</details>

A displayed category with all weak cocartesian lifts is called a
**preopfibered category**. A preopfibred category is opfibered when
weak cocartesian morphisms are closed under composition. This follows
via duality.

```agda
weak-cocartesian-lifts→opfibration
  : (lifts : ∀ {x y} → (f : Hom x y) → (x′ : Ob[ x ]) → Weak-cocartesian-lift f x′)
  → (∀ {x y z x′ y′ z′} {f : Hom y z} {g : Hom x y}
     → {f′ : Hom[ f ] y′ z′} {g′ : Hom[ g ] x′ y′}
     → Weak-cocartesian f f′ → Weak-cocartesian g g′
     → Weak-cocartesian (f ∘ g) (f′ ∘′ g′))
  → Cocartesian-fibration
weak-cocartesian-lifts→opfibration wlifts weak-∘ =
  op-fibration→opfibration $
  weak-cartesian-lifts→fibration (ℰ ^total-op)
  (λ f y′ → weak-cocartesian-lift→weak-co-cartesian-lift (wlifts f y′))
  (λ f g →
    weak-cocartesian→weak-co-cartesian $
    weak-∘
      (weak-co-cartesian→weak-cocartesian g)
      (weak-co-cartesian→weak-cocartesian f))
```

If $\ca{E}$ is cartesian, we can drop the requirement that weak
cocartesian maps are closed under composition, thanks to
`fibration+weak-cocartesian→cocartesian`{.Agda}.

```agda
cartesian+weak-cocartesian-lifts→opfibration
  : Cartesian-fibration ℰ
  → (∀ {x y} → (f : Hom x y) → (x′ : Ob[ x ]) → Weak-cocartesian-lift f x′)
  → Cocartesian-fibration
cartesian+weak-cocartesian-lifts→opfibration fib wlifts =
  weak-cocartesian-lifts→opfibration wlifts λ f-weak g-weak →
    cocartesian→weak-cocartesian $
    cocartesian-∘
      (fibration+weak-cocartesian→cocartesian fib f-weak)
      (fibration+weak-cocartesian→cocartesian fib g-weak)
```
