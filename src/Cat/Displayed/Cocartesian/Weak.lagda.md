<!--
```agda
open import Cat.Displayed.Cartesian.Weak
open import Cat.Functor.Hom.Displayed
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Total.Op
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Displayed.Cocartesian.Indexing as Indexing
import Cat.Displayed.Morphism.Duality
import Cat.Displayed.Cocartesian as Cocart
import Cat.Displayed.Reasoning
import Cat.Displayed.Morphism
import Cat.Reasoning as CR
```
-->

```agda
module Cat.Displayed.Cocartesian.Weak
  {o ℓ o' ℓ'}
  {ℬ : Precategory o ℓ}
  (ℰ : Displayed ℬ o' ℓ')
  where
```

<!--
```agda
open CR ℬ
open Displayed ℰ
open Cocart ℰ
open Cat.Displayed.Morphism ℰ
open Cat.Displayed.Morphism.Duality ℰ
open Cat.Displayed.Reasoning ℰ
private
  module Fib {x} = Precategory (Fibre ℰ x)
```
-->

# Weak cocartesian morphisms

We can define a weaker notion of [cocartesian morphism] much like we can
with their [cartesian counterparts].

[cocartesian morphism]: Cat.Displayed.Cocartesian.html
[cartesian counterparts]: Cat.Displayed.Cartesian.Weak.html

```agda
record is-weak-cocartesian
  {a b a' b'} (f : Hom a b) (f' : Hom[ f ] a' b')
  : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ')
  where
  no-eta-equality
  field
    universal : ∀ {x'} → (g' : Hom[ f ] a' x') → Hom[ id ] b' x'
    commutes  : ∀ {x'} → (g' : Hom[ f ] a' x') → universal g' ∘' f' ≡[ idl _ ] g'
    unique    : ∀ {x'} {g' : Hom[ f ] a' x'}
              → (h' : Hom[ id ] b' x')
              → h' ∘' f' ≡[ idl _ ] g'
              → h' ≡ universal g'

open is-weak-cocartesian
```

## Duality

Weak cartesian maps in the total opposite category are equivalent to
weak cocartesian maps.

```agda
weak-co-cartesian→weak-cocartesian
  : ∀ {x y} {f : Hom x y} {x' y'} {f' : Hom[ f ] x' y'}
  → is-weak-cartesian (ℰ ^total-op) f f'
  → is-weak-cocartesian f f'

weak-cocartesian→weak-co-cartesian
  : ∀ {x y} {f : Hom x y} {x' y'} {f' : Hom[ f ] x' y'}
  → is-weak-cocartesian f f'
  → is-weak-cartesian (ℰ ^total-op) f f'
```

<details>
<summary>These functions just shuffle data around, so we omit their
definitions.
</summary>

```agda
weak-co-cartesian→weak-cocartesian wcart .is-weak-cocartesian.universal =
  is-weak-cartesian.universal wcart
weak-co-cartesian→weak-cocartesian wcart .is-weak-cocartesian.commutes =
  is-weak-cartesian.commutes wcart
weak-co-cartesian→weak-cocartesian wcart .is-weak-cocartesian.unique =
  is-weak-cartesian.unique wcart

weak-cocartesian→weak-co-cartesian wcocart .is-weak-cartesian.universal =
  is-weak-cocartesian.universal wcocart
weak-cocartesian→weak-co-cartesian wcocart .is-weak-cartesian.commutes =
  is-weak-cocartesian.commutes wcocart
weak-cocartesian→weak-co-cartesian wcocart .is-weak-cartesian.unique =
  is-weak-cocartesian.unique wcocart
```
</details>

Weak cocartesian maps satisfy the dual properties of weak cartesian maps.

```agda
weak-cocartesian-codomain-unique
  : ∀ {x y} {f : Hom x y}
  → ∀ {x' y' y''} {f' : Hom[ f ] x' y'} {f'' : Hom[ f ] x' y''}
  → is-weak-cocartesian f f'
  → is-weak-cocartesian f f''
  → y' ≅↓ y''

cocartesian→weak-cocartesian
  : ∀ {x y x' y'} {f : Hom x y} {f' : Hom[ f ] x' y'}
  → is-cocartesian f f'
  → is-weak-cocartesian f f'

weak-cocartesian→cocartesian
  : ∀ {x y x' y'} {f : Hom x y} {f' : Hom[ f ] x' y'}
  → Cocartesian-fibration
  → is-weak-cocartesian f f'
  → is-cocartesian f f'

precompose-equiv→weak-cocartesian
  : ∀ {x y x' y'} {f : Hom x y}
  → (f' : Hom[ f ] x' y')
  → (∀ {y''} → is-equiv {A = Hom[ id ] y' y''} (_∘' f'))
  → is-weak-cocartesian f f'

weak-cocartesian→precompose-equiv
  : ∀ {x y x' y' y''} {f : Hom x y} {f' : Hom[ f ] x' y'}
  → is-weak-cocartesian f f'
  → is-equiv {A = Hom[ id ] y' y''} (_∘' f')

fibre-precompose-equiv→weak-cocartesian
  : ∀ {x} {x' x'' : Ob[ x ]}
  → (f' : Hom[ id ] x' x'')
  → (∀ {x'''} → is-equiv {A = Hom[ id ] x'' x'''} (Fib._∘ f'))
  → is-weak-cocartesian id f'

weak-cocartesian→fibre-precompose-equiv
  : ∀ {x} {x' x'' x''' : Ob[ x ]} {f' : Hom[ id ] x' x''}
  → is-weak-cocartesian id f'
  → is-equiv {A = Hom[ id ] x'' x'''} (Fib._∘ f')
```

<details>
<summary>The proofs consist of tedious applications of duality.
</summary>

```agda
weak-cocartesian-codomain-unique f'-cocart f''-cocart =
  vertical-co-iso→vertical-iso $
  weak-cartesian-domain-unique (ℰ ^total-op)
    (weak-cocartesian→weak-co-cartesian f''-cocart)
    (weak-cocartesian→weak-co-cartesian f'-cocart)

cocartesian→weak-cocartesian cocart =
  weak-co-cartesian→weak-cocartesian $
  cartesian→weak-cartesian (ℰ ^total-op) $
  cocartesian→co-cartesian cocart

weak-cocartesian→cocartesian opfib wcocart =
  co-cartesian→cocartesian $
  weak-cartesian→cartesian (ℰ ^total-op)
    (opfibration→op-fibration opfib)
    (weak-cocartesian→weak-co-cartesian wcocart)

precompose-equiv→weak-cocartesian f eqv =
  weak-co-cartesian→weak-cocartesian $
  (postcompose-equiv→weak-cartesian (ℰ ^total-op) f eqv)

weak-cocartesian→precompose-equiv cocart =
  weak-cartesian→postcompose-equiv (ℰ ^total-op) $
  weak-cocartesian→weak-co-cartesian cocart

fibre-precompose-equiv→weak-cocartesian f' eqv .universal v =
  equiv→inverse eqv v
fibre-precompose-equiv→weak-cocartesian f' eqv .commutes v =
  to-pathp $ equiv→counit eqv v
fibre-precompose-equiv→weak-cocartesian f' eqv .unique v p =
  sym (equiv→unit eqv v) ∙ ap (equiv→inverse eqv) (from-pathp p)

weak-cocartesian→fibre-precompose-equiv wcocart =
  is-iso→is-equiv $
    iso (wcocart .universal)
      (λ v → from-pathp (wcocart .commutes v))
      (λ v → sym (wcocart .unique v (to-pathp refl)))

```
</details>

Notably, if $\ca{E}$ is a [[Cartesian fibration]], then all weak
cocartesian morphisms are cocartesian.

```agda
fibration+weak-cocartesian→cocartesian
  : ∀ {x y x' y'} {f : Hom x y} {f' : Hom[ f ] x' y'}
  → Cartesian-fibration ℰ
  → is-weak-cocartesian f f'
  → is-cocartesian f f'
fibration+weak-cocartesian→cocartesian {x} {y} {x'} {y'} {f} {f'} fib weak = cocart
  where
    open Cartesian-fibration fib
    module weak = is-weak-cocartesian weak
```

To see show this, we need to construct a unique factorisation of some
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
    module Morphisms {u} {u' : Ob[ u ]} (m : Hom y u) (h' : Hom[ m ∘ f ] x' u') where
      y* : Ob[ y ]
      y* = Cartesian-lift.x' (has-lift m u')

      m* : Hom[ m ] y* u'
      m* =  Cartesian-lift.lifting (has-lift m u')

      module m* = is-cartesian (Cartesian-lift.cartesian (has-lift m u'))
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
      h* : Hom[ f ] x' y*
      h* = m*.universal f h'
```

Finally, we can construct a vertical morphism $h^{**} : y' \to y^{*}$,
as $f'$ is weakly cartesian.

```agda
      h** : Hom[ id ] y' y*
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
    cocart : is-cocartesian f f'
    cocart .is-cocartesian.universal m h' =
      hom[ idr _ ] (m* ∘' h**)
      where open Morphisms m h'
```

Showing that $m^{*} \cdot h^{**} = h'$ is best understood diagrammatically;
both the $m^{*} \cdot h^{*} = h'$ and $h^{**} \cdot f' = h^{*}$ cells
commute.

```agda
    cocart .is-cocartesian.commutes m h' =
      hom[] (m* ∘' h**) ∘' f'   ≡˘⟨ yank _ _ _ ⟩
      m* ∘' hom[] (h** ∘' f')   ≡⟨ ap (m* ∘'_) (from-pathp (weak.commutes _)) ⟩
      m* ∘' m*.universal f h'                 ≡⟨ m*.commutes f h' ⟩
      h' ∎
      where open Morphisms m h'
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
    cocart .is-cocartesian.unique {m = m} {h' = h'} m' p =
      m'                ≡⟨ from-pathp⁻ (symP (m*.commutesp (idr _) m')) ⟩
      hom[] (m* ∘' id*) ≡⟨ hom[]⟩⟨ ap (m* ∘'_) (weak.unique _ (to-pathp $ m*.unique _ path )) ⟩
      hom[] (m* ∘' h**) ∎
      where
        open Morphisms m h'

        id* : Hom[ id ] y' y*
        id* = m*.universalv m'

        path : m* ∘' hom[ idl _ ] (id* ∘' f') ≡ h'
        path =
          m* ∘' hom[] (id* ∘' f') ≡⟨ whisker-r _ ⟩
          hom[] (m* ∘' id* ∘' f') ≡⟨ cancel _ (ap (m ∘_) (idl _)) (pulll' (idr _) (m*.commutesv m')) ⟩
          m' ∘' f'                ≡⟨ p ⟩
          h' ∎
```

## Weak cocartesian lifts

We can also define the dual to [weak cartesian lifts].

[weak cartesian lifts]: Cat.Displayed.Cartesian.Weak.html#Weak-cartesian-lift

```agda
record Weak-cocartesian-lift
  {x y} (f : Hom x y) (x' : Ob[ x ]) : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ')
  where
  no-eta-equality
  field
    {y'}    : Ob[ y ]
    lifting : Hom[ f ] x' y'
    weak-cocartesian : is-weak-cocartesian f lifting

  open is-weak-cocartesian weak-cocartesian public
```


As expected, weak cocartesian lifts are dual to weak cartesian lifts.

```agda
weak-co-cartesian-lift→weak-cocartesian-lift
  : ∀ {x y} {f : Hom x y} {x' : Ob[ x ]}
  → Weak-cartesian-lift (ℰ ^total-op) f x'
  → Weak-cocartesian-lift f x'

weak-cocartesian-lift→weak-co-cartesian-lift
  : ∀ {x y} {f : Hom x y} {x' : Ob[ x ]}
  → Weak-cocartesian-lift f x'
  → Weak-cartesian-lift (ℰ ^total-op) f x'
```

<details>
<summary>We omit the proofs, as they are even more applications of
duality.
</summary>

```agda
weak-co-cartesian-lift→weak-cocartesian-lift wlift .Weak-cocartesian-lift.y' =
  Weak-cartesian-lift.x' wlift
weak-co-cartesian-lift→weak-cocartesian-lift wlift .Weak-cocartesian-lift.lifting =
  Weak-cartesian-lift.lifting wlift
weak-co-cartesian-lift→weak-cocartesian-lift wlift .Weak-cocartesian-lift.weak-cocartesian =
  weak-co-cartesian→weak-cocartesian (Weak-cartesian-lift.weak-cartesian wlift)

weak-cocartesian-lift→weak-co-cartesian-lift wlift .Weak-cartesian-lift.x' =
  Weak-cocartesian-lift.y' wlift
weak-cocartesian-lift→weak-co-cartesian-lift wlift .Weak-cartesian-lift.lifting =
  Weak-cocartesian-lift.lifting wlift
weak-cocartesian-lift→weak-co-cartesian-lift wlift .Weak-cartesian-lift.weak-cartesian =
  weak-cocartesian→weak-co-cartesian (Weak-cocartesian-lift.weak-cocartesian wlift)
```
</details>

A [[displayed category]] with all weak cocartesian lifts is called a
**weak cocartesian fibration**, though we will often refer to them
as **weak opfibrations** These are also sometimes called
**preopfibred categories**, though we avoid this terminology, as it
conflicts with the precategory/category distinction.

```agda
record is-weak-cocartesian-fibration : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
  no-eta-equality
  field
    weak-lift : ∀ {x y} → (f : Hom x y) → (x' : Ob[ x ]) → Weak-cocartesian-lift f x'

  module weak-lift {x y} (f : Hom x y) (x' : Ob[ x ]) =
    Weak-cocartesian-lift (weak-lift f x')
```

<!--
```agda
  rebase : ∀ {x y x' x''} → (f : Hom x y)
           → Hom[ id ] x' x''
           → Hom[ id ] (weak-lift.y' f x') (weak-lift.y' f x'')
  rebase f vert =
    weak-lift.universal f _ (hom[ idr _ ] (weak-lift.lifting f _ ∘' vert))
```
-->

Weak opfibrations are dual to [weak fibrations].

[weak fibrations]: Cat.Displayed.Cartesian.Weak.html#is-weak-cartesian-fibration

```agda
weak-op-fibration→weak-opfibration
  : is-weak-cartesian-fibration (ℰ ^total-op)
  → is-weak-cocartesian-fibration

weak-opfibration→weak-op-fibration
  : is-weak-cocartesian-fibration
  → is-weak-cartesian-fibration (ℰ ^total-op)
```


<details>
<summary>As usual, we omit the duality proofs, as they are quite tedious.
</summary>
```agda
weak-op-fibration→weak-opfibration wlift .is-weak-cocartesian-fibration.weak-lift f x' =
  weak-co-cartesian-lift→weak-cocartesian-lift $
  is-weak-cartesian-fibration.weak-lift wlift f x'

weak-opfibration→weak-op-fibration wlift .is-weak-cartesian-fibration.weak-lift f y' =
  weak-cocartesian-lift→weak-co-cartesian-lift $
  is-weak-cocartesian-fibration.weak-lift wlift f y'
```
</details>

Every opfibration is a weak opfibration.

```agda
cocartesian-lift→weak-cocartesian-lift
  : ∀ {x y} {f : Hom x y} {x' : Ob[ x ]}
  → Cocartesian-lift f x'
  → Weak-cocartesian-lift f x'

opfibration→weak-opfibration
  : Cocartesian-fibration
  → is-weak-cocartesian-fibration
```

<!--
```agda
cocartesian-lift→weak-cocartesian-lift cocart .Weak-cocartesian-lift.y' =
  Cocartesian-lift.y' cocart
cocartesian-lift→weak-cocartesian-lift cocart .Weak-cocartesian-lift.lifting =
  Cocartesian-lift.lifting cocart
cocartesian-lift→weak-cocartesian-lift cocart .Weak-cocartesian-lift.weak-cocartesian =
  cocartesian→weak-cocartesian (Cocartesian-lift.cocartesian cocart)

opfibration→weak-opfibration opfib .is-weak-cocartesian-fibration.weak-lift f x' =
  cocartesian-lift→weak-cocartesian-lift (Cocartesian-fibration.has-lift opfib f x')
```
-->



A weak opfibration is an opfibration when weak cocartesian morphisms are
closed under composition. This follows via duality.

```agda
weak-opfibration→opfibration
  : is-weak-cocartesian-fibration
  → (∀ {x y z x' y' z'} {f : Hom y z} {g : Hom x y}
     → {f' : Hom[ f ] y' z'} {g' : Hom[ g ] x' y'}
     → is-weak-cocartesian f f' → is-weak-cocartesian g g'
     → is-weak-cocartesian (f ∘ g) (f' ∘' g'))
  → Cocartesian-fibration
weak-opfibration→opfibration wopfib weak-∘ =
  op-fibration→opfibration $
  weak-fibration→fibration (ℰ ^total-op)
  (weak-opfibration→weak-op-fibration wopfib)
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
cartesian+weak-opfibration→opfibration
  : Cartesian-fibration ℰ
  → is-weak-cocartesian-fibration
  → Cocartesian-fibration
cartesian+weak-opfibration→opfibration fib wlifts =
  weak-opfibration→opfibration wlifts λ f-weak g-weak →
    cocartesian→weak-cocartesian $
    cocartesian-∘
      (fibration+weak-cocartesian→cocartesian fib f-weak)
      (fibration+weak-cocartesian→cocartesian fib g-weak)
```

# Weak opfibrations and equivalence of Hom sets

If $\cE$ is a weak opfibration, then the hom sets $x' \to_f y'$ and
$f^{*}(x') \to_{id} y'$ are equivalent, where $f^{*}(x')$ is the codomain
of the lift of $f$ along $y'$.

```agda
module _ (wopfib : is-weak-cocartesian-fibration) where
  open is-weak-cocartesian-fibration wopfib

  weak-opfibration→universal-is-equiv
    : ∀ {x y y' x'}
    → (u : Hom x y)
    → is-equiv (weak-lift.universal u x' {y'})
  weak-opfibration→universal-is-equiv {x' = x'} u =
    is-iso→is-equiv $
    iso (λ u' → hom[ idl u ] (u' ∘' weak-lift.lifting u x'))
        (λ u' → sym $ weak-lift.unique u x' u' (to-pathp refl))
        (λ u' → cancel _ _ (weak-lift.commutes u x' u'))

  weak-opfibration→vertical-equiv
    : ∀ {x y x' y'}
    → (u : Hom x y)
    → Hom[ u ] x' y' ≃ Hom[ id ] (weak-lift.y' u x') y'
  weak-opfibration→vertical-equiv {x' = x'} u =
    weak-lift.universal u x' , weak-opfibration→universal-is-equiv u
```

Furthermore, this equivalence is natural.

```agda
  weak-opfibration→hom-iso-from
    : ∀ {x y x'} (u : Hom x y)
    → Hom-over-from ℰ u x' ≅ⁿ Hom-from (Fibre ℰ y) (weak-lift.y' u x')
  weak-opfibration→hom-iso-from {y = y} {x' = x'} u = to-natural-iso mi where
    open make-natural-iso

    u*x' : Ob[ y ]
    u*x' = weak-lift.y' u x'

    mi : make-natural-iso (Hom-over-from ℰ u x') (Hom-from (Fibre ℰ y) u*x')
    mi .eta x u' = weak-lift.universal u x' u'
    mi .inv x v' = hom[ idl u ] (v' ∘' weak-lift.lifting u x')
    mi .eta∘inv _ = funext λ v' →
      sym $ weak-lift.unique u _ _ (to-pathp refl)
    mi .inv∘eta _ = funext λ u' →
      from-pathp $ weak-lift.commutes u _ _
    mi .natural _ _ v' = funext λ u' →
      weak-lift.unique _ _ _ $ to-pathp $
        smashl _ _
      ∙ weave _ (ap (_∘ u) (idl id)) _ (pullr' _ (weak-lift.commutes _ _ _))
```

As in the [weak cartesian case], the converse is also true: if there is
a lifting of objects `Ob[ x ] → Ob[ y ]` for every morphism $f : x \to y$
in $\cB$, along with a equivalence of homs as above, then $\cE$ is a weak
opfibration.

[weak cartesian case]: Cat.Displayed.Cartesian.Weak.html#weak-fibrations-and-equivalence-of-hom-sets

```agda
module _ (_*₀_ : ∀ {x y} → Hom x y → Ob[ x ] → Ob[ y ]) where

  private
    vertical-equiv-iso-natural
      : (∀ {x y x' y'} {f : Hom x y} → Hom[ f ] x' y' → Hom[ id ] (f *₀ x') y')
      → Type _
    vertical-equiv-iso-natural to =
      ∀ {x y x' y' y''} {g : Hom x y}
      → (f' : Hom[ id ] y' y'') (g' : Hom[ g ] x' y')
      → to (hom[ idl g ] (f' ∘' g')) ≡[ sym (idl id) ] f' ∘' to g'

  vertical-equiv→weak-opfibration
    : (to : ∀ {x y x' y'} {f : Hom x y} → Hom[ f ] x' y' → Hom[ id ] (f *₀ x') y')
    → (eqv : ∀ {x y x' y'} {f : Hom x y} → is-equiv (to {x} {y} {x'} {y'} {f}))
    → (natural : vertical-equiv-iso-natural to)
    → is-weak-cocartesian-fibration
  vertical-equiv→weak-opfibration to to-eqv natural =
    weak-op-fibration→weak-opfibration $
    vertical-equiv→weak-fibration (ℰ ^total-op) _*₀_ to to-eqv λ f' g' →
      to-pathp (reindex _ _ ∙ from-pathp (natural g' f'))
```

<!--
```agda
module _ (U : ∀ {x y} → Hom x y → Functor (Fibre ℰ x) (Fibre ℰ y)) where
  open Functor
  open _=>_

  hom-iso→weak-opfibration
    : (∀ {x y x'} (u : Hom x y)
       → Hom-over-from ℰ u x' ≅ⁿ Hom-from (Fibre ℰ y) (U u .F₀ x'))
    → is-weak-cocartesian-fibration
  hom-iso→weak-opfibration hom-iso =
    vertical-equiv→weak-opfibration
      (λ u → U u .F₀)
      (λ u' → Isoⁿ.to (hom-iso _) .η _ u')
      (natural-iso-to-is-equiv (hom-iso _) _)
      λ f' g' → to-pathp⁻ $
        happly (Isoⁿ.to (hom-iso _) .is-natural _ _ f') g'
```
-->

<!--
```agda
module _ (opfib : Cocartesian-fibration) where
  open Cocartesian-fibration opfib
  open Indexing ℰ opfib

  opfibration→hom-iso-from
    : ∀ {x y x'} (u : Hom x y)
    → Hom-over-from ℰ u x' ≅ⁿ Hom-from (Fibre ℰ y) (has-lift.y' u x')
  opfibration→hom-iso-from u =
    weak-opfibration→hom-iso-from (opfibration→weak-opfibration opfib) u

  opfibration→hom-iso-into
    : ∀ {x y y'} (u : Hom x y)
    → Hom-over-into ℰ u y' ≅ⁿ Hom-into (Fibre ℰ y) y' F∘ Functor.op (cobase-change u)
  opfibration→hom-iso-into {y = y} {y' = y'} u = to-natural-iso mi where
    open make-natural-iso

    mi : make-natural-iso
           (Hom-over-into ℰ u y')
           (Hom-into (Fibre ℰ y) y' F∘ Functor.op (cobase-change u) )
    mi .eta x u' = has-lift.universalv u x u'
    mi .inv x v' = hom[ idl u ] (v' ∘' has-lift.lifting u _)
    mi .eta∘inv x = funext λ v' →
      sym $ has-lift.uniquev u _ _ (to-pathp refl)
    mi .inv∘eta x = funext λ u' →
      from-pathp (has-lift.commutesv u _ _)
    mi .natural _ _ v' = funext λ u' →
      has-lift.unique u _ _ $ to-pathp $
        smashl _ _
        ·· revive₁ (pullr[] _ (has-lift.commutesv u _ _))
        ·· smashr _ _
        ·· weave _ (pulll (idl u)) _ (pulll[] _ (has-lift.commutesv u _ _))
        ·· duplicate id-comm _ (idr u)

  opfibration→hom-iso
    : ∀ {x y} (u : Hom x y)
    → Hom-over ℰ u ≅ⁿ Hom[-,-] (Fibre ℰ y) F∘ (Functor.op (cobase-change u) F× Id)
  opfibration→hom-iso {y = y} u = to-natural-iso mi where
    open make-natural-iso
    open _=>_
    open Functor

    module into-iso {y'} = Isoⁿ (opfibration→hom-iso-into {y' = y'} u)
    module from-iso {x'} = Isoⁿ (opfibration→hom-iso-from {x' = x'} u)
    module Fibre {x} = CR (Fibre ℰ x)

    mi : make-natural-iso
           (Hom-over ℰ u)
           (Hom[-,-] (Fibre ℰ y) F∘ (Functor.op (cobase-change u) F× Id))
    mi .eta x u' = has-lift.universalv u _ u'
    mi .inv x v' = hom[ idl u ] (v' ∘' has-lift.lifting u _)
    mi .eta∘inv x = funext λ v' →
      sym $ has-lift.uniquev u _ _ (to-pathp refl)
    mi .inv∘eta x = funext λ u' →
      from-pathp (has-lift.commutesv u _ _)
    mi .natural _ _ (v₁' , v₂') = funext λ u' →
      Fibre.pulll (sym (happly (from-iso.to .is-natural _ _ v₂') u'))
      ·· sym (happly (into-iso.to .is-natural _ _ v₁') (hom[ idl _ ] (v₂' ∘' u')))
      ·· ap (into-iso.to .η _) (smashl _ _ ∙ sym assoc[])

  opfibration→universal-is-equiv
    : ∀ {x y x' y'}
    → (u : Hom x y)
    → is-equiv (has-lift.universalv u y' {x'})
  opfibration→universal-is-equiv u =
    weak-opfibration→universal-is-equiv (opfibration→weak-opfibration opfib) u

  opfibration→vertical-equiv
    : ∀ {x y x' y'}
    → (u : Hom x y)
    → Hom[ u ] x' y' ≃ Hom[ id ] (has-lift.y' u x') y'
  opfibration→vertical-equiv u =
   weak-opfibration→vertical-equiv (opfibration→weak-opfibration opfib) u
```
-->
