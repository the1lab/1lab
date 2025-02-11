<!--
```agda
open import Cat.Displayed.Cartesian.Weak
open import Cat.Functor.Hom.Displayed
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Total.Op
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Displayed.Fibre
open import Cat.Functor.Adjoint.Hom
open import Cat.Functor.Adjoint
open import Cat.Displayed.Base
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Displayed.Cocartesian.Indexing
import Cat.Displayed.Cartesian.Indexing
import Cat.Displayed.Morphism.Duality
import Cat.Displayed.Cocartesian as Cocart
import Cat.Displayed.Fibre.Reasoning
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
  module Fib = Cat.Displayed.Fibre.Reasoning ℰ
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
  → (∀ {y''} → is-equiv {A = Hom[ id ] y' y''} (λ h' → hom[ idl _ ] (h' ∘' f')))
  → is-weak-cocartesian f f'

weak-cocartesian→precompose-equiv
  : ∀ {x y x' y' y''} {f : Hom x y} {f' : Hom[ f ] x' y'}
  → is-weak-cocartesian f f'
  → is-equiv {A = Hom[ id ] y' y''} (λ h' → hom[ idl _ ] (h' ∘' f'))

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

fibre-precompose-equiv→weak-cocartesian f' eqv .is-weak-cocartesian.universal v =
  equiv→inverse eqv v
fibre-precompose-equiv→weak-cocartesian f' eqv .is-weak-cocartesian.commutes v =
  to-pathp $ equiv→counit eqv v
fibre-precompose-equiv→weak-cocartesian f' eqv .is-weak-cocartesian.unique v p =
  sym (equiv→unit eqv v) ∙ ap (equiv→inverse eqv) (from-pathp p)

weak-cocartesian→fibre-precompose-equiv wcocart =
  is-iso→is-equiv $
    iso universal
      (λ v → from-pathp (commutes v))
      (λ v → sym (unique v (to-pathp refl)))
  where open is-weak-cocartesian wcocart
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
    open Cartesian-fibration ℰ fib
    module weak = is-weak-cocartesian weak
```

To see show this, we need to construct a unique factorisation of some
morphism $h' : x' \to_{mf} u'$, as depicted in the following diagram

~~~{.quiver}
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

~~~{.quiver}
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

Next, we can construct the morphism $h^{*}$ (highlighted in red) as the
universal factorisation of $h'$ through $m^{*}$.

~~~{.quiver}
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
    module Morphisms {u} {u' : Ob[ u ]} (m : Hom y u) (h' : Hom[ m ∘ f ] x' u') where
      h* : Hom[ f ] x' (m ^* u')
      h* = π*.universal f h'
```

Finally, we can construct a vertical morphism $h^{**} : y' \to y^{*}$,
as $f'$ is weakly cartesian.

```agda
      h** : Hom[ id ] y' (m ^* u')
      h** = weak.universal h*
```

~~~{.quiver}
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
      hom[ idr _ ] (π* m _ ∘' h**)
      where open Morphisms m h'
```

Showing that $m^{*} \cdot h^{**} = h'$ is best understood diagrammatically;
both the $m^{*} \cdot h^{*} = h'$ and $h^{**} \cdot f' = h^{*}$ cells
commute.

```agda
    cocart .is-cocartesian.commutes m h' =
      hom[] (π* m _ ∘' h**) ∘' f'   ≡˘⟨ yank _ _ _ ⟩
      π* m _ ∘' hom[] (h** ∘' f')   ≡⟨ ap (π* m _ ∘'_) (from-pathp (weak.commutes _)) ⟩
      π* m _ ∘' π*.universal f h'                 ≡⟨ π*.commutes f h' ⟩
      h' ∎
      where open Morphisms m h'
```

Uniqueness is somewhat more delicate. We need to show that the blue cell
in the following diagram commutes.

~~~{.quiver}
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

~~~{.quiver}
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

~~~{.quiver}
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
    cocart .is-cocartesian.unique {u' = u'} {m = m} {h' = h'} m' p =
      m'                     ≡⟨ from-pathp⁻ (symP (π*.commutesp (idr _) m')) ⟩
      hom[] (π* m u' ∘' id*) ≡⟨ hom[]⟩⟨ ap (π* m u' ∘'_) (weak.unique _ (to-pathp $ π*.unique _ path )) ⟩
      hom[] (π* m u' ∘' h**) ∎
      where
        open Morphisms m h'

        id* : Hom[ id ] y' (m ^* u')
        id* = π*.universalv m'

        path : π* m u' ∘' hom[ idl _ ] (id* ∘' f') ≡ h'
        path =
          π* m u' ∘' hom[] (id* ∘' f') ≡⟨ whisker-r _ ⟩
          hom[] (π* m u' ∘' id* ∘' f') ≡⟨ cancel _ (ap (m ∘_) (idl _)) (pulll' (idr _) (π*.commutesv m')) ⟩
          m' ∘' f'                     ≡⟨ p ⟩
          h'                           ∎
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
Weak-cocartesian-fibration : Type _
Weak-cocartesian-fibration = ∀ {x y} → (f : Hom x y) → (x' : Ob[ x ]) → Weak-cocartesian-lift f x'
```

<!--
```agda
module Weak-cocartesian-fibration (wfib : Weak-cocartesian-fibration) where
  module _ {x y} (f : Hom x y) (x' : Ob[ x ]) where
    open Weak-cocartesian-lift (wfib f x')
      using ()
      renaming (y' to _^!_; lifting to ι!)
      public

  module ι! {x y} {f : Hom x y} {x' : Ob[ x ]} where
    open Weak-cocartesian-lift (wfib f x')
      hiding (y'; lifting)
      public


  rebase : ∀ {x y x' x''} → (f : Hom x y)
           → Hom[ id ] x' x''
           → Hom[ id ] (f ^! x') (f ^! x'')
  rebase f vert =
    ι!.universal (hom[ idr _ ] (ι! f _ ∘' vert))
```
-->

Weak cocartesian fibrations are dual to [[weak cartesian fibrations]].

```agda
weak-op-fibration→weak-opfibration
  : Weak-cartesian-fibration (ℰ ^total-op)
  → Weak-cocartesian-fibration

weak-opfibration→weak-op-fibration
  : Weak-cocartesian-fibration
  → Weak-cartesian-fibration (ℰ ^total-op)
```


<details>
<summary>As usual, we omit the duality proofs, as they are quite tedious.
</summary>
```agda
weak-op-fibration→weak-opfibration wlift f x' =
  weak-co-cartesian-lift→weak-cocartesian-lift $
  wlift f x'

weak-opfibration→weak-op-fibration wlift f y' =
  weak-cocartesian-lift→weak-co-cartesian-lift $
  wlift f y'
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
  → Weak-cocartesian-fibration
```

<!--
```agda
cocartesian-lift→weak-cocartesian-lift cocart .Weak-cocartesian-lift.y' =
  Cocartesian-lift.y' cocart
cocartesian-lift→weak-cocartesian-lift cocart .Weak-cocartesian-lift.lifting =
  Cocartesian-lift.lifting cocart
cocartesian-lift→weak-cocartesian-lift cocart .Weak-cocartesian-lift.weak-cocartesian =
  cocartesian→weak-cocartesian (Cocartesian-lift.cocartesian cocart)

opfibration→weak-opfibration opfib f x' =
  cocartesian-lift→weak-cocartesian-lift (opfib f x')
```
-->

A weak opfibration is an opfibration when weak cocartesian morphisms are
closed under composition. This follows via duality.

```agda
weak-opfibration→opfibration
  : Weak-cocartesian-fibration
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
  → Weak-cocartesian-fibration
  → Cocartesian-fibration
cartesian+weak-opfibration→opfibration fib wlifts =
  weak-opfibration→opfibration wlifts λ f-weak g-weak →
    cocartesian→weak-cocartesian $
    cocartesian-∘
      (fibration+weak-cocartesian→cocartesian fib f-weak)
      (fibration+weak-cocartesian→cocartesian fib g-weak)
```

# Weak cocartesian morphisms as left adjoints to base change

If $\cE$ is a [[cocartesian fibration]], we can define [[cobase change]]
functors $f_! : \cE_{X} \to \cE_{Y}$ for every $f : X \to Y$. However, the
requirement that $\cE$ is cocartesian is overly strong[^1]; all we need to define
a base change functor $f_! : \cE_{X} \to \cE_{Y}$ is a family of *weak*
cocartesian lifts of $f$.

[^1]: Note that these functors are only well-behaved if $\cE$ is in fact
cocartesian, so the loss of generality is minimal in the long run.

```agda
weak-cocartesian-lift→cobase-change
  : ∀ {x y}
  → (f : Hom x y)
  → (∀ x' → Weak-cocartesian-lift f x')
  → Functor (Fibre ℰ x) (Fibre ℰ y)
```

The reason that weak cocartesian morphisms suffice is that we only need
to consider vertical structure when performing cobase change, so the weaker
universal property is enough. This is reflected in the action on morphisms,
which is identical to the definition of cobase change for a cocartesian fibration.

```agda
weak-cocartesian-lift→cobase-change {x = x} {y = y} f wcocart = f-cobase-change where
  module wcocart (x' : Ob[ x ]) where
    open Weak-cocartesian-lift (wcocart x')
      renaming (y' to f^!_; lifting to ι!)
      public

  open wcocart

  f-cobase-change : Functor (Fibre ℰ x) (Fibre ℰ y)
  f-cobase-change .Functor.F₀ x' =
    f^! x'
  f-cobase-change .Functor.F₁ f' =
    universal _ (hom[ idr _ ] (ι! _ ∘' f'))
```

<details>
<summary>Functoriality follows from the fact that the universal map is
unique, though this is rather tedious to show.
</summary>
```agda
  f-cobase-change .Functor.F-id =
    sym $ unique _ _ $ cast[] $
      id' ∘' ι! _         ≡[]⟨ idl' _ ⟩
      ι! _                ≡[]⟨ from-pathp⁻ (symP (idr' _)) ⟩
      hom[] (ι! _ ∘' id') ∎
  f-cobase-change .Functor.F-∘ f' g' =
    sym $ unique  _ _ $ cast[] $
      (universal _ (hom[ idr _ ] (ι! _ ∘' f')) Fib.∘ universal _ (hom[ idr _ ] (ι! _ ∘' g'))) ∘' ι! _
        ≡[]⟨ Fib.pullrf (commutes _ _) ∙[] unwrapr (idr _) ⟩
      universal _ (hom[ idr f ] (ι! _ ∘' f')) ∘' (ι! _ ∘' g')
        ≡[]⟨ pulll[] _ (commutes _ _) ∙[] unwrapl (idr _) ⟩
      (ι! _ ∘' f') ∘' g'
        ≡[]⟨ pullr[] _ (wrap (idl _)) ∙[] wrap (idr _) ⟩
      hom[ idr f ] (ι! _ ∘' f' Fib.∘ g')
        ∎
```
</details>

The existence of cobase change functors also provides an alternative universal
property for weak cocartesian lifts when $\cE$ is a [[cartesian fibration]];
namely, a family of cocartesian lifts is equivalent to the existence of a
[[left adjoint]] to a [[base change]] functor.

```agda
module _ (fib : Cartesian-fibration ℰ) where
  open Cat.Displayed.Cartesian.Indexing ℰ fib
  open Cartesian-fibration ℰ fib

  left-adjoint→weak-cocartesian-lift
    : ∀ {x y}
    → (f : Hom x y)
    → (f^! : Functor (Fibre ℰ x) (Fibre ℰ y))
    → f^! ⊣ base-change f
    → ∀ x' → Weak-cocartesian-lift f x'


  weak-cocartesian-lift→left-adjoint
    : ∀ {x y}
    → (f : Hom x y)
    → (f^! : ∀ x' → Weak-cocartesian-lift f x')
    → weak-cocartesian-lift→cobase-change f f^! ⊣ base-change f
```

We shall start by showing a left adjoint $f^! : \cE_{x} \to \cE_{y}$ to base change along $f$
induces cocartesian lifts for every $x'$. The object $f_{!}(X')$ is the only
possible candidate for our lift, and we can construct a map $X' \to f_{!}(X')$
by composing the unit $\eta_{X'} : X' \to f^{*}f_{!}(X')$ with the projection
out of $f^{*}f_{!}(X')$.

~~~{.quiver}
\begin{tikzcd}
  {X'} & {f^*f_!(X')} && {f_!(X)} \\
  \\
  & X && Y
  \arrow["{\eta_{X'}}", from=1-1, to=1-2]
  \arrow[from=1-1, to=3-2]
  \arrow["\pi", from=1-2, to=1-4]
  \arrow[from=1-2, to=3-2]
  \arrow[from=1-4, to=3-4]
  \arrow["f", from=3-2, to=3-4]
\end{tikzcd}
~~~

```agda
  left-adjoint→weak-cocartesian-lift  {y = y} f f^! f^!⊣f^* x' = f-lift where
    module f^! = Functor f^!

    open Weak-cocartesian-lift
    open _⊣_ f^!⊣f^*

    ι! : Hom[ f ] x' (f^!.₀ x')
    ι! = hom[ idr _ ] (π* f (f^!.F₀ x') ∘' η x')

    f-lift : Weak-cocartesian-lift f x'
    f-lift .y' = f^!.₀ x'
    f-lift .lifting = ι!
```

We can prove that our putative lift $\iota = \pi \circ \eta_{X'}$ is weakly
cocartesian via a nice equivalence chase. First, recall that a map is weakly
cocartesian if and only if precomposition with a vertical map is an [[equivalence]].
Moreover, the universal map of a cartesian fibration is also an equivalence,
so by 2-out-of-3 it suffices to show that the function that takes a vertical
map $f' : f_{!}(X') \to Y'$ to the universal factorization indicated in the
following diagram is an equivalence.

~~~{.quiver}
\begin{tikzcd}
  {X'} \\
  & {f^*f_!(X')} && {f_{!}(X')} \\
  X \\
  & X && Y
  \arrow["{\exists!}"', dashed, from=1-1, to=2-2]
  \arrow["{f' \circ \pi \circ \eta_{X'}}", curve={height=-12pt}, from=1-1, to=2-4]
  \arrow[from=1-1, to=3-1]
  \arrow["\pi"', from=2-2, to=2-4]
  \arrow[from=2-2, to=4-2]
  \arrow[from=2-4, to=4-4]
  \arrow["\id"{description}, from=3-1, to=4-2]
  \arrow["f"{description}, from=4-2, to=4-4]
\end{tikzcd}
~~~

However, this is just the [[left adjunct]] of the adjoint up to some
transport gunk, which is an equivalence!

```agda
    f-lift .weak-cocartesian =
      precompose-equiv→weak-cocartesian ι! $ λ {y'} →
      equiv-cancell (fibration→universal-is-equiv ℰ fib f) $
      subst is-equiv (funext (coh y')) (L-adjunct-is-equiv f^!⊣f^*)
      where
        coh
           : ∀ y' (f' : Hom[ id ] (f^!.₀ x') y')
           → hom[ idl _ ] (π*.universal' id-comm (f' ∘' π* f _) ∘' η x')
           ≡ π*.universalv (hom[ idl _ ] (f' ∘' ι!))
        coh y' f' =
          from-pathp $ π*.uniquep _ (idl _) (idr _) _ $
            π* f y' ∘' π*.universal' _ (f' ∘' π* f (f^!.₀ x')) ∘' η x' ≡[]⟨ pulll[] _ (π*.commutesp id-comm _) ⟩
            (f' ∘' π* f (f^!.₀ x')) ∘' η x'                            ≡[]⟨ (pullr[] (idr _) (wrap (idr _)) ∙[] wrap (idl _)) ⟩
            hom[ idl f ] (f' ∘' ι!)                                    ∎
```

The reverse direction follows from some more equivalence yoga. First,
recall that we can present [[adjoints as hom isomorphisms]]; this means that it
suffices to construct an equivalence between $f_{!}(X) \to y$ and
$X \to f^*{Y}$. Moreover, we already have equivalences that characterise
these two types: these are just the universal properties of weak cocartesian and
cartesian maps, resp.

```agda
  weak-cocartesian-lift→left-adjoint {x = x} {y = y} f wcocart = f-cobase-change-adj where
    module wcocart (x' : Ob[ x ]) where
      open Weak-cocartesian-lift (wcocart x')
        renaming (y' to f^!_; lifting to ι!)
        public

    open wcocart
    open _=>_
    open _⊣_

    f-cobase-change-adj : weak-cocartesian-lift→cobase-change f wcocart ⊣ base-change f
    f-cobase-change-adj =
      hom-iso→adjoints
        (λ f' → π*.universalv (hom[ idl _ ] (f' ∘' ι! _)))
        (∙-is-equiv (weak-cocartesian→precompose-equiv (weak-cocartesian _))
          ((fibration→universal-is-equiv ℰ fib f)))
        universalv-natural
```

<details>
<summary>All that remains is the naturality condition, which follows from
some brute-force applications of the universal property of cartesian maps.
</summary>

```agda
      where
        universalv-natural
          : ∀ {x' x'' : Ob[ x ]} {y' y'' : Ob[ y ]}
          → (vy : Hom[ id ] y' y'') (vx : Hom[ id ] x' x'')
          → (f' : Hom[ id ] (f^! x'') y')
          → _
        universalv-natural vy vx f' =
          π*.uniquep₂ _ _ _ _ _
            (π*.commutesv _
              ∙[] unwrap _
              ∙[] Fib.pullrf (Fib.pullrf (commutes _ _)))
            (Fib.pulllf (π*.commutesp id-comm _)
              ∙[] Fib.pulllf (pullr[] _ (π*.commutesv _))
              ∙[] pullr[] _ (unwrapl (idl f) ∙[] symP (assoc' _ _ _) ∙[] wrapr (idr f)))

```
</details>

# Weak opfibrations and equivalence of Hom sets

If $\cE$ is a weak opfibration, then the hom sets $x' \to_f y'$ and
$f^{*}(x') \to_{id} y'$ are equivalent, where $f^{*}(x')$ is the codomain
of the lift of $f$ along $y'$.

```agda
module _ (wopfib : Weak-cocartesian-fibration) where
  open Weak-cocartesian-fibration wopfib

  weak-opfibration→universal-is-equiv
    : ∀ {x y y' x'}
    → (u : Hom x y)
    → is-equiv (ι!.universal {f = u} {x' = x'} {y'})
  weak-opfibration→universal-is-equiv {x' = x'} u =
    is-iso→is-equiv $
    iso (λ u' → hom[ idl u ] (u' ∘' ι! u x'))
        (λ u' → sym $ ι!.unique u' (to-pathp refl))
        (λ u' → cancel _ _ (ι!.commutes u'))

  weak-opfibration→vertical-equiv
    : ∀ {x y x' y'}
    → (u : Hom x y)
    → Hom[ u ] x' y' ≃ Hom[ id ] (u ^! x') y'
  weak-opfibration→vertical-equiv {x' = x'} u =
    ι!.universal , weak-opfibration→universal-is-equiv u
```

Furthermore, this equivalence is natural.

```agda
  weak-opfibration→hom-iso-from
    : ∀ {x y x'} (u : Hom x y)
    → Hom-over-from ℰ u x' ≅ⁿ Hom-from (Fibre ℰ y) (u ^! x')
  weak-opfibration→hom-iso-from {y = y} {x' = x'} u = to-natural-iso mi where
    open make-natural-iso

    mi : make-natural-iso (Hom-over-from ℰ u x') (Hom-from (Fibre ℰ y) (u ^! x'))
    mi .eta x u' = ι!.universal u'
    mi .inv x v' = hom[ idl u ] (v' ∘' ι! u x')
    mi .eta∘inv _ = funext λ v' →
      sym $ ι!.unique _ (to-pathp refl)
    mi .inv∘eta _ = funext λ u' →
      from-pathp $ ι!.commutes _
    mi .natural _ _ v' = funext λ u' →
      ι!.unique _ $ to-pathp $
        smashl _ _
      ∙ weave _ (ap (_∘ u) (idl id)) _ (pullr' _ (ι!.commutes _))
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
    → Weak-cocartesian-fibration
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
    → Weak-cocartesian-fibration
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
  open Cat.Displayed.Cocartesian.Indexing ℰ opfib
  open Cocartesian-fibration opfib

  opfibration→hom-iso-from
    : ∀ {x y x'} (u : Hom x y)
    → Hom-over-from ℰ u x' ≅ⁿ Hom-from (Fibre ℰ y) (u ^! x')
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
    mi .eta x u' = ι!.universalv u'
    mi .inv x v' = hom[ idl u ] (v' ∘' ι! u _)
    mi .eta∘inv x = funext λ v' →
      sym $ ι!.uniquev _ (to-pathp refl)
    mi .inv∘eta x = funext λ u' →
      from-pathp (ι!.commutesv _)
    mi .natural _ _ v' = funext λ u' →
      ι!.unique _ $ to-pathp $
        smashl _ _
        ·· revive₁ (pullr[] _ (ι!.commutesv _))
        ·· smashr _ _
        ·· weave _ (pulll (idl u)) _ (pulll[] _ (ι!.commutesv _))
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
    mi .eta x u' = ι!.universalv u'
    mi .inv x v' = hom[ idl u ] (v' ∘' ι! u _)
    mi .eta∘inv x = funext λ v' →
      sym $ ι!.uniquev _ (to-pathp refl)
    mi .inv∘eta x = funext λ u' →
      from-pathp (ι!.commutesv _)
    mi .natural _ _ (v₁' , v₂') = funext λ u' →
      Fibre.pulll (sym (happly (from-iso.to .is-natural _ _ v₂') u'))
      ·· sym (happly (into-iso.to .is-natural _ _ v₁') (hom[ idl _ ] (v₂' ∘' u')))
      ·· ap (into-iso.to .η _) (smashl _ _ ∙ sym assoc[])

  opfibration→universal-is-equiv
    : ∀ {x y x' y'}
    → (u : Hom x y)
    → is-equiv (ι!.universalv {f = u} {x' = x'} {y'})
  opfibration→universal-is-equiv u =
    weak-opfibration→universal-is-equiv (opfibration→weak-opfibration opfib) u

  opfibration→vertical-equiv
    : ∀ {x y x' y'}
    → (u : Hom x y)
    → Hom[ u ] x' y' ≃ Hom[ id ] (u ^! x') y'
  opfibration→vertical-equiv u =
   weak-opfibration→vertical-equiv (opfibration→weak-opfibration opfib) u
```
-->
