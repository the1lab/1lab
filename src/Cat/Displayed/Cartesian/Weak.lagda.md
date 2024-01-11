<!--
```agda
open import Cat.Functor.Hom.Displayed
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Displayed.Cartesian.Indexing as Indexing
import Cat.Displayed.Fibre.Reasoning as FibR
import Cat.Displayed.Cartesian as Cart
import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism as DM
import Cat.Reasoning as CR
```
-->

```agda
module Cat.Displayed.Cartesian.Weak
  {o ℓ o' ℓ'}
  {ℬ : Precategory o ℓ}
  (ℰ : Displayed ℬ o' ℓ')
  where
```

<!--
```agda
open CR ℬ
open Displayed ℰ
open Cart ℰ
open DR ℰ
open DM ℰ
open Functor
open Functor
private module Fib = FibR ℰ
```
-->

# Weak cartesian morphisms {defines="weak-cartesian-morphism weakly-cartesian-morphism weak-cartesian-map weakly-cartesian-map"}

Some authors use a weaker notion of [[cartesian morphism]] when defining
fibrations, referred to as a "weak cartesian" or "hypocartesian"
morphism. Such morphisms only allow for the construction of universal
maps when the morphism to be factored is displayed over the same morphism
as the weak cartesian map. This situation is best understood graphically.

~~~{.quiver}
\begin{tikzcd}
	{u'} \\
	& {x'} && {y'} \\
	x \\
	& x && y
	\arrow["f"', from=4-2, to=4-4]
	\arrow[lies over, from=2-2, to=4-2]
	\arrow[lies over, from=2-4, to=4-4]
	\arrow["{f'}"', from=2-2, to=2-4]
	\arrow["id"', from=3-1, to=4-2]
	\arrow[dashed, from=1-1, to=2-2]
	\arrow[lies over, from=1-1, to=3-1]
	\arrow["{g'}"', curve={height=-12pt}, from=1-1, to=2-4]
	\arrow["f"', curve={height=-12pt}, from=3-1, to=4-4]
\end{tikzcd}
~~~

```agda
record is-weak-cartesian
  {a b a' b'} (f : Hom a b) (f' : Hom[ f ] a' b')
  : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ')
  where
  no-eta-equality
  field
    universal : ∀ {x'} → (g' : Hom[ f ] x' b') → Hom[ id ] x' a'
    commutes  : ∀ {x'} → (g' : Hom[ f ] x' b') → f' ∘' universal g' ≡[ idr _ ] g'
    unique    : ∀ {x'} {g' : Hom[ f ] x' b'}
                → (h' : Hom[ id ] x' a')
                → f' ∘' h' ≡[ idr _ ] g'
                → h' ≡ universal g'

open is-weak-cartesian
```

Like their stronger counterparts, weak cartesian lifts are unique
up to vertical isomorphism.

```agda
weak-cartesian-domain-unique
  : ∀ {x y} {f : Hom x y}
  → ∀ {x' x'' y'} {f' : Hom[ f ] x' y'} {f'' : Hom[ f ] x'' y'}
  → is-weak-cartesian f f'
  → is-weak-cartesian f f''
  → x' ≅↓ x''
weak-cartesian-domain-unique {f' = f'} {f'' = f''} f'-weak f''-weak =
  make-iso[ _ ] to* from*
    (to-pathp $ unique f''-weak _ invl* ∙ (sym $ unique f''-weak _ (idr' f'')))
    (to-pathp $ unique f'-weak _ invr* ∙ (sym $ unique f'-weak _ (idr' f')))
  where
    open is-weak-cartesian

    to* = universal f''-weak f'
    from* = universal f'-weak f''

    invl* : f'' ∘' hom[] (to* ∘' from*) ≡[ idr _ ] f''
    invl* = to-pathp $
      hom[] (f'' ∘' hom[] (to* ∘' from*)) ≡⟨ smashr _ _ ⟩
      hom[] (f'' ∘' to* ∘' from*)         ≡⟨ revive₁ {p = ap (_ ∘_) (idl _)} (pulll' (idr _) (f''-weak .commutes f')) ⟩
      hom[] (f' ∘' from*)                ≡⟨ revive₁ (f'-weak .commutes f'') ⟩
      hom[] f''                           ≡⟨ liberate _ ⟩
      f'' ∎

    invr* : f' ∘' hom[] (from* ∘' to*) ≡[ idr _ ] f'
    invr* = to-pathp $
      hom[] (f' ∘' hom[] (from* ∘' to*)) ≡⟨ smashr _ _ ⟩
      hom[] (f' ∘' from* ∘' to*)         ≡⟨ revive₁ {p = ap (_ ∘_) (idl _)} (pulll' (idr _) (f'-weak .commutes f'')) ⟩
      hom[] (f'' ∘' to*)                  ≡⟨ revive₁ (f''-weak .commutes f') ⟩
      hom[] f'                           ≡⟨ liberate _ ⟩
      f' ∎
```

As one would expect, cartesian maps are always weakly cartesian.
Proving this does involve a bit of cubical yoga, as the maps we want to
factorize aren't definitionally composites, but we can use the
generalized versions of the functions from `Cartesian`{.Agda} to get
the job done.

```agda
cartesian→weak-cartesian : ∀ {x y x' y'} {f : Hom x y} {f' : Hom[ f ] x' y'}
  → is-cartesian f f'
  → is-weak-cartesian f f'
cartesian→weak-cartesian {f = f} {f' = f'} cart = weak-cart where
  open is-cartesian cart

  weak-cart : is-weak-cartesian f f'
  weak-cart .universal g' = universalv g'
  weak-cart .commutes g' = commutesv g'
  weak-cart .unique h' p = uniquev h' p
```

Furthermore, if $\cE$ is a fibration, weakly cartesian morphisms are
also cartesian. To see this, we note that the lift of $f$ is cartesian,
and thus also a weak cartesian morphism. This implies that there is
an isomorphism between their codomains, which allows us to invoke
`cartesian-vert-retraction-stable`{.Agda} to show that $f'$ must also be
cartesian.

```agda
weak-cartesian→cartesian
  : ∀ {x y x' y'} {f : Hom x y} {f' : Hom[ f ] x' y'}
  → (fib : Cartesian-fibration)
  → is-weak-cartesian f f'
  → is-cartesian f f'
weak-cartesian→cartesian {x = x} {y' = y'} {f = f} {f' = f'} fib f-weak = f-cart where
  open Cartesian-fibration fib
  module f-weak = is-weak-cartesian f-weak

  x* : Ob[ x ]
  x* = has-lift.x' f y'

  f* : Hom[ f ] x* y'
  f* = has-lift.lifting f y'

  f*-cart : is-cartesian f f*
  f*-cart = has-lift.cartesian f y'

  f*-weak : is-weak-cartesian f f*
  f*-weak = cartesian→weak-cartesian f*-cart

  f-cart : is-cartesian f f'
  f-cart =
    cartesian-vertical-retraction-stable f*-cart
      (iso[]→to-has-section[] (weak-cartesian-domain-unique f*-weak f-weak))
      (f-weak.commutes f*)
```

$f' : x' \to_{f} y'$ is a weak cartesian morphism if and only if
postcomposition of $f'$ onto vertical maps is an equivalence.

```agda
postcompose-equiv→weak-cartesian
  : ∀ {x y x' y'} {f : Hom x y}
  → (f' : Hom[ f ] x' y')
  → (∀ {x''} → is-equiv {A = Hom[ id ] x'' x'} (f' ∘'_))
  → is-weak-cartesian f f'
postcompose-equiv→weak-cartesian f' eqv .universal h' =
  equiv→inverse eqv (hom[ idr _ ]⁻ h')
postcompose-equiv→weak-cartesian f' eqv .commutes h' =
  to-pathp⁻ (equiv→counit eqv (hom[ idr _ ]⁻ h'))
postcompose-equiv→weak-cartesian f' eqv .unique m' p =
  (sym $ equiv→unit eqv m') ∙ ap (equiv→inverse eqv) (from-pathp⁻ p)

weak-cartesian→postcompose-equiv
  : ∀ {x y x' x'' y'} {f : Hom x y} {f' : Hom[ f ] x' y'}
  → is-weak-cartesian f f'
  → is-equiv {A = Hom[ id ] x'' x'} (f' ∘'_)
weak-cartesian→postcompose-equiv wcart =
  is-iso→is-equiv $
    iso (λ h' → wcart .universal (hom[ idr _ ] h'))
        (λ h' → from-pathp⁻ (wcart .commutes _) ·· hom[]-∙ _ _ ·· liberate _)
        (λ h' → sym $ wcart .unique _ (to-pathp refl))
```

## Weak cartesian lifts {defines=weak-cartesian-fibration}

We can also define a notion of weak cartesian lifts, much like we can
with their stronger cousins.

```agda
record Weak-cartesian-lift
  {x y} (f : Hom x y) (y' : Ob[ y ]) : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ')
  where
  no-eta-equality
  field
    {x'}    : Ob[ x ]
    lifting : Hom[ f ] x' y'
    weak-cartesian : is-weak-cartesian f lifting

  open is-weak-cartesian weak-cartesian public
```

A [[displayed category]] that has weak cartesian lifts for all morphisms
in the base is called a **weak cartesian fibration**, though we will
often use the term **weak fibration**. Other authors call weak
fibrations **prefibred categories**, though we avoid this name as it
conflicts with the precategory/category distinction.

```agda
record is-weak-cartesian-fibration : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
  no-eta-equality
  field
    weak-lift : ∀ {x y} → (f : Hom x y) → (y' : Ob[ y ]) → Weak-cartesian-lift f y'

  module weak-lift {x y} (f : Hom x y) (y' : Ob[ y ]) =
    Weak-cartesian-lift (weak-lift f y')
```

Note that if $\cE$ is a weak fibration, we can define an operation that
allows us to move vertical morphisms between fibres. This is actually
enough to define [base change functors], though they are not well behaved
unless $\cE$ is a fibration.

[base change functors]: Cat.Displayed.Cartesian.Indexing.html

```agda
  rebase : ∀ {x y y' y''} → (f : Hom x y)
           → Hom[ id ] y' y''
           → Hom[ id ] (weak-lift.x' f y') (weak-lift.x' f y'')
  rebase f vert =
    weak-lift.universal f _ (hom[ idl _ ] (vert ∘' weak-lift.lifting f _))
```

Every fibration is a weak fibration.

```agda
cartesian-lift→weak-cartesian-lift
  : ∀ {x y} {f : Hom x y} {y' : Ob[ y ]}
  → Cartesian-lift f y'
  → Weak-cartesian-lift f y'

fibration→weak-fibration
  : Cartesian-fibration
  → is-weak-cartesian-fibration
```

<details>
<summary>The proofs of these facts are just shuffling around data, so we
omit them.
</summary>
```agda
cartesian-lift→weak-cartesian-lift cart .Weak-cartesian-lift.x' =
  Cartesian-lift.x' cart
cartesian-lift→weak-cartesian-lift cart .Weak-cartesian-lift.lifting =
  Cartesian-lift.lifting cart
cartesian-lift→weak-cartesian-lift cart .Weak-cartesian-lift.weak-cartesian =
  cartesian→weak-cartesian (Cartesian-lift.cartesian cart)

fibration→weak-fibration fib .is-weak-cartesian-fibration.weak-lift x y' =
  cartesian-lift→weak-cartesian-lift (Cartesian-fibration.has-lift fib x y')
```
</details>


Notably, weak fibrations are fibrations when weak cartesian morphisms
are closed under composition.

```agda
module _ where
  open Cartesian-fibration
  open is-cartesian

  weak-fibration→fibration
    : is-weak-cartesian-fibration
    → (∀ {x y z x' y' z'} {f : Hom y z} {g : Hom x y}
       → {f' : Hom[ f ] y' z'} {g' : Hom[ g ] x' y'}
       → is-weak-cartesian f f' → is-weak-cartesian g g'
       → is-weak-cartesian (f ∘ g) (f' ∘' g'))
    → Cartesian-fibration
  weak-fibration→fibration weak-fib weak-∘ .has-lift {x = x} f y' = f-lift where
    open is-weak-cartesian-fibration weak-fib

    module weak-∘ {x y z} (f : Hom y z) (g : Hom x y) (z' : Ob[ z ]) =
      is-weak-cartesian (weak-∘ (weak-lift.weak-cartesian f z')
                                (weak-lift.weak-cartesian g _))
```

To show that $f$ has a cartesian lift, we begin by taking the weak
cartesian lift $f^{*}$ of $f$.

~~~{.quiver}
\begin{tikzcd}
	\textcolor{rgb,255:red,214;green,92;blue,92}{x^{*}} && {y'} \\
	\\
	x && y
	\arrow["f", from=3-1, to=3-3]
	\arrow[lies over, color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=3-1]
	\arrow[lies over, from=1-3, to=3-3]
	\arrow["{f^{*}}", color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=1-3]
\end{tikzcd}
~~~

```agda
    x* : Ob[ x ]
    x* = weak-lift.x' f y'

    f* : Hom[ f ] x* y'
    f* = weak-lift.lifting f y'

    f*-weak-cartesian : is-weak-cartesian f f*
    f*-weak-cartesian = weak-lift.weak-cartesian f y'

    module f* = is-weak-cartesian (f*-weak-cartesian)
```

We must now show that the weak cartesian morphism $f^{*}$ is actually
cartesian. To do this, we must construct the following unique universal
map:

~~~{.quiver}
\begin{tikzcd}
	{u'} \\
	&& {x^{*}} && {y'} \\
	u \\
	&& x && y
	\arrow["f", from=4-3, to=4-5]
	\arrow[lies over, from=2-3, to=4-3]
	\arrow[lies over, from=2-5, to=4-5]
	\arrow["{f^{*}}", from=2-3, to=2-5]
	\arrow[color={rgb,255:red,214;green,92;blue,92}, dashed, from=1-1, to=2-3]
	\arrow["m", from=3-1, to=4-3]
	\arrow["{h'}", curve={height=-18pt}, from=1-1, to=2-5]
	\arrow[lies over, from=1-1, to=3-1]
\end{tikzcd}
~~~

To do this, we shall first take the weak cartesian lift $m^{*}$ of
$m$. Both $f^{*}$ and $m^{*}$ are weak cartesian, which means that
their composite is also weak cartesian by our hypothesis. We can
then factor $h'$ through $f^{*} \cdot m^{*}$ to obtain a vertical
morphism $u' \to u^{*}$, which we can then compose with $m^{*}$
to obtain the requisite map.

```agda
    module Morphisms
      {u : Ob} {u' : Ob[ u ]} (m : Hom u x) (h' : Hom[ f ∘ m ] u' y')
      where
        u* : Ob[ u ]
        u* = weak-lift.x' m _

        m* : Hom[ m ] u* x*
        m* = weak-lift.lifting m _

        m*-weak-cartesian : is-weak-cartesian m m*
        m*-weak-cartesian = weak-lift.weak-cartesian m x*

        module m* = is-weak-cartesian m*-weak-cartesian
        module f*∘m* = is-weak-cartesian (weak-∘ f*-weak-cartesian m*-weak-cartesian)
```


```agda
    f*-cartesian : is-cartesian f f*
    f*-cartesian .universal {u = u} {u' = u'} m h' =
      hom[ idr m ] (m* ∘'  f*∘m*.universal h')
      where open Morphisms m h'
```

<details>
<summary> Showing that this commutes is mostly an exercise in cubical
yoga; the only real mathematical content is that the factorisation of
$h'$ via $f^{*} \cdot m^{*}$ commutes.
</summary>
```agda
    f*-cartesian .commutes {u = u} {u' = u'} m h' = path
      where
        open Morphisms m h'

        abstract
          path : f* ∘' hom[ idr m ] (m* ∘' f*∘m*.universal h') ≡ h'
          path =
            f* ∘' hom[] (m* ∘' f*∘m*.universal h')   ≡⟨ whisker-r _ ⟩
            hom[] (f* ∘' m* ∘' f*∘m*.universal h')   ≡⟨ assoc[] {q = idr _} ⟩
            hom[] ((f* ∘' m*) ∘' f*∘m*.universal h') ≡⟨ hom[]⟩⟨ from-pathp⁻ (f*∘m*.commutes h') ⟩
            hom[] (hom[] h')                         ≡⟨ hom[]-∙ _ _ ∙ liberate _ ⟩
            h'                                       ∎
```
</details>

<details>
<summary>Uniqueness follows similarly as some cubical yoga, followed by
the fact that both $m^{*}$ and $f^{*} \cdot m^{*}$ are weak cartesian
maps.
</summary>
```agda
    f*-cartesian .unique {u = u} {u' = u'} {m = m} {h' = h'} m' p = path
      where
        open Morphisms m h'

        abstract
          universal-path : (f* ∘' m*) ∘' m*.universal m' ≡[ idr (f ∘ m) ] h'
          universal-path = to-pathp $
            hom[] ((f* ∘' m*) ∘' m*.universal m') ≡˘⟨ assoc[] {p = ap (f ∘_) (idr m)} ⟩
            hom[] (f* ∘' (m* ∘' m*.universal m')) ≡⟨ hom[]⟩⟨ ap (f* ∘'_) (from-pathp⁻ (m*.commutes m')) ⟩
            hom[] (f* ∘' hom[] m')                ≡⟨ smashr _ _ ∙ liberate _ ⟩
            f* ∘' m'                              ≡⟨ p ⟩
            h' ∎

          path : m' ≡ hom[ idr m ] (m* ∘' f*∘m*.universal h')
          path =
            m'                               ≡˘⟨ from-pathp (m*.commutes m') ⟩
            hom[] (m* ∘' m*.universal m')    ≡⟨ reindex _ (idr m) ⟩
            hom[] (m* ∘' m*.universal m')    ≡⟨ hom[]⟩⟨ ap (m* ∘'_) (f*∘m*.unique _ universal-path) ⟩
            hom[] (m* ∘' f*∘m*.universal h') ∎
```
</details>

Putting this all together, we can finally deduce that $f^{*}$ is
a cartesian lift of $f$.

```agda
    f-lift : Cartesian-lift f y'
    f-lift .Cartesian-lift.x' = x*
    f-lift .Cartesian-lift.lifting = f*
    f-lift .Cartesian-lift.cartesian = f*-cartesian
```

## Factorisations in weak fibrations

If $\cE$ is a weak fibration, then every morphism factorizes into
a vertical morphism followed by a weak cartesian morphism.

```agda
record weak-cartesian-factorisation
  {x y x' y'} {f : Hom x y}
  (f' : Hom[ f ] x' y')
  : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ')
  where
  no-eta-equality
  field
    {x''} : Ob[ x ]
    vertical : Hom[ id ] x' x''
    weak-cart : Hom[ f ] x'' y'
    has-weak-cartesian : is-weak-cartesian f weak-cart
    factors : f' ≡[ sym (idr _) ] weak-cart ∘' vertical

weak-fibration→weak-cartesian-factors
  : ∀ {x y x' y'} {f : Hom x y}
  → is-weak-cartesian-fibration
  → (f' : Hom[ f ] x' y')
  → weak-cartesian-factorisation f'
```

Because $\cE$ is a weak fibration, every morphism in $\cB$ has a weak
cartesian lift. This allows us to take the lift of $f$, which will
form the weak cartesian component of the factorisation. The vertical
component can be obtained by taking the universal factorisation of
$f'$ by the lift of $f$.

```agda
weak-fibration→weak-cartesian-factors {y' = y'} {f = f} wfib f' = weak-factor where
  open is-weak-cartesian-fibration wfib
  module f-lift = weak-lift f y'
  open weak-cartesian-factorisation

  weak-factor : weak-cartesian-factorisation f'
  weak-factor .x'' = f-lift.x'
  weak-factor .vertical = f-lift.universal f'
  weak-factor .weak-cart = f-lift.lifting
  weak-factor .has-weak-cartesian = f-lift.weak-cartesian
  weak-factor .factors = symP $ f-lift.commutes f'
```

## Weak fibrations and equivalence of Hom sets

If $\cE$ is a weak fibration, then the hom sets $x' \to_f y'$ and
$x' \to_{id} f^{*}(y')$ are equivalent, where $f^{*}(y')$ is the domain
of the lift of $f$ along $y'$. To go from $f' : x' \to_u y'$ to
$x' \to_{id} f^{*}(y')$, we use the vertical component of the
factorisation of $f'$; this forms an equivalence, as this factorisation
is unique.

```agda
module _ (wfib : is-weak-cartesian-fibration) where
  open is-weak-cartesian-fibration wfib

  weak-fibration→universal-is-equiv
    : ∀ {x y x' y'}
    → (f : Hom x y)
    → is-equiv (weak-lift.universal f y' {x'})
  weak-fibration→universal-is-equiv {y' = y'} f = is-iso→is-equiv $
    iso (λ f' → hom[ idr f ] (weak-lift.lifting f y' ∘' f') )
        (λ f' → sym $ weak-lift.unique f y' f' (to-pathp refl))
        (λ f' → cancel _ _ (weak-lift.commutes f y' f'))

  weak-fibration→vertical-equiv
    : ∀ {x y x' y'}
    → (f : Hom x y)
    → Hom[ f ] x' y' ≃ Hom[ id ] x' (weak-lift.x' f y')
  weak-fibration→vertical-equiv {y' = y'} f =
    weak-lift.universal f y' ,
    weak-fibration→universal-is-equiv f
```

Furthermore, this equivalence can be extended into a natural isomorphism
between $\cE_{u}(-,y')$ and $\cE_{x}(-,u^{*}(y'))$.

```agda
  weak-fibration→hom-iso-into
    : ∀ {x y y'} (u : Hom x y)
    → Hom-over-into ℰ u y' ≅ⁿ Hom-into (Fibre ℰ x) (weak-lift.x' u y')
  weak-fibration→hom-iso-into {x} {y} {y'} u = to-natural-iso mi where
    open make-natural-iso

    u*y' : Ob[ x ]
    u*y' = weak-lift.x' u y'

    mi : make-natural-iso (Hom-over-into ℰ u y') (Hom-into (Fibre ℰ x) u*y')
    mi .eta x u' = weak-lift.universal u y' u'
    mi .inv x v' = hom[ idr u ] (weak-lift.lifting u y' ∘' v')
    mi .eta∘inv x = funext λ v' →
      sym $ weak-lift.unique u _ _ (to-pathp refl)
    mi .inv∘eta x = funext λ u' →
      from-pathp (weak-lift.commutes u _ _)
    mi .natural x y v' = funext λ u' →
      weak-lift.unique u _ _ $ to-pathp $
        smashr _ _
        ∙ weave _ (ap (u ∘_) (idl id)) _ (pulll' _ (weak-lift.commutes _ _ _))
```

An *extremely* useful fact is that the converse is true: if there is some
lifting of objects $\cE_{y} \to \cE_{x}$ for every morphism $f : x \to y$
in $\cB$, along with a natural equivalence of homs as above, then
$\cE$ is a weak fibration.

This result is the primary reason to care about weak fibrations, as we
already have a toolkit for constructing natural equivalences of hom
sets! Most notably, this allows us to use the theory of [[adjuncts]] to
construct weak fibrations.

```agda
module _ (_*₀_ : ∀ {x y} → Hom x y → Ob[ y ] → Ob[ x ]) where
  open is-weak-cartesian-fibration
  open Weak-cartesian-lift
  open is-weak-cartesian

  private
    vertical-equiv-iso-natural
      : (∀ {x y x' y'} {f : Hom x y} → Hom[ f ] x' y' → Hom[ id ] x' (f *₀ y'))
      → Type _
    vertical-equiv-iso-natural to =
      ∀ {x y x' x'' y'} {f : Hom x y}
      → (f' : Hom[ f ] x'' y') (g' : Hom[ id ] x' x'')
      → to (hom[ idr _ ] (f' ∘' g')) ≡[ sym (idl id) ] to f' ∘' g'

  vertical-equiv→weak-fibration
    : (to* : ∀ {x y x' y'} {f : Hom x y} → Hom[ f ] x' y' → Hom[ id ] x' (f *₀ y'))
    → (∀ {x y x' y'} {f : Hom x y} → is-equiv (to* {x} {y} {x'} {y'} {f}))
    → vertical-equiv-iso-natural to*
    → is-weak-cartesian-fibration
  vertical-equiv→weak-fibration to* to-eqv natural .weak-lift f y' = f-lift where
```

To start, we note that the inverse portion of the equivalence is also
natural.

```agda
    from* : ∀ {x y x' y'} {f : Hom x y} → Hom[ id ] x' (f *₀ y') → Hom[ f ] x' y'
    from* = equiv→inverse to-eqv

    from*-natural
      : ∀ {x y} {f : Hom x y} {x' x'' : Ob[ x ]} {y' : Ob[ y ]}
      → (f' : Hom[ id ] x'' (f *₀ y')) (g' : Hom[ id ] x' x'')
      → from* (hom[ idl id ] (f' ∘' g')) ≡[ sym (idr f) ] from* f' ∘' g'
    from*-natural {f = f} f' g' =
      to-pathp⁻ $ ap fst $ is-contr→is-prop (to-eqv .is-eqv (hom[ idl id ] (f' ∘' g')))
        (from* (hom[ idl id ] (f' ∘' g')) , equiv→counit to-eqv _)
        (hom[ idr f ] (from* f' ∘' g') , from-pathp⁻ (natural (from* f') g') ∙
                                        (hom[]⟩⟨ ap (_∘' g') (equiv→counit to-eqv _)))
```

We then proceed to construct a weak lift of $f$. We can use our object
lifting function to construct the domain of the lift, apply the inverse
direction of the equivalence to $id' : f^{*}(y') \to f^{*}(y')$ to
obtain the required lifting $x' \to_{f} f^{*}(y')$.

```agda
    f-lift : Weak-cartesian-lift f y'
    f-lift .x' = f *₀ y'
    f-lift .lifting = from* id'
```

Now, we must show that the constructed lifting is weakly cartesian. We
can use the forward direction of the equivalence to construct the
universal map; the remaining properties follow from the fact that
the equivalence is natural.

```agda
    f-lift .weak-cartesian .universal g' = to* g'
    f-lift .weak-cartesian .commutes g' = to-pathp $
      hom[] (from* id' ∘' to* g')   ≡˘⟨ from-pathp⁻ (from*-natural id' (to* g')) ⟩
      from* (hom[] (id' ∘' to* g')) ≡⟨ ap from* idl[] ⟩
      from* (to* g')                ≡⟨ equiv→unit to-eqv g' ⟩
      g'                            ∎
    f-lift .weak-cartesian .unique {g' = g'} h' p =
      h'                            ≡˘⟨ idl[] {p = idl id} ⟩
      hom[] (id' ∘' h')             ≡˘⟨ hom[]⟩⟨ ap (_∘' h') (equiv→counit to-eqv id') ⟩
      hom[] (to* (from* id') ∘' h') ≡˘⟨ from-pathp⁻ (natural (from* id') h') ⟩
      to* (hom[] (from* id' ∘' h')) ≡⟨ ap to* (from-pathp p) ⟩
      to* g'                        ∎
```

<!--
```agda
module _ (U : ∀ {x y} → Hom x y → Functor (Fibre ℰ y) (Fibre ℰ x)) where
  open Functor
  open _=>_

  hom-iso→weak-fibration
    : (∀ {x y y'} (u : Hom x y)
       → Hom-over-into ℰ u y' ≅ⁿ Hom-into (Fibre ℰ x) (U u .F₀ y'))
    → is-weak-cartesian-fibration
  hom-iso→weak-fibration hom-iso =
    vertical-equiv→weak-fibration
      (λ u → U u .F₀)
      (λ u' → Isoⁿ.to (hom-iso _) .η _ u')
      (natural-iso-to-is-equiv (hom-iso _) _)
      λ f' g' → to-pathp⁻ $
        happly (Isoⁿ.to (hom-iso _) .is-natural _ _ g') f'
```
-->


Note that this result does *not* extend to fibrations; the equivalence
of homs can only get us weak cartesian lifts. To make the final step
to a fibration, we need to use other means.

However, we do obtain a natural isomorphism between $\cE_{u}(x',-)$ and
$cE_{y}(x',u^{*}(-))$.

```agda
module _ (fib : Cartesian-fibration) where
  open Cartesian-fibration fib
  open Indexing ℰ fib

  fibration→hom-iso-from
    : ∀ {x y x'} (u : Hom x y)
    → Hom-over-from ℰ u x' ≅ⁿ Hom-from (Fibre ℰ x) x' F∘ base-change u
  fibration→hom-iso-from {x} {y} {x'} u = to-natural-iso mi where
    open make-natural-iso

    mi : make-natural-iso
          (Hom-over-from ℰ u x')
          (Hom-from (Fibre ℰ x) x' F∘ base-change u)
    mi .eta x u' = has-lift.universalv u x u'
    mi .inv x v' = hom[ idr u ] (has-lift.lifting u x ∘' v')
    mi .eta∘inv x = funext λ v' →
      sym $ has-lift.uniquev u _ _ (to-pathp refl)
    mi .inv∘eta x = funext λ u' →
      from-pathp (has-lift.commutesv u _ _)
    mi .natural _ _ v' = funext λ u' →
      has-lift.uniquep u _ _ _ _ _ $
        Fib.pulllf (has-lift.commutesp u _ id-comm _)
        ∙[] pullr[] _ (has-lift.commutesv u _ _)
        ∙[] to-pathp refl
```

<!--
```agda
  fibration→universal-is-equiv
    : ∀ {x y x' y'}
    → (f : Hom x y)
    → is-equiv (has-lift.universalv f y' {x'})
  fibration→universal-is-equiv f =
    weak-fibration→universal-is-equiv (fibration→weak-fibration fib) f

  fibration→vertical-equiv
    : ∀ {x y x' y'}
    → (f : Hom x y)
    → Hom[ f ] x' y' ≃ Hom[ id ] x' (has-lift.x' f y')
  fibration→vertical-equiv f =
    weak-fibration→vertical-equiv (fibration→weak-fibration fib) f

  fibration→hom-iso-into
    : ∀ {x y y'} (u : Hom x y)
    → Hom-over-into ℰ u y' ≅ⁿ Hom-into (Fibre ℰ x) (has-lift.x' u y')
  fibration→hom-iso-into u =
    weak-fibration→hom-iso-into (fibration→weak-fibration fib) u
```
-->

If we combine this with `weak-fibration→hom-iso-into`{.Agda}, we obtain
a natural iso between $\cE_{u}(-,-)$ and $\cE_{id}(-,u^{*}(-))$.

```agda
  fibration→hom-iso
    : ∀ {x y} (u : Hom x y)
    → Hom-over ℰ u ≅ⁿ Hom[-,-] (Fibre ℰ x) F∘ (Id F× base-change u)
  fibration→hom-iso {x = x} u = to-natural-iso mi where
    open make-natural-iso
    open _=>_

    module into-iso {y'} = Isoⁿ (fibration→hom-iso-into {y' = y'} u)
    module from-iso {x'} = Isoⁿ (fibration→hom-iso-from {x' = x'} u)

    mi : make-natural-iso (Hom-over ℰ u) (Hom[-,-] (Fibre ℰ x) F∘ (Id F× base-change u))
    mi .eta x u' = has-lift.universalv u _ u'
    mi .inv x v' = hom[ idr u ] (has-lift.lifting u _ ∘' v')
    mi .eta∘inv x = funext λ v' →
      sym $ has-lift.uniquev u _ _ (to-pathp refl)
    mi .inv∘eta x = funext λ u' →
      from-pathp (has-lift.commutesv u _ _)
    mi .natural _ _ (v₁' , v₂') = funext λ u' →
      sym (apr' (happly (into-iso.to .is-natural _ _ v₁') u'))
      ·· sym (happly (from-iso.to .is-natural _ _ v₂') (hom[ idr _ ] (u' ∘' v₁')))
      ·· ap (into-iso.to .η _) (smashr _ _ ∙ reindex _ _ )
```
