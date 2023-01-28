```agda
open import Cat.Displayed.Base
open import Cat.Displayed.Fibre
open import Cat.Prelude

import Cat.Displayed.Cartesian as Cart
import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism as DM

module Cat.Displayed.Cartesian.Weak
  {o ℓ o′ ℓ′}
  {ℬ : Precategory o ℓ}
  (ℰ : Displayed ℬ o′ ℓ′)
  where

open Precategory ℬ
open Displayed ℰ
open Cart ℰ
open DR ℰ
open DM ℰ
open Functor
```

# Weak Cartesian Morphisms

Some authors use a weaker notion of [cartesian morphism] when defining
fibrations, referred to as a "weak cartesian" or "hypocartesian"
morphism. Such morphisms only allow for the construction of universal
maps when the morphism to be factored is displayed over the same morphism
as the weak cartesian map. This situation is best understood graphically.

[cartesian morphism]: Cat.Displayed.Cartesian.html

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
  {a b a′ b′} (f : Hom a b) (f′ : Hom[ f ] a′ b′)
  : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′)
  where
  no-eta-equality
  field
    universal : ∀ {x′} → (g′ : Hom[ f ] x′ b′) → Hom[ id ] x′ a′
    commutes  : ∀ {x′} → (g′ : Hom[ f ] x′ b′) → f′ ∘′ universal g′ ≡[ idr _ ] g′
    unique    : ∀ {x′} {g′ : Hom[ f ] x′ b′}
                → (h′ : Hom[ id ] x′ a′)
                → f′ ∘′ h′ ≡[ idr _ ] g′
                → h′ ≡ universal g′
```

Like their stronger counterparts, weak cartesian lifts are unique
up to vertical isomorphism.

```agda
weak-cartesian-domain-unique
  : ∀ {x y} {f : Hom x y}
  → ∀ {x′ x″ y′} {f′ : Hom[ f ] x′ y′} {f″ : Hom[ f ] x″ y′}
  → is-weak-cartesian f f′
  → is-weak-cartesian f f″
  → x′ ≅↓ x″
weak-cartesian-domain-unique {f′ = f′} {f″ = f″} f′-weak f″-weak =
  make-iso[ _ ] to* from*
    (to-pathp $ unique f″-weak _ invl* ∙ (sym $ unique f″-weak _ (idr′ f″)))
    (to-pathp $ unique f′-weak _ invr* ∙ (sym $ unique f′-weak _ (idr′ f′)))
  where
    open is-weak-cartesian

    to* = universal f″-weak f′
    from* = universal f′-weak f″

    invl* : f″ ∘′ hom[] (to* ∘′ from*) ≡[ idr _ ] f″
    invl* = to-pathp $
      hom[] (f″ ∘′ hom[] (to* ∘′ from*)) ≡⟨ smashr _ _ ⟩
      hom[] (f″ ∘′ to* ∘′ from*)         ≡⟨ revive₁ {p = ap (_ ∘_) (idl _)} (pulll′ (idr _) (f″-weak .commutes f′)) ⟩
      hom[] (f′ ∘′ from*)                ≡⟨ revive₁ (f′-weak .commutes f″) ⟩
      hom[] f″                           ≡⟨ liberate _ ⟩
      f″ ∎

    invr* : f′ ∘′ hom[] (from* ∘′ to*) ≡[ idr _ ] f′
    invr* = to-pathp $
      hom[] (f′ ∘′ hom[] (from* ∘′ to*)) ≡⟨ smashr _ _ ⟩
      hom[] (f′ ∘′ from* ∘′ to*)         ≡⟨ revive₁ {p = ap (_ ∘_) (idl _)} (pulll′ (idr _) (f′-weak .commutes f″)) ⟩
      hom[] (f″ ∘′ to*)                  ≡⟨ revive₁ (f″-weak .commutes f′) ⟩
      hom[] f′                           ≡⟨ liberate _ ⟩
      f′ ∎
```

As one would expect, cartesian maps are always weakly cartesian.
Proving this does involve a bit of cubical yoga, as the maps we want to
factorize aren't definitionally composites, but we can use the
generalized versions of the functions from `Cartesian`{.Agda} to get
the job done.

```agda
cartesian→weak-cartesian : ∀ {x y x′ y′} {f : Hom x y} {f′ : Hom[ f ] x′ y′}
  → is-cartesian f f′
  → is-weak-cartesian f f′
cartesian→weak-cartesian {f = f} {f′ = f′} cart = weak-cart where
  open is-cartesian cart

  weak-cart : is-weak-cartesian f f′
  weak-cart .is-weak-cartesian.universal g′ =
    universal′ (idr f) g′
  weak-cart .is-weak-cartesian.commutes g′ =
    commutesp (idr f) g′
  weak-cart .is-weak-cartesian.unique h′ p =
    uniquep (idr f) refl (idr f) h′ p
```

Furthermore, if $\ca{E}$ is a fibration, weakly cartesian morphisms are
also cartesian. To see this, we note that the lift of $f$ is cartesian,
and thus also a weak cartesian morphism. This implies that there is
an isomorphism between their codomains, which allows us to invoke
`cartesian-vert-retraction-stable`{.Agda} to show that $f'$ must also be
cartesian.

```agda
weak-cartesian→cartesian
  : ∀ {x y x′ y′} {f : Hom x y} {f′ : Hom[ f ] x′ y′}
  → (fib : Cartesian-fibration)
  → is-weak-cartesian f f′
  → is-cartesian f f′
weak-cartesian→cartesian {x = x} {y′ = y′} {f = f} {f′ = f′} fib f-weak = f-cart where
  open Cartesian-fibration fib
  module f-weak = is-weak-cartesian f-weak

  x* : Ob[ x ]
  x* = Cartesian-lift.x′ (has-lift f y′)

  f* : Hom[ f ] x* y′
  f* = Cartesian-lift.lifting (has-lift f y′)

  f*-cart : is-cartesian f f*
  f*-cart = Cartesian-lift.cartesian (has-lift f y′)

  f*-weak : is-weak-cartesian f f*
  f*-weak = cartesian→weak-cartesian f*-cart

  f-cart : is-cartesian f f′
  f-cart =
    cartesian-vertical-retraction-stable f*-cart
      (iso[]→to-has-section[] (weak-cartesian-domain-unique f*-weak f-weak))
      (f-weak.commutes f*)
```

## Weak Cartesian Lifts

We can also define a notion of weak cartesian lifts, much like we can
with their stronger cousins.

```
record Weak-cartesian-lift
  {x y} (f : Hom x y) (y′ : Ob[ y ]) : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′)
  where
  no-eta-equality
  field
    {x′}    : Ob[ x ]
    lifting : Hom[ f ] x′ y′
    weak-cartesian : is-weak-cartesian f lifting

  open is-weak-cartesian weak-cartesian public
```

A displayed category that has weak cartesian lifts for all morphisms
in the base is called a **prefibered category**. Notably, prefibered
categories are fibred when weak cartesian morphisms are closed under
composition.

```agda
weak-cartesian-lifts→fibration
  : (lifts : ∀ {x y} → (f : Hom x y) → (y′ : Ob[ y ]) → Weak-cartesian-lift f y′)
  → (∀ {x y z x′ y′ z′} {f : Hom y z} {g : Hom x y}
     → {f′ : Hom[ f ] y′ z′} {g′ : Hom[ g ] x′ y′}
     → is-weak-cartesian f f′ → is-weak-cartesian g g′
     → is-weak-cartesian (f ∘ g) (f′ ∘′ g′))
  → Cartesian-fibration
weak-cartesian-lifts→fibration weak-lift weak-∘ .Cartesian-fibration.has-lift {x = x} f y′ = f-lift where

  module weak-lift {x y} (f : Hom x y) (y′ : Ob[ y ]) =
    Weak-cartesian-lift (weak-lift f y′)
  module weak-∘ {x y z} (f : Hom y z) (g : Hom x y) (z′ : Ob[ z ]) =
    is-weak-cartesian (weak-∘ (weak-lift.weak-cartesian f z′) (weak-lift.weak-cartesian g _))
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
  x* = weak-lift.x′ f y′

  f* : Hom[ f ] x* y′
  f* = weak-lift.lifting f y′

  f*-weak-cartesian : is-weak-cartesian f f*
  f*-weak-cartesian = weak-lift.weak-cartesian f y′

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
    {u : Ob} {u′ : Ob[ u ]} (m : Hom u x) (h′ : Hom[ f ∘ m ] u′ y′)
    where
      u* : Ob[ u ]
      u* = weak-lift.x′ m _

      m* : Hom[ m ] u* x*
      m* = weak-lift.lifting m _

      m*-weak-cartesian : is-weak-cartesian m m*
      m*-weak-cartesian = weak-lift.weak-cartesian m x*

      module m* = is-weak-cartesian m*-weak-cartesian
      module f*∘m* = is-weak-cartesian (weak-∘ f*-weak-cartesian m*-weak-cartesian)
```


```agda
  f*-cartesian : is-cartesian f f*
  f*-cartesian .is-cartesian.universal {u = u} {u′ = u′} m h′ =
    hom[ idr m ] (m* ∘′  f*∘m*.universal h′)
    where open Morphisms m h′
```

<details>
<summary> Showing that this commutes is mostly an exercise in cubical
yoga; the only real mathematical content is that the factorization of
$h'$ via $f^{*} \cdot m^{*}$ commutes.
</summary>
```agda
  f*-cartesian .is-cartesian.commutes {u = u} {u′ = u′} m h′ = path
    where
      open Morphisms m h′

      abstract
        path : f* ∘′ hom[ idr m ] (m* ∘′ f*∘m*.universal h′) ≡ h′
        path =
          f* ∘′ hom[] (m* ∘′ f*∘m*.universal h′)   ≡⟨ whisker-r _ ⟩
          hom[] (f* ∘′ m* ∘′ f*∘m*.universal h′)   ≡⟨ assoc[] {q = idr _} ⟩
          hom[] ((f* ∘′ m*) ∘′ f*∘m*.universal h′) ≡⟨ hom[]⟩⟨ from-pathp⁻ (f*∘m*.commutes h′) ⟩
          hom[] (hom[] h′)                         ≡⟨ hom[]-∙ _ _ ∙ liberate _ ⟩
          h′                                       ∎
```
</details>

<details>
<summary>Uniqueness follows similarly as some cubical yoga, followed by
the fact that both $m^{*}$ and $f^{*} \cdot m^{*}$ are weak cartesian
maps.
</summary>
```agda
  f*-cartesian .is-cartesian.unique {u = u} {u′ = u′} {m = m} {h′ = h′} m′ p = path
    where
      open Morphisms m h′

      abstract
        universal-path : (f* ∘′ m*) ∘′ m*.universal m′ ≡[ idr (f ∘ m) ] h′
        universal-path = to-pathp $
          hom[] ((f* ∘′ m*) ∘′ m*.universal m′) ≡˘⟨ assoc[] {p = ap (f ∘_) (idr m)} ⟩
          hom[] (f* ∘′ (m* ∘′ m*.universal m′)) ≡⟨ hom[]⟩⟨ ap (f* ∘′_) (from-pathp⁻ (m*.commutes m′)) ⟩
          hom[] (f* ∘′ hom[] m′)                ≡⟨ smashr _ _ ∙ liberate _ ⟩
          f* ∘′ m′                              ≡⟨ p ⟩
          h′ ∎

        path : m′ ≡ hom[ idr m ] (m* ∘′ f*∘m*.universal h′)
        path =
          m′                               ≡˘⟨ from-pathp (m*.commutes m′) ⟩
          hom[] (m* ∘′ m*.universal m′)    ≡⟨ reindex _ (idr m) ⟩
          hom[] (m* ∘′ m*.universal m′)    ≡⟨ hom[]⟩⟨ ap (m* ∘′_) (f*∘m*.unique _ universal-path) ⟩
          hom[] (m* ∘′ f*∘m*.universal h′) ∎
```
</details>

Putting this all together, we can finally deduce that $f^{*}$ is
a cartesian lift of $f$.

```agda
  f-lift : Cartesian-lift f y′
  f-lift .Cartesian-lift.x′ = x*
  f-lift .Cartesian-lift.lifting = f*
  f-lift .Cartesian-lift.cartesian = f*-cartesian
```

<!--
[TODO: Reed M, 25/01/2023] Explain this code when showing that left
adjoints to reindexing gives opfibrations.
```agda
weak-cartesian-lift→reindex
  : ∀ {x y} {f : Hom x y} {x′ : Ob[ x ]} {y′ : Ob[ y ]}
  → (weak-lift : Weak-cartesian-lift f y′)
  → Hom[ f ] x′ y′ ≃ Hom[ id ] x′ (Weak-cartesian-lift.x′ weak-lift)
weak-cartesian-lift→reindex weak-lift = Iso→Equiv $
  universal ,
  iso (λ f′ → hom[ idr _ ] (lifting ∘′ f′))
      (λ f′ → sym $ unique f′ (to-pathp refl))
      (λ f′ → (hom[]⟩⟨ from-pathp⁻ (commutes f′)) ·· hom[]-∙ _ _ ·· liberate _)
  where
    open Weak-cartesian-lift weak-lift

module _ (U : ∀ {x y} → Hom x y → Functor (Fibre ℰ y) (Fibre ℰ x))
         where

  reindex-iso-natural
    : (∀ {x y x′ y′} {f : Hom x y} → Hom[ f ] x′ y′ → Hom[ id ] x′ (U f .F₀ y′))
    → Type _
  reindex-iso-natural to =
    ∀ {x y x′ x″ y′} {f : Hom x y}
    → (f′ : Hom[ f ] x″ y′) (g′ : Hom[ id ] x′ x″)
    → to (hom[ idr _ ] (f′ ∘′ g′)) ≡[ sym (idl id) ] to f′ ∘′ g′

  reindex→weak-cartesian-lift
    : (to : ∀ {x y x′ y′} {f : Hom x y} → Hom[ f ] x′ y′ → Hom[ id ] x′ (U f .F₀ y′))
    → (eqv : ∀ {x y x′ y′} {f : Hom x y} → is-equiv (to {x} {y} {x′} {y′} {f}))
    → (natural : reindex-iso-natural to)
    → ∀ {x y y′} {f : Hom x y}
    → Weak-cartesian-lift f y′
  reindex→weak-cartesian-lift to to-eqv natural {y′ = y′} {f = f} = weak-lift where
    open Weak-cartesian-lift
    open is-weak-cartesian

    from : ∀ {x y x′ y′} {f : Hom x y} → Hom[ id ] x′ (U f .F₀ y′) → Hom[ f ] x′ y′
    from = equiv→inverse to-eqv

    from-natural
      : ∀ {x y} {f : Hom x y} {x′ x″ : Ob[ x ]} {y′ : Ob[ y ]}
      → (f′ : Hom[ id ] x″ (U f .F₀ y′)) (g′ : Hom[ id ] x′ x″)
      → from (hom[ idl id ] (f′ ∘′ g′)) ≡[ sym (idr f) ] from f′ ∘′ g′
    from-natural {f = f} f′ g′ =
      to-pathp⁻ $ ap fst $ is-contr→is-prop (to-eqv .is-eqv (hom[ idl id ] (f′ ∘′ g′)))
        (from (hom[ idl id ] (f′ ∘′ g′)) , equiv→counit to-eqv _)
        (hom[ idr f ] (from f′ ∘′ g′) , from-pathp⁻ (natural (from f′) g′) ∙
                                        (hom[]⟩⟨ ap (_∘′ g′) (equiv→counit to-eqv _)))

    weak-lift : Weak-cartesian-lift f y′
    weak-lift .x′ = U f .F₀ y′
    weak-lift .lifting = from id′
    weak-lift .weak-cartesian .universal g′ = to g′
    weak-lift .weak-cartesian .commutes g′ = to-pathp $
      hom[] (from id′ ∘′ to g′)   ≡˘⟨ from-pathp⁻ (from-natural id′ (to g′)) ⟩
      from (hom[] (id′ ∘′ to g′)) ≡⟨ ap from idl[] ⟩
      from (to g′)                ≡⟨ equiv→unit to-eqv g′ ⟩
      g′ ∎
    weak-lift .weak-cartesian .unique {g′ = g′} h′ p =
      h′                          ≡˘⟨ idl[] {p = idl id} ⟩
      hom[] (id′ ∘′ h′)           ≡˘⟨  hom[]⟩⟨ ap (_∘′ h′) (equiv→counit to-eqv id′) ⟩
      hom[] (to (from id′) ∘′ h′) ≡˘⟨ from-pathp⁻ (natural (from id′) h′) ⟩
      to (hom[] (from id′ ∘′ h′)) ≡⟨ ap to (from-pathp p) ⟩
      to g′                       ∎
```
-->
