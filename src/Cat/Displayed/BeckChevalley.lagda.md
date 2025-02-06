---
description: |
  Beck-Chevalley conditions.
---
<!--
```agda
open import Cat.Displayed.Cocartesian
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Functor.Adjoint.Mate
open import Cat.Functor.Naturality
open import Cat.Functor.Adjoint
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Displayed.Morphism
import Cat.Reasoning

import Cat.Displayed.Cartesian.Indexing
```
-->
```agda
module Cat.Displayed.BeckChevalley where
```

# Beck-Chevalley conditions

Let $\cE \to \cB$ be a [[cartesian fibration]], which we shall view
as a setting for some sort of logic or type theory. In particular, we
shall view the corresponding [[base change]] functors $f^{*} : \cE_{Y} \to \cE_{X}$
as an operation of substitution on predicates/types. This leads to a particularly
tidy definition of quantifiers as [[adjoints]] to base change.

For instance, we can describe existential quantifiers as left adjoints
$\exists_{Y} : \cE_{X \times Y} \to \cE{X}$ to base changes along projections
$\pi : X \times Y \to X$:

- The introduction rule is given by the unit $\eta : \cE_{X}(P, \exists_{Y} (\pi^{*} P))$
- The elimination rule is given by the counit $\eps : \cE_{X \times Y}(\pi^{*}\exists_{Y} P, P)$
- The $\beta$ and $\eta$ rules are given by the zig-zag equations.

This story is quite elegant, but there is a missing piece: how do substitutions
interact with $\exists$, or, in categorical terms, how do base change functors
commute with their left adjoints? In particular, consider the following
diagram:

~~~{.quiver}
\begin{tikzcd}
  {\mathcal{E}_{\Gamma \times X}} && {\mathcal{E}_{\Gamma}} \\
  \\
  {\mathcal{E}_{\Delta \times X} && {\mathcal{E}_{\Delta}}
  \arrow["{\exists_{X}}", from=1-1, to=1-3]
  \arrow["{(\sigma \times \id)^*}"', from=1-1, to=3-1]
  \arrow["{\sigma^{*}}", from=1-3, to=3-3]
  \arrow["{\exist_{X}}"', from=3-1, to=3-3]
\end{tikzcd}
~~~

Ideally, we'd like $(\sigma)^*{\exists_{X} P} \iso \exists_{X}((\sigma \times \id)^{*} P)$;
this corresponds to the usual substitution rule for quantifiers. Somewhat
surprisingly, this does not always hold; we always have a map

$$\exists_{X}((\sigma \times \id)^{*} P) \to (\sigma)^*{\exists_{X} P}$$

that comes from some adjoint yoga, but this map is not neccesarily invertible!
This leads us to the main topic of this page: the **Beck-Chevalley**
conditions are a set of properties that ensure that the aforementioned
map is invertible, which in turn ensures that our quantifiers are stable
under substitution.

## Left Beck-Chevalley conditions

A **left Beck-Chevalley condition** characterises well-behaved left adjoints
to base change. Typically, this is done by appealing to properties of
base change, but we opt to use a a more local definition in
terms of [[cartesian|cartesian map]] and [[cocartesian|cocartesian map]]
maps. This has the benefit of working in displayed categories that may
be missing some cartesian maps.

:::{.definition #left-beck-chevalley-condition}
Explicitly, a square $fg = hk$ in $\cB$ satisfies the left Beck-Chevalley
condition if for every square $f'g' = h'k'$ over $fg = hk$, if $g'$ and
$h'$ are cartesian and $f'$ is cocartesian, then $k'$ is cocartesian.
This is best understood diagramatically: suppose we are in a situation
like the diagram below:

~~~{.quiver}
\begin{tikzcd}
  {A'} &&& {C'} \\
  & {B'} &&& {D'} \\
  A &&& C \\
  & B &&& D
  \arrow["{\mathrm{cocart}}"{description}, color={rgb,255:red,92;green,92;blue,214}, from=1-1, to=1-4]
  \arrow["{\mathrm{cart}}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=2-2]
  \arrow[from=1-1, lies over, to=3-1]
  \arrow["{\mathrm{cart}}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=1-4, to=2-5]
  \arrow[from=1-4, lies over, to=3-4]
  \arrow["{\mathrm{cocart}}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=2-2, to=2-5]
  \arrow[from=2-2, lies over, to=4-2]
  \arrow[from=2-5, lies over, to=4-5]
  \arrow["k"{description}, from=3-1, to=3-4]
  \arrow["g"{description}, from=3-1, to=4-2]
  \arrow["h"{description}, from=3-4, to=4-5]
  \arrow["f"{description}, from=4-2, to=4-5]
\end{tikzcd}
~~~

If all the morphisms marked in red are (co)cartesian, then the morphism
marked in blue must be cocartesian. To put things more succinctly, cocartesian
morphisms can be pulled back along pairs of cartesian morphisms.
:::


<!--
```agda
module _
  {o ℓ o' ℓ'}
  {B : Precategory o ℓ}
  (E : Displayed B o' ℓ')
  where
  open Cat.Reasoning B
  open Displayed E
  open Cat.Displayed.Reasoning E
```
-->

```agda
  record left-beck-chevalley
    {a b c d : Ob}
    (f : Hom b d) (g : Hom a b) (h : Hom c d) (k : Hom a c)
    (p : f ∘ g ≡ h ∘ k)
    : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
    no-eta-equality
    field
      cocart-stable
        : {a' : Ob[ a ]} {b' : Ob[ b ]} {c' : Ob[ c ]} {d' : Ob[ d ]}
        → {f' : Hom[ f ] b' d'} {g' : Hom[ g ] a' b'}
        → {h' : Hom[ h ] c' d'} {k' : Hom[ k ] a' c'}
        → f' ∘' g' ≡[ p ] h' ∘' k'
        → is-cocartesian E f f' → is-cartesian E g g'
        → is-cartesian E h h' → is-cocartesian E k k'
```

This may seem somewhat far removed from the intuition we provided earlier,
so we shall spend some time proving that the two notions are, in fact, equivalent.


<!--
```agda
module _
  {o ℓ o' ℓ'}
  {B : Precategory o ℓ}
  {E : Displayed B o' ℓ'}
  (E-fib : Cartesian-fibration E)
  where
  open Precategory B
  open Displayed E

  open Cat.Displayed.Cartesian.Indexing E E-fib
  open Cat.Displayed.Reasoning E
  open Cat.Displayed.Morphism E

  module E↓ {x} = Precategory (Fibre E x)
  module _ {x y : Ob} (f : Hom x y) (y' : Ob[ y ]) where
    open Cartesian-lift (Cartesian-fibration.has-lift E-fib f y')
      using ()
      renaming (x' to _^*_; lifting to π*)
      public

  module π* {x y : Ob} {f : Hom x y} {y' : Ob[ y ]} where
    open Cartesian-lift (Cartesian-fibration.has-lift E-fib f y')
      hiding (x'; lifting)
      public

  open Functor
  open _=>_

  private
    variable
      a b c d : Ob
      f g h k : Hom a b
```
-->


```agda
  left-beck-iso
    : {Lᵍ : Functor (Fibre E a) (Fibre E b)}
    → {Lʰ : Functor (Fibre E c) (Fibre E d)}
    → Lᵍ ⊣ base-change g
    → Lʰ ⊣ base-change h
    → (p : f ∘ g ≡ h ∘ k)
    → left-beck-chevalley E f g h k p
    → ∀ {c'} → (Lᵍ .F₀ (k ^* c')) ≅↓ (f ^* Lʰ .F₀ c')
  left-beck-iso {g = g} {h = h} {f = f} {k = k} {Lᵍ = Lᵍ} {Lʰ = Lʰ} L⊣g^* L⊣h^* p left-bc {c'} = {!!} where
    module Lᵍ where
      open Functor Lᵍ public
      open _⊣_ L⊣g^* public

    module Lʰ where
      open Functor Lʰ public
      open _⊣_ L⊣h^* public

    open left-beck-chevalley left-bc

    comparison : Lᵍ F∘ base-change k => base-change f F∘ Lʰ
    comparison =
      mate L⊣h^* L⊣g^* (base-change k) (base-change f)
        (Isoⁿ.from (base-change-square-ni p))

    -- α : Hom[ g ] (k ^* c') (f ^* Lʰ.₀ c')
    -- α = π*.universal' {!!} (π* h (Lʰ.F₀ c') ∘' Lʰ.η c' ∘' π* k c')
    α : Hom[ k ] (g ^* Lᵍ.F₀ (k ^* c')) (h ^* {!!})
    α = {!!}

    α-cocartesian : is-cocartesian E k α
    α-cocartesian = cocart-stable {!!} {!!} π*.cartesian π*.cartesian

    module α = is-cocartesian α-cocartesian

    comparison⁻¹ : Hom[ id ] (f ^* Lʰ.₀ c') (Lᵍ.₀ (k ^* c'))
    comparison⁻¹ = {!α.universalv!}
    --   let module foo = is-cocartesian (cocart-stable {a' = g ^* Lᵍ.₀ (k ^* c')} {b' = Lᵍ.₀ (k ^* c')} {c' = h ^* Lʰ.₀ c'} {d' = Lʰ.₀ c'}
    --              {f' = {!!}}
    --              {k' = hom[ {!!} ] ({!!} ∘' {!!} ∘' π* g (Lᵍ.₀ (k ^* c')))} {!!} {!!} π*.cartesian π*.cartesian)
    --   in {!!}
```


-- ## The dual case

-- ```agda
--   record cartesian-beck-chevalley
--     {a b c d : Ob}
--     (f : Hom b d) (g : Hom a b) (h : Hom c d) (k : Hom a c)
--     (p : f ∘ g ≡ h ∘ k)
--     : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
--     no-eta-equality
--     field
--       cart-stable
--         : {a' : Ob[ a ]} {b' : Ob[ b ]} {c' : Ob[ c ]} {d' : Ob[ d ]}
--         → {f' : Hom[ f ] b' d'} {g' : Hom[ g ] a' b'}
--         → {h' : Hom[ h ] c' d'} {k' : Hom[ k ] a' c'}
--         → f' ∘' g' ≡[ p ] h' ∘' k'
--         → is-cocartesian E f f' → is-cartesian E g g'
--         → is-cocartesian E k k' → is-cartesian E h h'
-- ```
