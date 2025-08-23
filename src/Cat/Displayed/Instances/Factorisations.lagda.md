<!--
```agda
open import Cat.Instances.Shape.Interval
open import Cat.Displayed.Section
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Instances.Factorisations where
```

<!--
```agda
open Displayed
open Functor
open _=>s_
open _=>_
```
-->

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C
```
-->

# The displayed category of factorisations

Given a category $\cC$, we can define a [[displayed category]] $\cC^3
\liesover \operatorname{Arr}(\cC)$ over the [[arrow category]]
$\Arr{\cC}$ where an object over $f : X \to Y$ consists of a
factorisation
$$
X \xto{f} Y = X \xto{m} I \xto{e} Y
$$
of $f$ through some choice of object $M$. This is akin to the
non-displayed notion of [factorisation], but without the reference to
pre-existing classes $M$ and $E$ for $m$ and $e$ to belong to.

[factorisation]: Cat.Morphism.Factorisation.html

```agda
  record Splitting {X Y : ⌞ C ⌟} (f : Hom X Y) : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      {mid} : ⌞ C ⌟
      map   : Hom X mid
      out   : Hom mid Y
      com   : f ≡ out ∘ map
```

<!--
```agda
  {-# INLINE Splitting.constructor #-}

  open Splitting public
```
-->

A morphism between splittings lying over a square from $f$ to $g$ in the
arrow category, depicted in blue in the diagram below, is a map $i : I
\to I'$ between the "middle" objects of the two factorisations making
both the top and bottom rectangles commute.

~~~{.quiver .attach-around}
\[\begin{tikzcd}[ampersand replacement=\&]
  \textcolor{rgb,255:red,92;green,92;blue,214}{X} \&\& \textcolor{rgb,255:red,92;green,92;blue,214}{{X'}} \\
  I \&\& {I'} \\
  \textcolor{rgb,255:red,92;green,92;blue,214}{Y} \&\& \textcolor{rgb,255:red,92;green,92;blue,214}{{Y'}}
  \arrow["t", color={rgb,255:red,92;green,92;blue,214}, from=1-1, to=1-3]
  \arrow["m", from=1-1, to=2-1]
  \arrow["f"', color={rgb,255:red,92;green,92;blue,214}, curve={height=12pt}, from=1-1, to=3-1]
  \arrow["{m'}"', from=1-3, to=2-3]
  \arrow["g", color={rgb,255:red,92;green,92;blue,214}, curve={height=-12pt}, from=1-3, to=3-3]
  \arrow["i"{description}, dashed, from=2-1, to=2-3]
  \arrow["o", from=2-1, to=3-1]
  \arrow["{o'}"', from=2-3, to=3-3]
  \arrow["b"', color={rgb,255:red,92;green,92;blue,214}, from=3-1, to=3-3]
\end{tikzcd}\]
~~~

```agda
  record
    Interpolant
      {X X' Y Y'} {f : Hom X Y} {g : Hom X' Y'}
      (sq : Homᵃ C f g) (s : Splitting f) (t : Splitting g)
      : Type ℓ where
```

<!--
```agda
    no-eta-equality
    private
      module s = Splitting s
      module t = Splitting t
```
-->

```agda
    field
      map : Hom (s .mid) (t .mid)
      sq₀ : t.map ∘ sq .top ≡ map     ∘ s.map
      sq₁ : t.out ∘ map     ≡ sq .bot ∘ s.out
```

In the literature on factorisation systems, the [[total category]] of
this displayed category is identified with the diagram category $\cC^3$
of composable *triples*[^three] in $\cC$, and its projection functor
$\cC^3 \to \Arr{\cC}$ sends each triple to its composite. In a proof
assistant, defining this as a displayed category is superior because it
lets us define [[*sections*|section of a displayed category]] of the
composition functor--- which send each arrow to a factorisation--- where
the domain and codomain of a factored arrow are *definitionally* the
ones we started with.

[^three]:
    Note that here $3$ denotes the *ordinal* $\{0 \le 1 \le 2\}$,
    and not the set with three elements.

<!--
```agda
  {-# INLINE Interpolant.constructor #-}
  open Interpolant public
unquoteDecl H-Level-Interpolant = declare-record-hlevel 2 H-Level-Interpolant (quote Interpolant)

module _ {o ℓ} {C : Precategory o ℓ} where
  open Precategory C

  Interpolant-pathp
    : ∀ {X X' Y Y'} {f : Hom X Y} {g : Hom X' Y'} {sq sq' : Homᵃ C f g} {p : sq ≡ sq'} {s : Splitting C f} {t : Splitting C g}
    → {f : Interpolant C sq s t} {g : Interpolant C sq' s t}
    → f .map ≡ g .map
    → PathP (λ i → Interpolant C (p i) s t) f g
  Interpolant-pathp p i .map = p i
  Interpolant-pathp {p = q} {s} {t} {f} {g} p i .sq₀ = is-prop→pathp (λ i → Hom-set _ _ (t .map ∘ q i .top) (p i ∘ s .map)) (f .sq₀) (g .sq₀) i
  Interpolant-pathp {p = q} {s} {t} {f} {g} p i .sq₁ = is-prop→pathp (λ i → Hom-set _ _ (t .out ∘ p i) (q i .bot ∘ s .out)) (f .sq₁) (g .sq₁) i

  instance
    Extensional-Interpolant
      : ∀ {X X' Y Y' ℓr} {f : Hom X Y} {g : Hom X' Y'} {sq : Homᵃ C f g} {s : Splitting C f} {t : Splitting C g}
      → ⦃ _ : Extensional (Hom (s .mid) (t .mid)) ℓr ⦄
      → Extensional (Interpolant C sq s t) ℓr
    Extensional-Interpolant = injection→extensional! Interpolant-pathp auto

module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C
```
-->

```agda
  Factorisations' : Displayed (Arr C) _ _
  Factorisations' .Ob[_]  (_ , _ , f) = Splitting C f
  Factorisations' .Hom[_]     sq s s' = Interpolant C sq s s'

  Factorisations' .id' = record { sq₀ = id-comm ; sq₁ = id-comm }

  Factorisations' ._∘'_ f g = record where
    map = f .map ∘ g .map
    sq₀ = pulll (f .sq₀) ∙ extendr (g .sq₀)
    sq₁ = pulll (f .sq₁) ∙ extendr (g .sq₁)
```

<details>
<summary>The only interesting to note about the coherence data here is
that we can reindex `Interpolant`{.Agda}s over identifications between
squares without disturbing the middle map.</summary>

```agda
  Factorisations' .Hom[_]-set f x y = hlevel 2

  Factorisations' .idr'   f     = Interpolant-pathp (idr _)
  Factorisations' .idl'   f     = Interpolant-pathp (idl _)
  Factorisations' .assoc' f g h = Interpolant-pathp (assoc _ _ _)

  Factorisations' .hom[_] p' f = record where
    map = f .map
    sq₀ = ap₂ _∘_ refl (sym (ap top p')) ∙ f .sq₀
    sq₁ = f .sq₁ ∙ ap₂ _∘_ (ap bot p') refl
  Factorisations' .coh[_] p' f = Interpolant-pathp refl
```

</details>

# Functorial factorisations

::: {.definition #functorial-factorisation}
A **(functorial) factorisation** on $\cC$ is a [[section|section of a
displayed category]] of `Factorisations'`{.Agda}. These naturally
assemble into a category.
:::

```agda
  Factorisation : Type _
  Factorisation = Section Factorisations'

  Factorisations : Precategory _ _
  Factorisations = Sections Factorisations'
```

We shall now identify some first properties of functorial
factorisations.

<!--
```agda
module Factorisation {o ℓ} {C : Precategory o ℓ} (fac : Factorisation C) where
  open Cat.Reasoning C
  open Section fac
  private module Arr = Cat.Reasoning (Arr C)

  module _ {X Y : ⌞ C ⌟} (f : Hom X Y) where
    open Splitting (Section.S₀ fac (X , Y , f))
      renaming (mid to Mid ; map to λ→ ; out to ρ→ ; com to factors)
      public

  module _ {u v w x : ⌞ C ⌟} {f : Hom u v} {g : Hom w x} (sq : Homᵃ C f g) where
    open Interpolant (Section.S₁ fac sq) using (map) public
```
-->

<details>
<summary>Because the morphism-assignment of sections has a pretty
dependent type, we can not immediately reuse the functor reasoning
combinators for functorial factorisations.

Adapting them to this case is pretty straightforward, though, so here
are the ones we'll need.
</summary>

```agda
  adjust
    : ∀ {u v w x} {f : Hom u v} {g : Hom w x} {sq sq' : Homᵃ C f g}
    → sq ≡ sq'
    → S₁ sq .map ≡ S₁ sq' .map
  adjust p = apd (λ i → map) (ap S₁ p)

  weave
    : ∀ {u v w x w' x' y z} {f : Hom u v} {g : Hom w x} {g' : Hom w' x'} {h : Hom y z}
    → {sq : Homᵃ C g h}  {sq' : Homᵃ C f g}
    → {tq : Homᵃ C g' h} {tq' : Homᵃ C f g'}
    → sq Arr.∘ sq' ≡ tq Arr.∘ tq'
    → S₁ sq .map ∘ S₁ sq' .map
    ≡ S₁ tq .map ∘ S₁ tq' .map
  weave p = apd (λ i → map) (sym (S-∘ _ _)) ∙∙ adjust p ∙∙ apd (λ i → map) (S-∘ _ _)

  collapse
    : ∀ {u v w x y z} {f : Hom u v} {g : Hom w x} {h : Hom y z}
    → {sq : Homᵃ C g h} {sq' : Homᵃ C f g} {tq : Homᵃ C f h}
    → sq Arr.∘ sq' ≡ tq
    → S₁ sq .map ∘ S₁ sq' .map
    ≡ S₁ tq .map
  collapse p = apd (λ i → map) (sym (S-∘ _ _)) ∙ adjust p

  expand
    : ∀ {u v w x y z} {f : Hom u v} {g : Hom w x} {h : Hom y z}
    → {sq : Homᵃ C g h} {sq' : Homᵃ C f g} {tq : Homᵃ C f h}
    → tq ≡ sq Arr.∘ sq'
    → S₁ tq .map
    ≡ S₁ sq .map ∘ S₁ sq' .map
  expand p = sym (collapse (sym p))

  annihilate : ∀ {u v} {f : Hom u v} {sq : Homᵃ C f f} → sq ≡ Arr.id → S₁ sq .map ≡ id
  annihilate p = adjust p ∙ apd (λ i → map) S-id
```

</details>

Given a functorial factorisation, we can define two endofunctors on
$\Arr{\cC}$, referred to simply as its *left* and *right* parts, which
send a morphism $X \xto{f} Y$ to $L(f) = X \xto{m} I(f)$ and $R(f) =
I(f) \xto{o} Y$, respectively, while sending a square to either the top
or bottom rectangles in the definition of `Interpolant`{.Agda}.

::: commented-out

:::{.definition #left-factor-functor}
If $F$ is a [[functorial factorisation]] on $\cC$, splitting an $X
\xto{f} Y$ into $X \xto{\lambda} M \xto{\rho} Y$ the **left factor
functor** on $\Arr{\cC}$ is $L(f) = X \xto{\lambda} M$. This is
naturally made into a *copointed endofunctor*, with the counit assigning
to each arrow $X \xto{f} Y$ the square

~~~{.quiver .attach-above}
\[\begin{tikzcd}[ampersand replacement=\&]
  X \&\& X \\
  \\
  M \&\& {Y\text{.}}
  \arrow[equals, from=1-1, to=1-3]
  \arrow["\lambda"', from=1-1, to=3-1]
  \arrow["f", from=1-3, to=3-3]
  \arrow["\rho"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~
:::

:::{.definition #right-factor-functor}
If $F$ is a [[functorial factorisation]] on $\cC$, splitting an $X
\xto{f} Y$ into $X \xto{\lambda} M \xto{\rho} Y$ the **right factor
functor** on $\Arr{\cC}$ is $R(f) = M \xto{\rho} Y$. This is naturally
made into a *pointed endofunctor*, with the unit assigning to each arrow
$X \xto{f} Y$ the square

~~~{.quiver .attach-above}
\[\begin{tikzcd}[ampersand replacement=\&]
	M \&\& X \\
	\\
	Y \&\& {Y\text{.}}
	\arrow["\lambda", from=1-1, to=1-3]
	\arrow["\rho"', from=1-1, to=3-1]
	\arrow["f", from=1-3, to=3-3]
	\arrow[equals, from=3-1, to=3-3]
\end{tikzcd}\]
~~~
:::

:::

```agda
  L : Functor (Arr C) (Arr C)
  L .F₀ (X , Y , f) = X , Mid f , λ→ f
  L .F₁ {X , Z , f} {X' , Z' , f'} sq = record
    { top = sq .top
    ; bot = S₁ sq .map
    ; com = S₁ sq .sq₀
    }
  L .F-id    = ext (refl ,ₚ annihilate refl)
  L .F-∘ f g = ext (refl ,ₚ expand refl)

  R : Functor (Arr C) (Arr C)
  R .F₀ (X , Y , f) = Mid f , Y , ρ→ f
  R .F₁ {X , Z , f} {X' , Z' , f'} sq = record
    { top = S₁ sq .map
    ; bot = sq .bot
    ; com = S₁ sq .sq₁
    }
  R .F-id    = ext (annihilate refl ,ₚ refl)
  R .F-∘ f g = ext (expand refl     ,ₚ refl)
```

These endofunctors are naturally *(co)pointed*, meaning that the left
(resp. right) functor admits a natural transformation *to* (resp.
*from*) the identity on $\Arr{\cC}$. These transformations send a
morphism to a triangle consisting of the complementary part of the
factorisation.

```agda
  L-ε : L => Id
  L-ε .η (X , Y , f) = record
    { top = id
    ; bot = ρ→ f
    ; com = elimr refl ∙ factors f
    }
  L-ε .is-natural x y f = ext (id-comm-sym ,ₚ S₁ f .sq₁)

  R-η : Id => R
  R-η .η (X , Y , f) = record
    { top = λ→ f
    ; bot = id
    ; com = sym (factors f) ∙ introl refl
    }
  R-η .is-natural x y f = ext (S₁ f .sq₀ ,ₚ id-comm-sym)
```

<!--
```agda
-- This is an ugly hack to pretend that morphisms in Factorisations have
-- record fields themselves. Note that we have to choose different names
-- to not clash with those from _=>s_, and that these can not be
-- overloaded.

module
  _ {o ℓ} {C : Precategory o ℓ} {X Y : ⌞ Factorisation C ⌟}
    (f : Factorisations C .Precategory.Hom X Y)
  where
  open Cat.Reasoning C

  private
    module X = Factorisation X
    module Y = Factorisation Y

    record Hack : Type (o ⊔ ℓ) where
      field
        mapᶠᶠ : ∀ {x y} (g : Hom x y) → Hom (X.Mid g) (Y.Mid g)

        sq₀ᶠᶠ : ∀ {x y} (g : Hom x y) → Y.λ→ g ≡ mapᶠᶠ g ∘ X.λ→ g
        sq₁ᶠᶠ : ∀ {x y} (g : Hom x y) → Y.ρ→ g ∘ mapᶠᶠ g ≡ X.ρ→ g

        comᶠᶠ
          : ∀ {w x y z} {g : Hom w x} {h : Hom y z} (i : Homᵃ C g h)
          → mapᶠᶠ h ∘ X .Section.S₁ i .map ≡ Y .Section.S₁ i .map ∘ mapᶠᶠ g

    hack : Hack
    hack = record
      { mapᶠᶠ = λ g → f .map (_ , _ , g) .map
      ; sq₀ᶠᶠ = λ g → intror refl ∙ f .map (_ , _ , g) .sq₀
      ; sq₁ᶠᶠ = λ g → f .map (_ , _ , g) .sq₁ ∙ eliml refl
      ; comᶠᶠ = λ i → apd (λ i → map) (f .com _ _ i)
      }

  open Hack hack public
```
-->
