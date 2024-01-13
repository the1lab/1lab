<!--
```agda
open import Cat.Functor.Bifunctor
open import Cat.Instances.Functor
open import Cat.Monoidal.Base
open import Cat.Prelude

import Cat.Reasoning
import Cat.Monoidal.Reasoning
```
-->

```agda
module Cat.Enriched.Base where
```

# Enriched Categories

One of the most useful tools of category theory is the notion of
**internal language**, which allows us to interpret definitions and
theorems from ordinary mathematics into structured categories. This
makes working with the category in question much easier, while
simultaneously generalizing existing mathematical ideas. If we take this
perspective seriously, we are led to an inevitable question: can we
replace the ambient type theory used to perform category theory with the
internal language of a suitably structured category?

## Enriching in Cartesian Categories

As a warm up, we will use the internal language of a cartesian category
$\cV$ as the type theory for defining a category. A category $\cC$
defined using the internal language of $\cV$ has the usual type of
objects $Ob_{\cC}$, but the hom sets $\cC(A, B)$ are replaced with
hom-**objects** $Hom_{\cC} : Ob_{\cC} \to Ob_{\cC} \to Ob_{\cV}$. The
identity morphisms are replaced with generalized objects $id_{\cC} :
\cV(\Gamma, \cC(A, A))$, and composition is replaced with an operation
on generalized objects

$$
\circ_{\cC} : \cV(\Gamma, \cC(B, C)) \to \cV(\Gamma, \cC(A, B)) \to \cV(\Gamma, \cC(A, C))
$$

The equations are what one would expect, and we also require naturality
conditions for both identity and composition:
$$
\begin{align*}
  & \forall (\sigma : \cV(\Gamma, \Delta)), id_{\cC} \circ_{\cV} \sigma = id_{\cC} \\
  & \forall (f : \cV(\Delta, \cC(B, C))) (g : \cV(\Delta, \cC(A, C))) (\sigma : \cV(\Gamma, \Delta)),
    (f \circ_{\cC} g) \circ_{\cV} \sigma = (f \circ_{\cV} \sigma) \circ_{\cC} (g \circ_{\cV} \sigma)
\end{align*}
$$

Type theoretically, these naturality conditions describe substitution
operates in identity morphisms and composites. We call $\cC$ a category
**enriched** in a cartesian category $\cV$.

Astute readers may note that we don't actually use the cartesian
structure of $\cV$ anywhere in the above definition. However, it is
crucial for making this definition well-behaved, as it gives us a
well-behaved internal language. The terminal object acts as the empty
context, the product gives us context concatenation/extension.
Furthermore, the projection maps give us the ability to weaken
generalized objects $f : \cV(\Gamma, \cC(A, B))$ to generalized
objects $f \circ \pi_1 : \cV(\Gamma \times \Delta, \cC(A, B))$, and
the universal property of products gives us contraction and weakening.
Finally, the universal property of the terminal object allows us
to bring generalized objects $f : \cV(\top, \cC(A, B))$ into an arbitrary
context $\Gamma$ via precomposition with $! : \Gamma \to \top$.

Both $\pi$ and $!$ are what allow us to define $id_{\cC}$ and
$\circ_{\cC}$ relative to an arbitrary context $\Gamma$, as opposed
following the traditional categorical path where operations are defined
in the smallest context possible:

$$
\begin{align*}
  & id_{\cC} : \cV(\top, \cC(A, A)) \\
  & \circ_{\cC} : \cV(\cC(B, C) \times \cC(A, B), \cC(A, C))
\end{align*}
$$

To get from this definition to our earlier one, we use [Yoneda] to
embed into the category of presheaves, which integrates much more nicely
with the ambient type theory.

[Yoneda]: Cat.Functor.Hom.html#the-yoneda-embedding

$$
\begin{align*}
  & id_{\cC} : \cV(\top, \cC(A, A)) \\
  & \circ_{\cC} : \cV(\Gamma, \cC(B, C)) \to \cV(\Delta, \cC(A, B)) \to \cV(\Gamma \times \Delta, \cC(A, C))
\end{align*}
$$

We can then then precompose with $!$ and $\pi$, with $!$ and $\pi$ in
the relevant positions, bringing all of the generalized objects into the
same context which we can then universally quantify over. This uses the
fact that limits are representable.

## Enrichment, Generally

Enrichment in cartesian categories is nice, though not as general as
we would like. Ideally, we would be able to replace the cartesian category
$(\cV, \top \times)$ with a [monoidal] category $(\cV, I, \otimes)$,
as monoidal categories are more natural from a categorical perspective,
and have many more (useful!) examples.

[monoidal]: Cat.Monoidal.Base.html

How does this work out on the type theory side? We still have an empty
context (the monoidal unit) and context concatenation (the monoidal
tensor).  However, we've gotten rid of all of our structural operations,
moving from a structural type theory to a sub-structural
one. Specifically, our type theory is now ordered-linear, as we lack
exchange, contraction, and weakening. This completely breaks our earlier
approach, as we can no longer define elements in an arbitrary context
$\Gamma$.

To see how this fails, let's start wit the category theorist's definition,
where all generalized objects are defined in a minimal context. This
yields the following pair of operations:

$$
\begin{align*}
  & id_{\cC} : \cV(I, \cC(A, A)) \\
  & \circ_{\cC} : \cV(\cC(B, C) \otimes \cC(A, B), \cC(A, C))
\end{align*}
$$

This is truly awful to work with: it forces us to write in a point-free
manner, and makes us to handle all contextual manipulations by hand via
associators and unitors.  As in the cartesian case, we can still apply
Yoneda to the composition, yielding the following operation:

$$
\circ_{\cC} : \cV(\Gamma, \cC(B, C)) \to \cV(\Delta, \cC(A, B)) \to \cV(\Gamma \otimes \Delta, \cC(A, C))
$$
This solves the point-free issue, but we still need to deal with
associators and unitors, which are the real source of suffering.
Unfortunately, we can't apply the same trick to move
everything into the same context, as we lack the structural operations
to do so.

The solution, as usual, comes from the type theory. Our earlier attempt
is a categorical version of context-splitting, which is one way encoding
of the rules of linear type theory. It operates by splitting up the
context whenever a term contains multiple sub-terms, ensuring that each
variable can only be available in one portion of the term.  If we were
to write out the composition operation in type-theoretic syntax, it
would look something like this:

$$
\frac{\Gamma \vdash f : \cC(B, C) \qquad \Delta \vdash g : \cC(A, B)}{\Gamma, \Delta \vdash f \circ_{\cC} g : \cC(A, C)}
$$

However, it is not the *only* way of encoding linearity! In particular,
linearity can be encoded by using leftover typing, as in
[@Allais:2018]. The core of the idea is that we modify the typing
judgement to return a context denoting the unused variables in a
derivation. Applying this technique to the composition operation, we get
the following typing rule.

$$
\frac{\Gamma \vdash f : \cC(B, C) \leadsto \Delta \qquad \Delta \vdash g : \cC(A, B) \leadsto \Psi}{\Gamma \vdash f \circ_{\cC} g : \cC(A, C) \leadsto \Psi}
$$

We can encode this type-theoretic insight categorically by modifying
the identity morphism and composition to the following versions:

$$
\begin{align*}
& id_{\cC} : \cV(\Gamma, \Gamma \otimes \cC(A, C)) \\
& \circ_{\cC} : \cV(\Delta, \Psi \otimes \cC(B, C)) \to \cV(\Gamma, \Delta \otimes \cC(A, B)) \to \cV(\Gamma, \Psi \otimes \cC(A, C))
\end{align*}
$$


As this formulation avoids tensors on the left-hand side, we no longer
need to perform any contextual manipulations when stating laws, which
means that we can totally avoid associators, unitors, and the coherence
problems that come with them!

With all of that motivation out of the way, we can proceed by giving
an Agda definition of an enriched category. Objects and morphisms
are straightforward.

```agda
record Enriched-precategory
  {o ℓ} {V : Precategory o ℓ}
  (V-monoidal : Monoidal-category V)
  (o' : Level) : Type (o ⊔ ℓ ⊔ lsuc o') where
  private
    module V = Cat.Reasoning V
    open Monoidal-category V-monoidal
  field
    Obv : Type o'
    Hom-ob : Obv → Obv → V.Ob
```

We provide an alias for our generalized objects with leftover typing,
as it can get a bit tedious to type.

```agda
  Homv : V.Ob → V.Ob → Obv → Obv → Type ℓ
  Homv Γ Δ x y = V.Hom Γ (Δ ⊗ Hom-ob x y)
```

Identity and composites are defined using our leftover typing trick.

```agda
  field
    idv : ∀ {Γ x} → Homv Γ Γ x x
    _∘v_ : ∀ {Γ Δ Ψ x y z}
         → Homv Δ Ψ y z → Homv Γ Δ x y → Homv Γ Ψ x z

  infixr 40 _∘v_
```

The equations are exactly what we would expect for a non-enriched category;
no coherence in sight!

```agda
  field
    idlv : ∀ {Γ Δ x y} → (f : Homv Γ Δ x y) → idv ∘v f ≡ f
    idrv : ∀ {Γ Δ x y} → (f : Homv Γ Δ x y) → f ∘v idv ≡ f
    assocv
      : ∀ {Γ Δ Ψ Θ w x y z}
      → (f : Homv Ψ Θ y z) → (g : Homv Δ Ψ x y) → (h : Homv Γ Δ w x)
      → f ∘v (g ∘v h) ≡ (f ∘v g) ∘v h
```

Unfortunately, these type theoretic methods are not free, and the price
we pay are naturality conditions. Leftover typing means that we have
even more than normal, as the context shows up on both the left
and right hand side of generalized objects. However, naturality is
much less annoying than coherence, so it's a price we gladly pay.

```agda
    idv-natural
      : ∀ {Γ Δ x}
      → (σ : V.Hom Γ Δ)
      → idv V.∘ σ ≡ (σ ◀ Hom-ob x x) V.∘ idv
    ∘v-naturall
      : ∀ {Γ Δ Ψ Θ x y z}
      → (σ : V.Hom Ψ Θ)
      → (f : Homv Δ Ψ y z) → (g : Homv Γ Δ x y)
      → (σ ◀ Hom-ob x z) V.∘ (f ∘v g) ≡ ((σ ◀ Hom-ob y z) V.∘ f) ∘v g
    ∘v-natural-inner
      : ∀ {Γ Δ Ψ Θ x y z}
      → (f : Homv Ψ Θ y z)
      → (σ : V.Hom Δ Ψ)
      → (g : Homv Γ Δ x y)
      → f ∘v ((σ ◀ Hom-ob x y) V.∘ g) ≡ (f V.∘ σ) ∘v g
    ∘v-naturalr
      : ∀ {Γ Δ Ψ Θ x y z}
      → (f : Homv Ψ Θ y z) → (g : Homv Δ Ψ x y)
      → (σ : V.Hom Γ Δ)
      → (f ∘v g) V.∘ σ ≡ (f ∘v (g V.∘ σ))
```

### Enriched vs. Internal Categories

Both enriched and [internal categories] aim to replace the ambient
type theory used to define a category with the internal langauge of
another category. However, internal categories internalize the theory
of [strict categories], whereas enriched categories internalize the general
theory of categories. As a result, internal categories tend to highlight
subtle issues of size, whereas enriched categories are a much less
delicate object of study.

[internal categories]: Cat.Internal.Base.html
[strict categories]: Cat.Strict.html

### The Non-Type Theoretic Perspective

So far, we have given a very type-theory-brained account of enriched
categories, which is somewhat revisionist. Enriched categories did not
arise from type-theoretic or logical needs; they were invented to solve
problems faced by the working category theorist. They aim to capture the
common situation where categories don't just have hom-sets, but rather
*structured* hom-sets (IE: hom-groups, hom-monoids, etc). If you
generalize this situation, you arrive at the category-theorists
definition of enriched category that was presented earlier.

## Enriched Functors

Let $(\cV, I, \otimes)$ be a monoidal category, and $\cC$, $\cD$ be
$\cV$-enriched categories. An **$\cV$-enriched functor**
$F : \cC \to \cD$ consists of an mapping of objects
$F_0 : Ob_{\cC} \to Ob_{\cD}$, along with a functorial mapping
$F_1 : \cV(\Gamma, \Delta \otimes \cC(A, B)) \to \cV(\Gamma, \Delta \otimes \cD(F_0(A), F_0(B)))$
of $\cC$ morphisms to $\cD$ morphisms. This may seem complicated, but
it is precisely what we get when we interpret the definition of a functor
into the internal language of $\cV$, and then apply our leftover-typing
trick to it!

```agda
record Enriched-functor
  {ov ℓv oc od} {V : Precategory ov ℓv} {V-monoidal : Monoidal-category V}
  (C : Enriched-precategory V-monoidal oc) (D : Enriched-precategory V-monoidal od)
  : Type (ov ⊔ ℓv ⊔ oc ⊔ od)
  where
  private
    module V = Precategory V
    open Monoidal-category V-monoidal
    module C = Enriched-precategory C
    module D = Enriched-precategory D
  field
    Fv₀ : C.Obv → D.Obv
    Fv₁ : ∀ {Γ Δ x y} → C.Homv Γ Δ x y → D.Homv Γ Δ (Fv₀ x) (Fv₀ y)
    Fv-id : ∀ {Γ x} → Fv₁ (C.idv {Γ} {x}) ≡ D.idv
    Fv-∘ : ∀ {Γ Δ Ψ x y z}
         → (f : C.Homv Δ Ψ y z) → (g : C.Homv Γ Δ x y)
         → Fv₁ (f C.∘v g) ≡ Fv₁ f D.∘v Fv₁ g
```

As per usual, we need to pay the type theory tax. These naturality
conditions are purely mechanical, and often easy to show.

```agda
    Fv-naturall :  ∀ {Γ Δ Ψ x y}
                → (σ : V.Hom Δ Ψ)
                → (f : C.Homv Γ Δ x y)
                → (σ ◀ _) V.∘ Fv₁ f ≡ Fv₁ ((σ ◀ _) V.∘ f)
    Fv-naturalr :  ∀ {Γ Δ Ψ x y}
                → (f : C.Homv Δ Ψ x y)
                → (σ : V.Hom Γ Δ)
                → (Fv₁ f V.∘ σ) ≡ Fv₁ (f V.∘ σ)

open Enriched-functor
```

<!--
```agda
module _
  {ov ℓv}
  {V : Precategory ov ℓv} {V-monoidal : Monoidal-category V}
  where
  private
    module V = Precategory V
    open Monoidal-category V-monoidal
```
-->

As expected, there is an identity enriched functor, and enriched
functors can be composed.

```agda
  Idv
    : ∀ {o} {C : Enriched-precategory V-monoidal o}
    → Enriched-functor C C
  Idv {C = C} = func module Idv where

    func : Enriched-functor _ _
    func .Fv₀ x = x
    func .Fv₁ f = f
    func .Fv-id = refl
    func .Fv-∘ f g = refl
    func .Fv-naturall f σ = refl
    func .Fv-naturalr f σ = refl

  _Fv∘_
    : ∀ {oc od oe}
    → {C : Enriched-precategory V-monoidal oc}
    → {D : Enriched-precategory V-monoidal od}
    → {E : Enriched-precategory V-monoidal oe}
    → Enriched-functor D E → Enriched-functor C D → Enriched-functor C E
  _Fv∘_ {C = C} {D = D} {E = E} F G = func module ∘Fv where

    func : Enriched-functor _ _
    func .Fv₀ x = F .Fv₀ (G .Fv₀ x)
    func .Fv₁ f = F .Fv₁ (G .Fv₁ f)
    func .Fv-id =
      ap (F .Fv₁) (G .Fv-id) ∙ F .Fv-id
    func .Fv-∘ f g =
      ap (F .Fv₁) (G .Fv-∘ f g) ∙ F .Fv-∘ (G .Fv₁ f) (G .Fv₁ g)
    func .Fv-naturall f σ =
      F .Fv-naturall f (G .Fv₁ σ)
      ∙ ap (F .Fv₁) (G .Fv-naturall f σ)
    func .Fv-naturalr f σ =
      F .Fv-naturalr (G .Fv₁ f) σ
      ∙ ap (F .Fv₁) (G .Fv-naturalr f σ)

  infixr 30 _Fv∘_
```

## Enriched Natural Transformations

We also have a notion of natural transformation between enriched functors, known
as an **enriched natural transformation**. This follows our normal recipe for
defining enriched structure: we take the definition of natural transformation,
interpret it into the internal language of $\cV$, and apply the leftover typing
trick.

```agda
record _=>v_ 
  {o ℓ o' o''} {V : Precategory o ℓ} {V-monoidal : Monoidal-category V}
  {C : Enriched-precategory V-monoidal o'} {D : Enriched-precategory V-monoidal o''}
  (F G : Enriched-functor C D)
  : Type (o ⊔ ℓ ⊔ o' ⊔ o'') where
  private
    module V = Precategory V
    open Monoidal-category V-monoidal
    module C = Enriched-precategory C
    module D = Enriched-precategory D
  field
    ηv : ∀ Γ x → D.Homv Γ Γ (F .Fv₀ x) (G .Fv₀ x)
    is-naturalv : ∀ {Γ Δ x y} → (f : C.Homv Γ Δ x y)
                → ηv _ y D.∘v F .Fv₁ f ≡ G .Fv₁ f D.∘v ηv _ x
    ηv-natural : ∀ {Γ Δ x}
               → (σ : V.Hom Γ Δ)
               → ηv _ x V.∘ σ ≡ (σ ◀ _) V.∘ ηv _ x

infix 20 _=>v_
open _=>v_
```

<!--
```agda
module _
  {ov ℓv oc od}
  {V : Precategory ov ℓv} {V-monoidal : Monoidal-category V}
  {C : Enriched-precategory V-monoidal oc}
  {D : Enriched-precategory V-monoidal od}
  {F G : Enriched-functor C D}
  where
  private
    module V = Precategory V
    open Monoidal-category V-monoidal
    module C = Enriched-precategory C
    module D = Enriched-precategory D

  Enriched-nat-path
    : {α β : F =>v G}
    → (∀ Γ x → α .ηv Γ x ≡ β .ηv Γ x)
    → α ≡ β
  Enriched-nat-path p i .ηv Γ x = p Γ x i
  Enriched-nat-path {α = α} {β = β} p i .is-naturalv f =
    is-prop→pathp
      (λ i → V.Hom-set _ _ (p _ _ i D.∘v F .Fv₁ f) (G .Fv₁ f D.∘v p _ _ i))
      (α .is-naturalv f)
      (β .is-naturalv f) i
  Enriched-nat-path {α = α} {β = β} p i .ηv-natural σ =
    is-prop→pathp
      (λ i → V.Hom-set _ _ ((p _ _ i) V.∘ σ) ((σ ◀ _) V.∘ (p _ _ i)))
      (α .ηv-natural σ) (β .ηv-natural σ) i
  
  private unquoteDecl eqv = declare-record-iso eqv (quote _=>v_)

  Enriched-nat-is-set : is-set (F =>v G)
  Enriched-nat-is-set = Iso→is-hlevel 2 eqv $
    Σ-is-hlevel 2 (Π-is-hlevel 2 (λ _ → Π-is-hlevel 2 λ _ → V.Hom-set _ _))
    λ _ → Σ-is-hlevel 2
      (Π-is-hlevel' 2 λ _ → Π-is-hlevel' 2 λ _ → Π-is-hlevel' 2 λ _ → Π-is-hlevel' 2 λ _ →
       Π-is-hlevel 2 λ _ → Path-is-hlevel 2 (V.Hom-set _ _))
    λ _ → (Π-is-hlevel' 2 λ _ → Π-is-hlevel' 2 λ _ → Π-is-hlevel' 2 λ _ →
      Π-is-hlevel 2 λ _ → Path-is-hlevel 2 (V.Hom-set _ _))
```
-->
