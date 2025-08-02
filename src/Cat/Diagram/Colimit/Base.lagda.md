<!--
```agda
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Instances.Shape.Interval
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.Kan.Reflection
open import Cat.Diagram.Coequaliser
open import Cat.Functor.Kan.Unique
open import Cat.Functor.Coherence
open import Cat.Instances.Functor
open import Cat.Functor.Constant
open import Cat.Functor.Kan.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Colimit.Base where
```

<!--
```agda
private variable
  o ℓ o' ℓ' : Level
```
-->

# Colimits {defines=colimit}

## Idea

Colimits are dual to [[limits]]; much like their duals, they generalize
constructions in several settings to arbitrary categories. A colimit (if
it exists), is the "best solution" to an "identification problem".  This
is in contrast to the limit, which acts as a solution to an "equational
problem".

Therefore, we define colimits in a similar way to limits. the only
difference being that we define the colimit of a diagram $F$ as a
[[left Kan extension]] instead of a [[right Kan extension]]. This
gives us the expected "mapping out" universal property, as opposed to
the "mapping in" property associated to limits.

Note that approach to colimits is not what normally presented in
introductory material. Instead, most books opt to define colimits via
[cocones], as they are less abstract, though harder to work with in the
long run.

[cocones]: Cat.Diagram.Colimit.Cocone.html

<!--
```agda
private variable
  o₁ o₂ o₃ o₄ h₁ h₂ h₃ h₄ : Level
```
-->

```agda
module _ {J : Precategory o₁ h₁} {C : Precategory o₂ h₂} (Diagram : Functor J C) where
  private
    module C = Precategory C

  is-colimit : (x : C.Ob) → Diagram => Const x → Type _
  is-colimit x cocone =
    is-lan !F Diagram (!Const x) cocone

  Colimit : Type _
  Colimit = Lan !F Diagram
```

## Concretely

As mentioned, our definition is very abstract, meaning we can directly
re-use definitions and theorems about Kan extensions in the setting of
colimits. The trade-off is that while working with colimits _in general_
is easier, working with _specific_ colimits becomes more difficult, as
the data we actually care about has been obfuscated.

One particularly egregious failure is... actually constructing colimits.
The definition in terms of `Lan`{.Agda} hides the concrete data behind a
few abstractions, which would be very tedious to write out each time. To
work around this, we provide an auxiliary record type,
`make-is-colimit`{.Agda}, as an intermediate step in constructing left
extensions.

<!--
```agda
module _ {J : Precategory o₁ h₁} {C : Precategory o₂ h₂}
  where
  private
    module J = Precategory J
    module C = Cat.Reasoning C

  record make-is-colimit
    (Diagram : Functor J C) (coapex : C.Ob)
    : Type (o₁ ⊔ h₁ ⊔ o₂ ⊔ h₂)
    where
    no-eta-equality
    open Functor Diagram
```
-->

First, we require morphisms from the every value of the diagram to the
coapex; taken as a family, we call it $\phi$. Moreover, if $f : x \to y$
is a morphism in the "shape" category $\cJ$, we require $\psi y \circ Ff
= \psi x$, which encodes the relevant naturality.

```agda
    field
      ψ : (j : J.Ob) → C.Hom (F₀ j) coapex
      commutes : ∀ {x y} (f : J.Hom x y) → ψ y C.∘ F₁ f ≡ ψ x
```

The rest of the data ensures that $\psi$ is the universal family of maps
with this property; if $\eta_j : Fj \to x$ is another natural family,
then each $\eta_j$ factors through the coapex by a _unique_ universal
morphism:

```agda
      universal
        : ∀ {x : C.Ob}
        → (eta : ∀ j → C.Hom (F₀ j) x)
        → (∀ {x y} (f : J.Hom x y) → eta y C.∘ F₁ f ≡ eta x)
        → C.Hom coapex x
      factors
        : ∀ {j : J.Ob} {x : C.Ob}
        → (eta : ∀ j → C.Hom (F₀ j) x)
        → (p : ∀ {x y} (f : J.Hom x y) → eta y C.∘ F₁ f ≡ eta x)
        → universal eta p C.∘ ψ j ≡ eta j
      unique
        : ∀ {x : C.Ob}
        → (eta : ∀ j → C.Hom (F₀ j) x)
        → (p : ∀ {x y} (f : J.Hom x y) → eta y C.∘ F₁ f ≡ eta x)
        → (other : C.Hom coapex x)
        → (∀ j → other C.∘ ψ j ≡ eta j)
        → other ≡ universal eta p
```

<!--
```agda
    unique₂
      : ∀ {x : C.Ob}
      → (eta : ∀ j → C.Hom (F₀ j) x)
      → (p : ∀ {x y} (f : J.Hom x y) → eta y C.∘ F₁ f ≡ eta x)
      → ∀ {o1} → (∀ j → o1 C.∘ ψ j ≡ eta j)
      → ∀ {o2} → (∀ j → o2 C.∘ ψ j ≡ eta j)
      → o1 ≡ o2
    unique₂ eta p q r = unique eta p _ q ∙ sym (unique eta p _ r)
```
-->

Once we have this data, we can use it to construct a value of type
`is-colimit`{.Agda}. The naturality condition we required above may seem
too weak, but the full naturality condition can be derived from it and
the rest of the data.

<!--
```agda
  open _=>_

  to-cocone
    : ∀ {D : Functor J C} {coapex}
    → make-is-colimit D coapex
    → D => Const coapex
  to-cocone ml .η = ml .make-is-colimit.ψ
  to-cocone ml .is-natural x y f = (ml .make-is-colimit.commutes f) ∙ sym (C.idl _)
```
-->

```agda
  to-is-colimit
    : ∀ {Diagram : Functor J C} {coapex}
    → (mc : make-is-colimit Diagram coapex)
    → is-colimit Diagram coapex (to-cocone mc)
  to-is-colimit {Diagram} {coapex} mkcolim = colim where
    open make-is-colimit mkcolim
    open is-lan
    open Functor

    colim : is-colimit Diagram coapex (to-cocone mkcolim)
    colim .σ {M = M} α .η _ =
      universal (α .η) (λ f → α .is-natural _ _ f ∙ C.eliml (M .F-id))
    colim .σ {M = M} α .is-natural _ _ _ = C.idr _ ∙ C.introl (M .F-id)
    colim .σ-comm {α = α} = ext λ j → factors (α .η) _
    colim .σ-uniq {α = α} {σ' = σ'} p = ext λ _ →
      sym $ unique (α .η) _ (σ' .η _) (λ j → sym (p ηₚ j))
```

<!--
```agda
  -- We often find ourselves working with something that isn't a colimit
  -- on the nose due to some annoying extensionality reasons involving
  -- functors '⊤Cat → C'
  -- We could use some general theorems of Kan extensions to adjust the
  -- colimit, but this has better definitional behaviour.
  generalize-colimitp
    : ∀ {D : Functor J C} {K : Functor ⊤Cat C}
    → {eta : D => (Const (Functor.F₀ K tt))} {eta' : D => K F∘ !F}
    → is-lan !F D (!Const (Functor.F₀ K tt)) eta
    → (∀ {j} → eta .η j ≡ eta' .η j)
    → is-lan !F D K eta'
  generalize-colimitp {D} {K} {eta} {eta'} lan q = lan' where
    module lan = is-lan lan
    open is-lan
    open Functor

    lan' : is-lan !F D K eta'
    lan' .σ α = !constⁿ (lan.σ α .η tt)
    lan' .σ-comm {M} {α} = ext λ j →
        ap (_ C.∘_) (sym q)
      ∙ lan.σ-comm {α = α} ηₚ _
    lan' .σ-uniq {M} {α} {σ'} r = ext λ j →
      lan.σ-uniq {σ' = !constⁿ (σ' .η tt)}
        (ext λ j → r ηₚ j ∙ ap (_ C.∘_) (sym q)) ηₚ j

  to-is-colimitp
    : ∀ {D : Functor J C} {K : Functor ⊤Cat C} {eta : D => K F∘ !F}
    → (mk : make-is-colimit D (K · tt))
    → (∀ {j} → to-cocone mk .η j ≡ eta .η j)
    → is-lan !F D K eta
  to-is-colimitp {D} {K} {eta} mkcolim p =
    generalize-colimitp (to-is-colimit mkcolim) p
```
-->

The concrete interface of `make-is-colimit`{.Agda} is also handy for
_consuming_ specific colimits. To enable this use case, we provide a
function which **un**makes a colimit.

```agda
  unmake-colimit
    : ∀ {D : Functor J C} {F : Functor ⊤Cat C} {eta}
    → is-lan !F D F eta
    → make-is-colimit D (Functor.F₀ F tt)
  unmake-colimit {D} {F} {eta} colim = mc module unmake-colimit where
    coapex = Functor.F₀ F tt
    module eta = _=>_ eta
    open is-lan colim
    open Functor D
    open make-is-colimit
    open _=>_

    module _ {x} (eta : ∀ j → C.Hom (F₀ j) x)
                 (p : ∀ {x y} (f : J.Hom x y) →  eta y C.∘ F₁ f ≡ eta x)
      where

      eta-nt : D => Const x
      eta-nt .η = eta
      eta-nt .is-natural _ _ f = p f ∙ sym (C.idl _)

      hom : C.Hom coapex x
      hom = σ {M = !Const x} eta-nt .η tt

    mc : make-is-colimit D coapex
    mc .ψ = eta.η
    mc .commutes f = eta.is-natural _ _ f ∙ C.eliml (F .Functor.F-id)
    mc .universal = hom
    mc .factors e p = σ-comm {α = eta-nt e p} ηₚ _
    mc .unique {x = x} eta p other q =
      sym $ σ-uniq {σ' = other-nt} (ext λ j → sym (q j)) ηₚ tt
      where
        other-nt : F => !Const x
        other-nt .η _ = other
        other-nt .is-natural _ _ _ = C.elimr (F .Functor.F-id) ∙ sym (C.idl _)
```

<!--
```agda
  to-colimit
    : ∀ {D : Functor J C} {K : Functor ⊤Cat C} {eta : D => K F∘ !F}
    → is-lan !F D K eta
    → Colimit D
  to-colimit c .Lan.Ext = _
  to-colimit c .Lan.eta = _
  to-colimit c .Lan.has-lan = c
```
-->

<!--
```agda
module is-colimit
  {J : Precategory o₁ h₁} {C : Precategory o₂ h₂}
  {D : Functor J C} {F : Functor ⊤Cat C} {eta : D => F F∘ !F}
  (t : is-lan !F D F eta)
  where

  open make-is-colimit (unmake-colimit {F = F} t) public
```
-->

We also provide a similar interface for the bundled form of colimits.

```agda
module Colimit
  {J : Precategory o₁ h₁} {C : Precategory o₂ h₂} {D : Functor J C} (L : Colimit D)
  where
```

<!--
```agda
  private
    import Cat.Reasoning J as J
    import Cat.Reasoning C as C
    module Diagram = Functor D
    open Functor
    open _=>_

  open Lan L public
```
-->

The coapex of the colimit can be obtained by applying the extension functor
to the single object of `⊤Cat`{.Agda}.

```agda
  coapex : C.Ob
  coapex = Ext .F₀ tt
```

Furthermore, we can show that the apex is the colimit, in the sense of
`is-colimit`{.Agda}, of the diagram. You'd think this is immediate, but
unfortunately, proof assistants: `is-colimit`{.Agda} asks for _the_
constant functor functor $\{*\} \to \cC$ with value `coapex` to be a Kan
extension, but `Colimit`{.Agda}, being an instance of `Lan`{.Agda},
packages an _arbitrary_ functor $\{*\} \to \cC$.

Since Agda does not compare functors for $\eta$-equality, we have to
shuffle our data around manually. Fortunately, this isn't a very long
computation.

```agda
  cocone : D => Const coapex
  cocone .η = eta .η
  cocone .is-natural x y f =
    eta .is-natural x y f ∙ ap (C._∘ _) (Ext .F-id)

  has-colimit : is-colimit D coapex cocone
  has-colimit .is-lan.σ α .η = σ α .η
  has-colimit .is-lan.σ α .is-natural x y f =
    ap (_ C.∘_) (sym (Ext .F-id)) ∙ σ α .is-natural tt tt tt
  has-colimit .is-lan.σ-comm = ext (σ-comm ηₚ_)
  has-colimit .is-lan.σ-uniq {M = M} {σ' = σ'} p =
    ext (λ _ → σ-uniq {σ' = nt} (reext! p) ηₚ _)
    where
      nt : Ext => M
      nt .η = σ' .η
      nt .is-natural x y f = ap (_ C.∘_) (Ext .F-id) ∙ σ' .is-natural x y f

  open is-colimit has-colimit public
```


# Uniqueness

[Much like limits], colimits are unique up to isomorphism. This all
follows from general properties of Kan extensions, combined with the
fact that natural isomorphisms between functors $\top \to \cC$
correspond with isomorphisms in $\cC$.

[Much like limits]: Cat.Diagram.Limit.Base.html#uniqueness

<!--
```agda
module _ {o₁ h₁ o₂ h₂ : _} {J : Precategory o₁ h₁} {C : Precategory o₂ h₂}
         {Diagram : Functor J C}
         {x y} {etay : Diagram => Const y} {etax : Diagram => Const x}
         (Cy : is-colimit Diagram y etay)
         (Cx : is-colimit Diagram x etax)
       where
  private
    module J = Precategory J
    module C = Cat.Reasoning C
    module Diagram = Functor Diagram
    open is-lan
    open _=>_

    module Cy = is-colimit Cy
    module Cx = is-colimit Cx
```
-->

```agda
  colimits→inversesp
    : ∀ {f : C.Hom x y} {g : C.Hom y x}
    → (∀ {j : J.Ob} → f C.∘ Cx.ψ j ≡ Cy.ψ j)
    → (∀ {j : J.Ob} → g C.∘ Cy.ψ j ≡ Cx.ψ j)
    → C.Inverses f g

  colimits→invertiblep
    : ∀ {f : C.Hom x y}
    → (∀ {j : J.Ob} → f C.∘ Cx.ψ j ≡ Cy.ψ j)
    → C.is-invertible f

  colimits-unique     : x C.≅ y
  colimits→invertible : C.is-invertible (Cx.universal Cy.ψ Cy.commutes)
  colimits→inverses
    : C.Inverses (Cx.universal Cy.ψ Cy.commutes) (Cy.universal Cx.ψ Cx.commutes)
```

<!--
```agda
  colimits→inversesp {f = f} {g = g} f-factor g-factor =
    inversesⁿ→inverses {α = !constⁿ f} {β = !constⁿ g}
      (Lan-unique.σ-inversesp Cx Cy
        (ext λ j → f-factor {j})
        (ext λ j → g-factor {j}))
      tt

  colimits→invertiblep {f = f} f-factor =
    is-invertibleⁿ→is-invertible {α = !constⁿ f}
      (Lan-unique.σ-is-invertiblep
        Cx Cy (ext λ j → f-factor {j}))
      tt

  colimits→inverses =
    colimits→inversesp (Cx.factors Cy.ψ Cy.commutes) (Cy.factors Cx.ψ Cx.commutes)

  colimits→invertible =
    colimits→invertiblep (Cx.factors Cy.ψ Cy.commutes)

  colimits-unique = isoⁿ→iso (Lan-unique.unique Cx Cy) tt
```
-->

Furthermore, if the universal map is invertible, then that means its
domain is _also_ a colimit of the diagram. This also follows from a
[general theorem of Kan extensions], though some golfing is required to
obtain the correct inverse definitionally.

[general theorem of Kan extensions]: Cat.Functor.Kan.Unique.html#is-invertible→is-lan

<!--
```agda
module _ {o₁ h₁ o₂ h₂ : _} {J : Precategory o₁ h₁} {C : Precategory o₂ h₂}
         {D : Functor J C} {K : Functor ⊤Cat C}
         {etay : D => Const (Functor.F₀ K tt)}
         (Cy : is-colimit D (Functor.F₀ K tt) etay)
       where
  private
    module J = Precategory J
    module C = Cat.Reasoning C
    module D = Functor D
    open Functor
    open _=>_

    module Cy = is-colimit Cy

  family→cocone
    : ∀ {x}
    → (eta : ∀ j → C.Hom (D.₀ j) x)
    → (∀ {x y} (f : J.Hom x y) → eta y C.∘ D.₁ f ≡ eta x)
    → D => Const x
  family→cocone eta p .η = eta
  family→cocone eta p .is-natural _ _ _ = p _ ∙ sym (C.idl _)
```
-->

```agda
  is-invertible→is-colimitp
    : ∀ {K' : Functor ⊤Cat C} {eta : D => K' F∘ !F}
    → (eta' : ∀ j → C.Hom (D.₀ j) (K' .F₀ tt))
    → (p : ∀ {x y} (f : J.Hom x y) → eta' y C.∘ D.₁ f ≡ eta' x)
    → (∀ {j} → eta' j ≡ eta .η j)
    → C.is-invertible (Cy.universal eta' p)
    → is-lan !F D K' eta
  is-invertible→is-colimitp {K' = K'} {eta = eta} eta' p q invert =
    generalize-colimitp
      (is-invertible→is-lan Cy $ invertible→invertibleⁿ _ λ _ → invert)
      q
```

Another useful fact is that if $C$ is a colimit of some diagram $Dia$,
and $Dia$ is naturally isomorphic to some other diagram $Dia'$, then the
coapex of $C$ is also a colimit of $Dia'$.

```agda
  natural-iso-diagram→is-colimitp
    : ∀ {D' : Functor J C} {eta : D' => K F∘ !F}
    → (isos : D ≅ⁿ D')
    → (∀ {j} →  Cy.ψ j C.∘ Isoⁿ.from isos .η j ≡ eta .η j)
    → is-lan !F D' K eta
  natural-iso-diagram→is-colimitp {D' = D'} isos q = generalize-colimitp
    (natural-iso-of→is-lan Cy isos)
    q
```

<!--
```agda
module _ {o₁ h₁ o₂ h₂ : _} {J : Precategory o₁ h₁} {C : Precategory o₂ h₂}
         {D D' : Functor J C} where
  natural-iso→colimit
    : D ≅ⁿ D' → Colimit D → Colimit D'
  natural-iso→colimit isos C .Lan.Ext = Lan.Ext C
  natural-iso→colimit isos C .Lan.eta = Lan.eta C ∘nt Isoⁿ.from isos
  natural-iso→colimit isos C .Lan.has-lan = natural-iso-of→is-lan (Lan.has-lan C) isos
```
-->

<!--
```agda
module _ {o₁ h₁ o₂ h₂ : _} {J : Precategory o₁ h₁} {C : Precategory o₂ h₂}
         {Diagram : Functor J C}
         {x} {eta : Diagram => Const x}
         where
  private
    module J = Precategory J
    module C = Cat.Reasoning C
    module Diagram = Functor Diagram
    open is-lan
    open _=>_

  is-colimit-is-prop : is-prop (is-colimit Diagram x eta)
  is-colimit-is-prop = is-lan-is-prop
```
-->

Since `is-colimit`{.Agda} is a proposition, and the colimiting cocones
are all unique (“up to isomorphism”), if we're talking about [[univalent
categories]], then `Colimit`{.Agda} _itself_ is a proposition.  This is
also an instance of the more general [uniqueness of Kan extensions].

[uniqueness of Kan extensions]: Cat.Functor.Kan.Unique.html

<!--
```agda
module _ {o₁ h₁ o₂ h₂ : _} {J : Precategory o₁ h₁} {C : Precategory o₂ h₂}
         {Diagram : Functor J C}
         where
```
-->

```agda
  Colimit-is-prop : is-category C → is-prop (Colimit Diagram)
  Colimit-is-prop cat = Lan-is-prop cat
```

# Cocompleteness {defines="cocomplete cocomplete-category"}

A category is **cocomplete** if it admits colimits for diagrams of arbitrary shape.
However, in the presence of excluded middle, if a category admits
coproducts indexed by its class of morphisms, then it is automatically
[thin]. Since excluded middle is independent of type theory, we can not
prove that any non-thin categories have arbitrary colimits.

[thin]: Order.Base.html

Instead, categories are cocomplete _with respect to_ a pair of
universes: A category is **$(o, \ell)$-cocomplete** if it has colimits
for any diagram indexed by a precategory with objects in $\ty\ o$ and
morphisms in $\ty\ \ell$.

```agda
is-cocomplete : ∀ {oc ℓc} o ℓ → Precategory oc ℓc → Type _
is-cocomplete oj ℓj C = ∀ {J : Precategory oj ℓj} (F : Functor J C) → Colimit F
```

While this condition might sound very strong, and thus that it would be hard to come
by, it turns out we can get away with only two fundamental types of colimits:
[[coproducts]] and [[coequalisers]]. In order to construct the colimit for a diagram
of shape $\cJ$, we will require coproducts [[indexed|indexed coproduct]] by $\cJ$'s type
of objects *and* by its type of morphisms.

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  private
    module C = Cat.Reasoning C
    open Indexed-coproduct
    open make-is-colimit
    open Coequaliser
```
-->

```agda
  colimit-as-coequaliser-of-coproduct
    : ∀ {oj ℓj} {J : Precategory oj ℓj}
    → has-coproducts-indexed-by C ⌞ J ⌟
    → has-coproducts-indexed-by C (Arrows J)
    → has-coequalisers C
    → (F : Functor J C) → Colimit F
  colimit-as-coequaliser-of-coproduct {oj} {ℓj} {J} has-Ob-cop has-Arrows-cop has-coeq F =
    to-colimit (to-is-colimit colim) where
```

<!--
```agda
    module J = Cat.Reasoning J
    open Functor F
```
-->

Given a diagram $F : \ca{J} \to \ca{C}$, we start by building the coproduct of all
the objects appearing in the diagram.

```agda
    Obs : Indexed-coproduct C λ o → F₀ o
    Obs = has-Ob-cop _
```

Our colimit will arise as a *quotient object* of this coproduct-of-objects,
namely the [[coequaliser]] of two carefully chosen morphisms.

As a guiding example, the [[pushout]] of $f : C \to A$ and $g : C \to B$ should be
the quotient of $A + B + C$ by the equivalence relation generated by
$\iota_A(f(c)) = \iota_C(c) = \iota_B(g(c))$. In full generality, for
each arrow $f : C \to A$ in our diagram, we should have that injecting
into the $C$th component of our coproduct should give the same
result as precomposing with $f$ and injecting into the $A$th component.

This suggests to build another indexed coproduct of all the *domains* of arrows in
the diagram, taking the first morphism to be the injection into the domain component
and the second morphism to be the injection into the codomain component precomposed with $f$:

~~~{.quiver}
\[\begin{tikzcd}
	{\displaystyle \coprod_{(f : a \to b) : \text{Arrows}(\mathcal J)} F(a)} & {\displaystyle \coprod_{o : \text{Ob}(\mathcal J)} F(o)}
	\arrow["{\iota_a}", shift left, from=1-1, to=1-2]
	\arrow["{\iota_b \circ F(f)}"', shift right, from=1-1, to=1-2]
\end{tikzcd}\]
~~~

```agda
    Dom : Indexed-coproduct C {Idx = Arrows J} λ (a , b , f) → F₀ a
    Dom = has-Arrows-cop _

    s t : C.Hom (Dom .ΣF) (Obs .ΣF)
    s = Dom .match λ (a , b , f) → Obs .ι b C.∘ F₁ f
    t = Dom .match λ (a , b , f) → Obs .ι a

    coequ : Coequaliser C s t
    coequ = has-coeq _ _

    colim : make-is-colimit F (coequ .coapex)
```

<details>
<summary>
The rest of the proof amounts to repackaging the data of the coequaliser and coproducts
as the data for a colimit.
</summary>

```agda
    colim .ψ c = coequ .coeq C.∘ Obs .ι c
    colim .commutes {a} {b} f =
      (coequ .coeq C.∘ Obs .ι b) C.∘ F₁ f          ≡˘⟨ C.extendr (Dom .commute) ⟩
      ⌜ coequ .coeq C.∘ s ⌝ C.∘ Dom .ι (a , b , f) ≡⟨ ap! (coequ .coequal) ⟩
      (coequ .coeq C.∘ t) C.∘ Dom .ι (a , b , f)   ≡⟨ C.pullr (Dom .commute) ⟩
      coequ .coeq C.∘ Obs .ι a                     ∎
    colim .universal {x} e comm = coequ .universal comm' where
      e' : C.Hom (Obs .ΣF) x
      e' = Obs .match e
      comm' : e' C.∘ s ≡ e' C.∘ t
      comm' = Indexed-coproduct.unique₂ Dom λ i@(a , b , f) →
        (e' C.∘ s) C.∘ Dom .ι i      ≡⟨ C.extendr (Dom .commute) ⟩
        ⌜ e' C.∘ Obs .ι b ⌝ C.∘ F₁ f ≡⟨ ap! (Obs .commute) ⟩
        e b C.∘ F₁ f                 ≡⟨ comm f ⟩
        e a                          ≡˘⟨ Obs .commute ⟩
        e' C.∘ Obs .ι a              ≡˘⟨ C.pullr (Dom .commute) ⟩
        (e' C.∘ t) C.∘ Dom .ι i      ∎
    colim .factors {j} e comm =
      colim .universal e comm C.∘ (coequ .coeq C.∘ Obs .ι j) ≡⟨ C.pulll (coequ .factors) ⟩
      Obs .match e C.∘ Obs .ι j                              ≡⟨ Obs .commute ⟩
      e j                                                    ∎
    colim .unique e comm u' fac = coequ .unique $ Obs .unique _
      λ i → sym (C.assoc _ _ _) ∙ fac i
```
</details>

This implies that a category with coequalisers and large enough indexed coproducts has
all colimits.

```agda
  coproducts+coequalisers→cocomplete
    : ∀ {oj ℓj}
    → has-indexed-coproducts C (oj ⊔ ℓj)
    → has-coequalisers C
    → is-cocomplete oj ℓj C
  coproducts+coequalisers→cocomplete {oj} {ℓj} has-cop has-coeq =
    colimit-as-coequaliser-of-coproduct
      (λ _ → Lift-Indexed-coproduct C ℓj (has-cop _))
      (λ _ → has-cop _)
      has-coeq
```

# Preservation and reflection of colimits {defines="preserved-colimit preserves-colimits reflected-colimit reflects-colimits"}

The definitions here are the same idea as [[preservation of
limits|preserved limit]], just dualised.

<!--
```agda
module _ {J : Precategory o₁ h₁} {C : Precategory o₂ h₂} {D : Precategory o₃ h₃}
         (F : Functor C D) (Diagram : Functor J C) where
```
-->

```agda
  preserves-colimit : Type _
  preserves-colimit = preserves-lan !F Diagram F

  reflects-colimit : Type _
  reflects-colimit = reflects-lan !F Diagram F
```

<!--
```agda
module preserves-colimit
  {J : Precategory o₁ h₁} {C : Precategory o₂ h₂} {D : Precategory o₃ h₃}
  {F : Functor C D} {Dia : Functor J C}
  (preserves : preserves-colimit F Dia)

  where
  private
    module D = Precategory D
    module C = Precategory C
    module J = Precategory J
    module F = Func F
    module Dia = Func Dia

  universal
    : {x : C.Ob}
    → {K : Functor ⊤Cat C} {eta : Dia => K F∘ !F}
    → {eta' : (j : J.Ob) → C.Hom (Dia.F₀ j) x}
    → {p : ∀ {i j} (f : J.Hom i j) → eta' j C.∘ Dia.F₁ f ≡ eta' i}
    → (colim : is-lan !F Dia K eta)
    → F.F₁ (is-colimit.universal colim eta' p) ≡ is-colimit.universal (preserves colim) (λ j → F.F₁ (eta' j)) (λ f → F.collapse (p f))
  universal colim =
    is-colimit.unique (preserves colim) _ _ _
      (λ j → F.collapse (is-colimit.factors colim _ _))

  colimit : Colimit Dia → Colimit (F F∘ Dia)
  colimit colim = to-colimit (preserves (Colimit.has-colimit colim))

module _ {J : Precategory o₁ h₁} {C : Precategory o₂ h₂} {D : Precategory o₃ h₃}
         {F F' : Functor C D} {Dia : Functor J C} where

  private
    module D = Cat.Reasoning D
    open Func
    open _=>_

  natural-iso→preserves-colimits
    : F ≅ⁿ F'
    → preserves-colimit F Dia
    → preserves-colimit F' Dia
  natural-iso→preserves-colimits α F-preserves {G = K} {eta} colim =
    natural-isos→is-lan idni (α ◂ni Dia) (α ◂ni K)
      (ext λ j →
        ⌜ F' .F₁ (K .F₁ tt) D.∘ α.to .η _ ⌝ D.∘ (F .F₁ (eta .η j) D.∘ α.from .η _) ≡⟨ ap! (eliml F' (K .F-id)) ⟩
        α.to .η _ D.∘ (F .F₁ (eta .η j) D.∘ α.from .η _)                           ≡⟨ D.pushr (sym (α.from .is-natural _ _ _)) ⟩
        ((α.to .η _ D.∘ α.from .η _) D.∘ F' .F₁ (eta .η j))                        ≡⟨ D.eliml (α.invl ηₚ _) ⟩
        F' .F₁ (eta .η j) ∎)
      (F-preserves colim)
    where
      module α = Isoⁿ α
```
-->

## Cocontinuity {defines="cocontinuous"}

```agda
is-cocontinuous
  : ∀ (oshape hshape : Level)
      {C : Precategory o₁ h₁}
      {D : Precategory o₂ h₂}
  → Functor C D → Type _
```

A cocontinuous functor is one that, for every shape of diagram `J`,
and every diagram `diagram`{.Agda} of shape `J` in `C`, preserves the
colimit for that diagram.

```agda
is-cocontinuous oshape hshape {C = C} F =
  ∀ {J : Precategory oshape hshape} {Diagram : Functor J C}
  → preserves-colimit F Diagram
```

## Lifting and creation of colimits {defines="lifted-colimit lifts-colimits created-colimit creates-colimits"}

**Lifted colimits** and **created colimits** dualise the notions of
[[lifted limits]] and [[created limits]]; see there for definitions and
explanations.

<!--
```agda
module _ {J : Precategory o₁ h₁} {C : Precategory o₂ h₂} {D : Precategory o₃ h₃}
         (F : Functor C D) {Diagram : Functor J C} where
```
-->

```agda
  record lifts-colimit (colim : Colimit (F F∘ Diagram)) : Type (o₁ ⊔ h₁ ⊔ o₂ ⊔ h₂ ⊔ o₃ ⊔ h₃) where
    no-eta-equality
    field
      lifted : Colimit Diagram
      preserved : preserves-is-lan F (Colimit.has-lan lifted)

    lifts→preserves-colimit : preserves-colimit F Diagram
    lifts→preserves-colimit = preserves-is-lan→preserves-lan F
      (Colimit.has-lan lifted) preserved
```

<!--
```agda
module _ {J : Precategory o₁ h₁} {C : Precategory o₂ h₂} {D : Precategory o₃ h₃}
         (F : Functor C D) (Diagram : Functor J C) where
```
-->

```agda
  record creates-colimit : Type (o₁ ⊔ h₁ ⊔ o₂ ⊔ h₂ ⊔ o₃ ⊔ h₃) where
    no-eta-equality
    field
      has-lifts-colimit : (colim : Colimit (F F∘ Diagram)) → lifts-colimit F colim
      reflects : reflects-colimit F Diagram
```

<!--
```agda
module _ (J : Precategory o₁ h₁) {C : Precategory o₂ h₂} {D : Precategory o₃ h₃}
         (F : Functor C D) where
```
-->

```agda
  lifts-colimits-of : Type _
  lifts-colimits-of =
    ∀ {Diagram : Functor J C} (colim : Colimit (F F∘ Diagram))
    → lifts-colimit F colim

  creates-colimits-of : Type _
  creates-colimits-of =
    ∀ {Diagram : Functor J C}
    → creates-colimit F Diagram
```

<!--
```agda
module _ {C : Precategory o₂ h₂} {D : Precategory o₃ h₃} (F : Functor C D) where
```
-->

```agda
  lifts-colimits→cocomplete
    : ∀ {oj ℓj}
    → (∀ {J : Precategory oj ℓj} → lifts-colimits-of J F)
    → is-cocomplete oj ℓj D
    → is-cocomplete oj ℓj C
  lifts-colimits→cocomplete lifts dcomp Diagram =
    lifts (dcomp (F F∘ Diagram)) .lifts-colimit.lifted
```

## Stability under composition

<!--
```agda
module _ {C : Precategory o₂ h₂} {D : Precategory o₃ h₃} {E : Precategory o₄ h₄}
         {F : Functor C D} {G : Functor D E} where
  open lifts-colimit
  open creates-colimit

  private
    fixup
      : ∀ {oj ℓj} {J : Precategory oj ℓj} {Diagram : Functor J C}
      → {K : Functor ⊤Cat C} {eta : Diagram => K F∘ !F}
      → is-lan !F (G F∘ F F∘ Diagram) (G F∘ F F∘ K) (nat-assoc-to (G ▸ nat-assoc-to (F ▸ eta)))
      ≃ is-lan !F ((G F∘ F) F∘ Diagram) ((G F∘ F) F∘ K) (nat-assoc-to ((G F∘ F) ▸ eta))
    fixup = trivial-lan-equiv!
```
-->

```agda
  F∘-preserves-colimits
    : ∀ {oj ℓj} {J : Precategory oj ℓj} {Diagram : Functor J C}
    → preserves-colimit F Diagram
    → preserves-colimit G (F F∘ Diagram)
    → preserves-colimit (G F∘ F) Diagram
  F∘-preserves-colimits F-preserves G-preserves =
    Equiv.to fixup ⊙ G-preserves ⊙ F-preserves

  F∘-reflects-colimits
    : ∀ {oj ℓj} {J : Precategory oj ℓj} {Diagram : Functor J C}
    → reflects-colimit F Diagram
    → reflects-colimit G (F F∘ Diagram)
    → reflects-colimit (G F∘ F) Diagram
  F∘-reflects-colimits F-reflects G-reflects =
    F-reflects ⊙ G-reflects ⊙ Equiv.from fixup

  F∘-lifts-colimits
    : ∀ {oj ℓj} {J : Precategory oj ℓj}
    → lifts-colimits-of J F
    → lifts-colimits-of J G
    → lifts-colimits-of J (G F∘ F)
  F∘-lifts-colimits F-lifts G-lifts colim = λ where
      .lifted → colim''
      .preserved → F∘-preserves-colimits
        (lifts→preserves-colimit lifted-colim')
        (lifts→preserves-colimit lifted-colim)
        (Lan.has-lan colim'')
    where
      lifted-colim = G-lifts (natural-iso→colimit (ni-assoc ni⁻¹) colim)
      colim' = lifted-colim .lifted
      lifted-colim' = F-lifts colim'
      colim'' = lifted-colim' .lifted

  F∘-creates-colimits
    : ∀ {oj ℓj} {J : Precategory oj ℓj}
    → creates-colimits-of J F
    → creates-colimits-of J G
    → creates-colimits-of J (G F∘ F)
  F∘-creates-colimits F-creates G-creates .has-lifts-colimit =
    F∘-lifts-colimits (F-creates .has-lifts-colimit) (G-creates .has-lifts-colimit)
  F∘-creates-colimits F-creates G-creates .reflects =
    F∘-reflects-colimits (F-creates .reflects) (G-creates .reflects)
```
