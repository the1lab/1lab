```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.Kan.Unique
open import Cat.Functor.Coherence
open import Cat.Instances.Functor
open import Cat.Functor.Kan.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning

module Cat.Diagram.Colimit.Base where
```

<!--
```agda
private variable
  o ℓ o′ ℓ′ : Level
```
-->

# Idea

Colimits are dual to limits [limit]; much like their cousins, they
generalize constructions in several settings to arbitrary categories.
A colimit (if it exists), is the "best solution" to an
"identification problem". This is in contrast to the limit, which
acts as a solution to an "equational problem".

[limit]: Cat.Diagram.Limit.Base.html

We define colimits in a similar way to limits; the only difference being
that we define a colimits of a diagram $F$ as left [kan extensions]
instead of right [kan extensions]. This gives us the expected
"mapping out" universal property, as opposed to the "mapping in" property
associated to limits.

[kan extensions]: Cat.Functor.Kan.Base.html

Note that approach to colimits is not what normally presented in
introductory material. Instead, most books opt to define colimits
via [cocones], as they are less abstract, though harder to work with
in the long run.

[cocones]: Cat.Diagram.Colimit.Cocone.html

<!--
```agda
private variable
  o₁ o₂ o₃ h₁ h₂ h₃ : Level
```
-->

```agda
module _ {J : Precategory o₁ h₁} {C : Precategory o₂ h₂} (Diagram : Functor J C) where
  private
    module C = Precategory C

  cocone→unit : ∀ {x : C.Ob} → (Diagram => Const x) → Diagram => const! x F∘ !F
  unquoteDef cocone→unit = define-coherence cocone→unit

  is-colimit : (x : C.Ob) → Diagram => Const x → Type _
  is-colimit x cocone =
    is-lan !F Diagram (const! x) (cocone→unit cocone)

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
-->A

First, we require morphisms from the every value of the diagram to
the coapex; taken as a family, we call it $\phi$. Moreover, if $f : x \to y$ is
a morphism in the "shape" category $\cJ$, we require $\psi y \circ Ff = \psi x$,
which encodes the relevant naturality.

```agda
    field
      ψ : (j : J.Ob) → C.Hom (F₀ j) coapex
      commutes : ∀ {x y} (f : J.Hom x y) → ψ y C.∘ F₁ f ≡ ψ x
```

The rest of the data ensures that $\psi$ is the universal family
of maps with this property; if $\eps_j : Fj \to x$ is another natural
family, then each $\eps_j$ factors through the coapex by a _unique_
universal morphism:

```agda
      universal
        : ∀ {x : C.Ob}
        → (eps : ∀ j → C.Hom (F₀ j) x)
        → (∀ {x y} (f : J.Hom x y) → eps y C.∘ F₁ f ≡ eps x)
        → C.Hom coapex x
      factors
        : ∀ {j : J.Ob} {x : C.Ob}
        → (eps : ∀ j → C.Hom (F₀ j) x)
        → (p : ∀ {x y} (f : J.Hom x y) → eps y C.∘ F₁ f ≡ eps x)
        → universal eps p C.∘ ψ j ≡ eps j
      unique
        : ∀ {x : C.Ob}
        → (eps : ∀ j → C.Hom (F₀ j) x)
        → (p : ∀ {x y} (f : J.Hom x y) → eps y C.∘ F₁ f ≡ eps x)
        → (other : C.Hom coapex x)
        → (∀ j → other C.∘ ψ j ≡ eps j)
        → other ≡ universal eps p

    unique₂
      : ∀ {x : C.Ob}
      → (eps : ∀ j → C.Hom (F₀ j) x)
      → (p : ∀ {x y} (f : J.Hom x y) → eps y C.∘ F₁ f ≡ eps x)
      → ∀ {o1} → (∀ j → o1 C.∘ ψ j ≡ eps j)
      → ∀ {o2} → (∀ j → o2 C.∘ ψ j ≡ eps j)
      → o1 ≡ o2
    unique₂ eps p q r = unique eps p _ q ∙ sym (unique eps p _ r)
```

Once we have this data, we can use it to construct a value of
`is-colimit`{.Agda}. The naturality condition we required above may
seem too weak, but the full naturality condition can be derived from
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
    open _=>_

    colim : is-colimit Diagram coapex (to-cocone mkcolim)
    colim .σ {M = M} α .η _ =
      universal (α .η) (λ f → α .is-natural _ _ f ∙ C.eliml (M .F-id))
    colim .σ {M = M} α .is-natural _ _ _ =
       C.idr _ ∙ C.introl (M .F-id)
    colim .σ-comm {α = α} = Nat-path λ j →
      factors (α .η) _
    colim .σ-uniq {α = α} {σ′ = σ′} p = Nat-path λ _ →
      sym $ unique (α .η) _ (σ′ .η _) (λ j → sym (p ηₚ j))
```

<!--
```agda
  to-is-colimitp
    : ∀ {D : Functor J C} {K : Functor ⊤Cat C} {eta : D => K F∘ !F}
    → (mk : make-is-colimit D (Functor.F₀ K tt))
    → (∀ {j} → to-cocone mk .η j ≡ eta .η j)
    → is-lan !F D K eta
  to-is-colimitp {D} {K} {eta} mkcolim p = colim where
    open make-is-colimit mkcolim
    open is-lan
    open Functor
    open _=>_

    colim : is-lan !F D K eta
    colim .σ {M = M} β .η _ =
      universal (β .η) (λ f → β .is-natural _ _ f ∙ C.eliml (M .F-id))
    colim .σ {M = M} β .is-natural _ _ _ =
      C.elimr (K .F-id) ∙ C.introl (M .F-id)
    colim .σ-comm {α = α} = Nat-path λ j →
      ap (_ C.∘_) (sym p) ∙ factors (α .η) _
    colim .σ-uniq {α = α} {σ′ = σ′} q = Nat-path λ _ →
      sym $ unique (α .η) _ (σ′ .η tt) λ j →
        ap (_ C.∘_) p ∙ sym (q ηₚ j)
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

    module _ {x} (eps : ∀ j → C.Hom (F₀ j) x)
                 (p : ∀ {x y} (f : J.Hom x y) →  eps y C.∘ F₁ f ≡ eps x)
      where

      eps-nt : D => const! x F∘ !F
      eps-nt .η = eps
      eps-nt .is-natural _ _ f = p f ∙ sym (C.idl _)

      hom : C.Hom coapex x
      hom = σ {M = const! x} eps-nt .η tt

    mc : make-is-colimit D coapex
    mc .ψ = eta.η
    mc .commutes f = eta.is-natural _ _ f ∙ C.eliml (Functor.F-id F)
    mc .universal = hom
    mc .factors e p = σ-comm {α = eps-nt e p} ηₚ _
    mc .unique {x = x} eta p other q =
      sym $ σ-uniq {σ′ = other-nt} (Nat-path λ j → sym (q j)) ηₚ tt
      where
        other-nt : F => const! x
        other-nt .η _ = other
        other-nt .is-natural _ _ _ = C.elimr (Functor.F-id F) ∙ sym (C.idl _)
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
    open Lan L
    open Functor
    open _=>_
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
  has-colimit .is-lan.σ-comm =
    Nat-path (λ _ → σ-comm ηₚ _)
  has-colimit .is-lan.σ-uniq {M = M} {σ′ = σ′} p =
    Nat-path (λ _ → σ-uniq {σ′ = nt} (Nat-path (λ j → p ηₚ j)) ηₚ _)
    where
      nt : Ext => M
      nt .η = σ′ .η
      nt .is-natural x y f = ap (_ C.∘_) (Ext .F-id) ∙ σ′ .is-natural x y f

  open is-colimit has-colimit public
```


# Uniqueness

[Much like limits], colimits are unique up to isomorphism.

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
  colimits→inversesp f-factor g-factor =
    C.make-inverses
      (Cy.unique₂ Cy.ψ Cy.commutes (λ j → C.pullr g-factor ∙ f-factor) λ _ → C.idl _)
      (Cx.unique₂ Cx.ψ Cx.commutes (λ j → C.pullr f-factor ∙ g-factor) λ _ → C.idl _)

  colimits→invertiblep
    : ∀ {f : C.Hom x y}
    → (∀ {j : J.Ob} → f C.∘ Cx.ψ j ≡ Cy.ψ j)
    → C.is-invertible f
  colimits→invertiblep f-factor =
    C.inverses→invertible $
    colimits→inversesp f-factor (Cy.factors Cx.ψ Cx.commutes)

  colimits→inverses
    : C.Inverses (Cx.universal Cy.ψ Cy.commutes) (Cy.universal Cx.ψ Cx.commutes)
  colimits→inverses =
    colimits→inversesp (Cx.factors Cy.ψ Cy.commutes) (Cy.factors Cx.ψ Cx.commutes)

  colimits→invertible
    : C.is-invertible (Cx.universal Cy.ψ Cy.commutes)
  colimits→invertible = colimits→invertiblep (Cx.factors Cy.ψ Cy.commutes)

  colimits-unique : x C.≅ y
  colimits-unique = C.invertible→iso _ colimits→invertible
```

Furthermore, if the universal map is invertible, then that means its
domain is _also_ a colimit of the diagram.

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
    open is-ran
    open Functor
    open _=>_

    module Cy = is-colimit Cy

  family→cocone
    : ∀ {x}
    → (eps : ∀ j → C.Hom (D.₀ j) x)
    → (∀ {x y} (f : J.Hom x y) → eps y C.∘ D.₁ f ≡ eps x)
    → D => Const x
  family→cocone eta p .η = eta
  family→cocone eta p .is-natural _ _ _ = p _ ∙ sym (C.idl _)
```
-->

```agda
  is-invertible→is-colimitp
    : ∀ {K' : Functor ⊤Cat C} {eta : D => K' F∘ !F}
    → (eps : ∀ j → C.Hom (D.₀ j) (K' .F₀ tt))
    → (p : ∀ {x y} (f : J.Hom x y) → eps y C.∘ D.₁ f ≡ eps x)
    → (∀ {j} → eps j ≡ eta .η j)
    → C.is-invertible (Cy.universal eps p)
    → is-lan !F D K' eta
  is-invertible→is-colimitp {K' = K'} eps p q invert =
    to-is-colimitp colim q
    where
      open C.is-invertible invert
      open make-is-colimit

      colim : make-is-colimit D (K' .F₀ tt)
      colim .ψ = eps
      colim .commutes = p
      colim .universal tau q = Cy.universal tau q C.∘ inv
      colim .factors tau q =
        sym (C.refl⟩∘⟨ Cy.factors eps p)
        ·· C.cancel-inner invr
        ·· Cy.factors tau q
      colim .unique tau q other r =
        C.insertr invl
        ∙ (Cy.unique _ _ _ (λ j → C.pullr (Cy.factors eps p) ∙ r j) C.⟩∘⟨refl)
```

Another useful fact is that if $C$ is a colimit of some diagram $Dia$,
and $Dia$ is naturally isomorphic to some other diagram $Dia'$, then the
coapex of $C$ is also a colimit of $Dia'$.

```agda
  natural-iso→is-colimitp
    : ∀ {D′ : Functor J C} {eta : D′ => K F∘ !F}
    → (isos : natural-iso D D′)
    → (∀ {j} →  Cy.ψ j C.∘ natural-iso.from isos .η j ≡ eta .η j)
    → is-lan !F D′ K eta
  natural-iso→is-colimitp {D′ = D′} isos p = to-is-colimitp colim p where
    open make-is-colimit
    module isos = natural-iso isos

    colim : make-is-colimit D′ (K .F₀ tt)
    colim .ψ j = Cy.ψ j C.∘ isos.from .η _
    colim .commutes f =
      C.pullr (isos.from .is-natural _ _ f)
      ∙ C.pulll (Cy.commutes f)
    colim .universal eps q =
      Cy.universal
        (λ j → eps j C.∘ isos.to .η _)
        (λ f →
          C.pullr (isos.to .is-natural _ _ f)
          ∙ C.pulll (q f))
    colim .factors eta q =
      C.pulll (Cy.factors _ _)
      ∙ C.cancelr (isos.invl ηₚ _)
    colim .unique eta q other r =
      Cy.unique _ _ other λ j →
        ap (other C.∘_) (C.insertr (isos.invr ηₚ _)) ∙ C.pulll (r j)
```

<!--
```agda
module _ {o₁ h₁ o₂ h₂ : _} {J : Precategory o₁ h₁} {C : Precategory o₂ h₂}
         {D D′ : Functor J C}
         where

  natural-iso→colimit
    : natural-iso D D′
    → Colimit D
    → Colimit D′
  natural-iso→colimit isos C .Lan.Ext = Lan.Ext C
  natural-iso→colimit isos C .Lan.eta = Lan.eta C ∘nt natural-iso.from isos
  natural-iso→colimit isos C .Lan.has-lan =
    natural-iso→is-colimitp (Colimit.has-colimit C) isos refl
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

Therefore, if $C$ is a category, then `Coimit`{.Agda} is a proposition!
However, this follows from a much more general result about [uniqueness
of kan extensions].

[uniqueness of kan extensions]: Cat.Functor.Kan.Unique.html

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


# Preservation of Colimits

The definitions here are the same idea as [preservation of limits], just
dualized.

[preservation of limits]: Cat.Diagram.Limit.Base.html#preservation-of-limits

<!--
```agda
module _ {J : Precategory o₁ h₁} {C : Precategory o₂ h₂} {D : Precategory o₃ h₃}
         (F : Functor C D) {Diagram : Functor J C} where
  private
    module D = Precategory D
    module C = Precategory C
    module J = Precategory J
    module F = Func F
```
-->

```agda
  preserves-colimit
     : ∀ {K : Functor ⊤Cat C} {eta : Diagram => K F∘ !F}
     → is-lan !F Diagram K eta
     → Type _
  preserves-colimit colim = preserves-lan F colim

  reflects-colimit
    : ∀ {K : Functor ⊤Cat C} {eps : Diagram => K F∘ !F}
    → is-lan !F (F F∘ Diagram) (F F∘ K) (nat-assoc-to (F ▸ eps))
    → Type _
  reflects-colimit lan = reflects-lan F lan

--   record creates-colimit : Type (o₁ ⊔ h₁ ⊔ o₂ ⊔ h₂ ⊔ o₃ ⊔ h₃) where
--     field
--       preserves-colimit : Preserves-colimit
--       reflects-colimit : Reflects-colimit
```

## Cocontinuity

```agda
is-cocontinuous
  : ∀ {oshape hshape}
      {C : Precategory o₁ h₁}
      {D : Precategory o₂ h₂}
  → Functor C D → Type _
```

A cocontinuous functor is one that --- for every shape of diagram `J`,
and every diagram `diagram`{.Agda} of shape `J` in `C` --- preserves the
colimit for that diagram.

```agda
is-cocontinuous {oshape = oshape} {hshape} {C = C} F =
  ∀ {J : Precategory oshape hshape} {Diagram : Functor J C}
  → ∀ {K : Functor ⊤Cat C} {eta : Diagram => K F∘ !F} 
  → (colim : is-lan !F Diagram K eta)
  → preserves-colimit F colim
```

## Cocompleteness

A category is **cocomplete** if admits for limits of arbitrary shape.
However, in the presence of excluded middle, if a category admits
coproducts indexed by its class of morphisms, then it is automatically
[thin]. Since excluded middle is independent of type theory, we can not
prove that any non-thin categories have arbitrary colimits.

Instead, categories are cocomplete _with respect to_ a pair of
universes: A category is **$(o, \ell)$-cocomplete** if it has colimits
for any diagram indexed by a precategory with objects in $\ty\ o$ and
morphisms in $\ty\ \ell$.

```agda
is-cocomplete : ∀ {oc ℓc} o ℓ → Precategory oc ℓc → Type _
is-cocomplete o ℓ C = ∀ {D : Precategory o ℓ} (F : Functor D C) → Colimit F
```
