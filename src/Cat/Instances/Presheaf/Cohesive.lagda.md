<!--
```agda
open import Cat.Functor.Adjoint.Hom
open import Cat.Diagram.Terminal
open import Cat.Functor.Adjoint
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning

open Precategory
open Functor
open _=>_
```
-->

```agda
module Cat.Instances.Presheaf.Cohesive
  {ℓ} (C : Precategory ℓ ℓ) (top : Terminal C)
  where
```

<!--
```agda
private
  module C = Cat.Reasoning C
  module PSh = Cat.Reasoning (PSh ℓ C)

open Terminal top renaming (top to pt)
```
-->

# Cohesion of a gros topos {defines="cohesive-topos gros-topos"}

What distinguishes a **gros** topos — a topos of generalized *spaces*,
like the smooth sets of physics, probed by a whole category of shapes
— from a *petit* topos of sheaves on a single fixed space is its
relation to the base topos of sets: for the gros case the
"underlying set of points" functor $\Gamma$ extends to an adjoint
tower

$$
\Pi_0 \dashv \rm{Disc} \dashv \Gamma \dashv \rm{Codisc}
$$

relating every space to the discrete and codiscrete spaces on its
points, and to its set of connected components. This is Lawvere's
axiomatisation of *cohesion*, and it is what lets a topos distinguish
a space from its point-set skeleton: a smooth set generally has far
fewer *points* than *plots*.

We construct the tower constructively, for the presheaf topos on any
category $\cC$ of probes having a terminal probe $\rm{pt}$ — for
smooth sets, the point $\bR^0$.

**Global sections.** The points of a presheaf are its plots of the
terminal shape:

```agda
Γ : Functor (PSh ℓ C) (Sets ℓ)
Γ .F₀ X = X .F₀ pt
Γ .F₁ α = α .η pt
Γ .F-id = refl
Γ .F-∘ f g = refl
```

**Discrete spaces.** A set $A$ becomes a space in which a plot sees
nothing but the point it lands on: every shape of plot is constantly
$A$.

```agda
Disc : Functor (Sets ℓ) (PSh ℓ C)
Disc .F₀ A .F₀ _ = A
Disc .F₀ A .F₁ _ x = x
Disc .F₀ A .F-id = refl
Disc .F₀ A .F-∘ _ _ = refl
Disc .F₁ f .η _ = f
Disc .F₁ f .is-natural _ _ _ = refl
Disc .F-id = trivial!
Disc .F-∘ f g = trivial!
```

**Codiscrete spaces.** Dually, a set $A$ becomes the space whose
plots of shape $U$ are *arbitrary* assignments of elements of $A$ to
the points of $U$ — no cohesion between them at all.

```agda
Codisc : Functor (Sets ℓ) (PSh ℓ C)
Codisc .F₀ A .F₀ U = el! (C.Hom pt U → ∣ A ∣)
Codisc .F₀ A .F₁ f g p = g (f C.∘ p)
Codisc .F₀ A .F-id = ext λ g p → ap g (C.idl p)
Codisc .F₀ A .F-∘ f g = ext λ h p → ap h (sym (C.assoc _ _ _))
Codisc .F₁ f .η U g p = f (g p)
Codisc .F₁ f .is-natural _ _ _ = refl
Codisc .F-id = trivial!
Codisc .F-∘ f g = trivial!
```

**Connected components.** In the other direction, a space has a set
of pieces: the quotient of all its plots, of every shape, by the
relation identifying a plot with any of its restrictions. Two points
land in the same piece exactly if some probe connects them.

```agda
Π₀ : Functor (PSh ℓ C) (Sets ℓ)
Π₀ .F₀ X = el! (Coeq {A = R X} (fst ⊙ fst) (snd ⊙ fst)) where
  R : ⌞ PSh ℓ C ⌟ → Type ℓ
  R X = Σ[ p ∈ (Σ[ U ∈ C ] ∣ X .F₀ U ∣) × (Σ[ V ∈ C ] ∣ X .F₀ V ∣) ]
        (Σ[ f ∈ C.Hom (p .fst .fst) (p .snd .fst) ]
         (X .F₁ f (p .snd .snd) ≡ p .fst .snd))
Π₀ .F₁ {X} {Y} α = Coeq-rec (λ (U , x) → inc (U , α .η U x)) λ where
  (((U , x) , (V , y)) , f , p) → glue
    ( ((U , α .η U x) , (V , α .η V y))
    , f
    , sym (happly (α .is-natural V U f) y) ∙ ap (α .η U) p
    )
Π₀ .F-id {X} = ext λ _ _ → refl
Π₀ .F-∘ f g = ext λ _ _ → refl
```

## The adjunctions

Maps out of a discrete space are exactly maps out of its set:
$\rm{Disc} \dashv \Gamma$.

```agda
Disc⊣Γ : Disc ⊣ Γ
Disc⊣Γ ._⊣_.unit .η A a = a
Disc⊣Γ ._⊣_.unit .is-natural A B f = refl
Disc⊣Γ ._⊣_.counit .η X .η U x = X .F₁ ! x
Disc⊣Γ ._⊣_.counit .η X .is-natural V U f = ext λ x →
    ap (λ e → X .F₁ e x) (!-unique (! C.∘ f))
  ∙ happly (X .F-∘ f !) x
Disc⊣Γ ._⊣_.counit .is-natural X Y h = ext λ U x →
  sym (happly (h .is-natural pt U !) x)
Disc⊣Γ ._⊣_.zig {A} = ext λ U a → refl
Disc⊣Γ ._⊣_.zag {X} = ext λ x →
  ap (λ e → X .F₁ e x) (!-unique C.id) ∙ happly (X .F-id) x
```

Maps into a codiscrete space are exactly maps out of the points:
$\Gamma \dashv \rm{Codisc}$.

```agda
Γ⊣Codisc : Γ ⊣ Codisc
Γ⊣Codisc = record
  { unit = u ; counit = c ; zig = λ {X} → zig' {X} ; zag = λ {A} → zag' {A} }
  where
  u : Id => (Codisc F∘ Γ)
  u .η X .η U x p = X .F₁ p x
  u .η X .is-natural V U f = ext λ x p →
    sym (happly (X .F-∘ p f) x)
  u .is-natural X Y h = ext λ U x p →
    sym (happly (h .is-natural U pt p) x)

  c : (Γ F∘ Codisc) => Id
  c .η A g = g C.id
  c .is-natural A B f = refl

  zig' : ∀ {X} → c .η (Γ .F₀ X) ⊙ Γ .F₁ (u .η X) ≡ (λ x → x)
  zig' {X} = ext λ x → happly (X .F-id) x

  zag' : ∀ {A} → Codisc .F₁ (c .η A) PSh.∘ u .η (Codisc .F₀ A) ≡ PSh.id
  zag' {A} = ext λ U g p → ap g (C.idr p)
```

And maps out of the pieces of a space are exactly maps into a
discrete space: $\Pi_0 \dashv \rm{Disc}$.

```agda
Π₀⊣Disc : Π₀ ⊣ Disc
Π₀⊣Disc ._⊣_.unit .η X .η U x = inc (U , x)
Π₀⊣Disc ._⊣_.unit .η X .is-natural V U f = ext λ y →
  glue (((U , X .F₁ f y) , (V , y)) , f , refl)
Π₀⊣Disc ._⊣_.unit .is-natural X Y h = ext λ U x → refl
Π₀⊣Disc ._⊣_.counit .η A = Coeq-rec snd λ where
  ((_ , _) , f , p) → sym p
Π₀⊣Disc ._⊣_.counit .is-natural A B f = ext λ U a → refl
Π₀⊣Disc ._⊣_.zig {X} = ext λ U x → refl
Π₀⊣Disc ._⊣_.zag {A} = ext λ U a → refl
```

## Cohesion

The composite $\Gamma \circ \rm{Disc}$ is the identity on the nose —
the points of a discrete space are the original set — and, because
the site has a terminal probe (in particular, is connected), so is
the composite $\Pi_0 \circ \rm{Disc}$: a discrete space has one piece
per point. It is this last equivalence that fails for a petit topos,
and that makes the presheaf topos over probes a topos of *cohesive
spaces*.

```agda
Γ-Disc-path : ∀ (A : Set ℓ) → Γ .F₀ (Disc .F₀ A) ≡ A
Γ-Disc-path A = refl

Π₀-Disc : ∀ (A : Set ℓ) → ∣ Π₀ .F₀ (Disc .F₀ A) ∣ ≃ ∣ A ∣
Π₀-Disc A = Iso→Equiv (to , iso from ri li) where
  to : ∣ Π₀ .F₀ (Disc .F₀ A) ∣ → ∣ A ∣
  to = Coeq-rec snd λ where ((_ , _) , f , p) → sym p

  from : ∣ A ∣ → ∣ Π₀ .F₀ (Disc .F₀ A) ∣
  from a = inc (pt , a)

  ri : is-right-inverse from to
  ri a = refl

  li : is-left-inverse from to
  li = Coeq-elim-prop (λ _ → hlevel 1) λ (U , a) →
    sym (glue (((U , a) , (pt , a)) , ! , refl))
```

For the topos of *sheaves* on a site with a terminal probe the same
tower exists whenever discrete and codiscrete presheaves are sheaves
— true for the coverages of interest in physics, but requiring the
coverage as extra input; we leave this refinement for future work.
