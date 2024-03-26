---
description: |
  Free objects, adjoints, and initiality.
---
<!--
```agda
open import Cat.Functor.Subcategory
open import Cat.Functor.Properties
open import Cat.Diagram.Initial
open import Cat.Functor.Adjoint
open import Cat.Instances.Comma
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->
```agda
module Cat.Diagram.Free where
```

# Free objects

<!--
```agda
module _
  {oc ℓc od ℓd}
  {C : Precategory oc ℓc}
  {D : Precategory od ℓd}
  (U : Functor C D)
  where
  private
    module C = Precategory C
    module D = Precategory D
    module U = Functor U
```
-->

One common perspective on [[adjunctions]] describe free constructions:
the right adjoint forgets structure, and the left adjoint freely adds it.
These sorts of adjunctions are so common that we may be tempted to *define*
free constructions as left adjoints. However, this doesn't quite capture
the whole story: there are many situations where a left adjoint does not
exist, yet we can perform a free constructions on *some* objects.
This gives rise to the following definition:

:::{.definition #free-object}

Let $\cC, \cD$ be a pair of categories, and let $U : \cC \to \cD$ be a
functor. A **free object** on $X : \cD$ is an object $A : \cC$ equipped
with a morphism $\eta : \cD(X, U(A))$, satisfying the following universal
proprety:

- For every $B : \cD$ and $f : \cD(X, U(B))$, there exists a unique
  map $\eps : \cC(A, B)$ with $U(\eps) \circ \eta = f$.
:::

```agda
  record is-free-object-on {x : D.Ob} {a : C.Ob} (eta : D.Hom x (U.₀ a)) : Type (oc ⊔ ℓc ⊔ ℓd) where
    field
      eps : ∀ {b} → D.Hom x (U.₀ b) → C.Hom a b
      commute : ∀ {b} {f : D.Hom x (U.₀ b)} → U.₁ (eps f) D.∘ eta ≡ f
      unique
        : ∀ {b} {f : D.Hom x (U.₀ b)}
        → (other : C.Hom a b)
        → U.₁ other D.∘ eta ≡ f
        → other ≡ eps f

    unique₂
      : ∀ {b} {f : D.Hom x (U.₀ b)}
      → (other₁ other₂ : C.Hom a b)
      → U.₁ other₁ D.∘ eta ≡ f
      → U.₁ other₂ D.∘ eta ≡ f
      → other₁ ≡ other₂
    unique₂ other₁ other₂ p q = unique other₁ p ∙ sym (unique other₂ q)

  record Free-object-on (x : D.Ob) : Type (oc ⊔ ℓc ⊔ ℓd) where
    field
      free : C.Ob
      eta : D.Hom x (U.₀ free)
      has-is-free : is-free-object-on eta

    open is-free-object-on has-is-free public
```

<!--
```agda
module _
  {oc ℓc od ℓd}
  {C : Precategory oc ℓc}
  {D : Precategory od ℓd}
  {U : Functor C D}
  where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module U = Cat.Functor.Reasoning U

  open Free-object-on
```
-->

Intuitively, a free object on $X$ is an approximation of a
(potentially non-existent) left adjoint at $X$.

A free object $A : \cC$ on $X : \cD$ induces an equivalence between
$\cD(X, U(B))$ and $\cC(A, B)$. in other words, free objects are
representing objects for the functor $\cD(X,U(-))$.

```agda
  free-object-eps-equiv
    : ∀ {x} (a : Free-object-on U x)
    → ∀ b → is-equiv (a .eps {b})
  free-object-eps-equiv a b .is-eqv f .centre .fst = U.₁ f D.∘ a .eta
  free-object-eps-equiv a b .is-eqv f .centre .snd = sym $ a .unique f refl
  free-object-eps-equiv a b .is-eqv f .paths (g , p) = Σ-prop-path! $
    ap (λ ϕ → U.₁ ϕ D.∘ a .eta) (sym p)
    ∙ a .commute
```

Free objects have all the usual hallmarks of universal constructions:
the universal property of free objects is a proposition, and they are
unique up to isomorphism.

```agda
  is-free-object-on-is-prop
    : ∀ {x a} {eta : D.Hom x (U.₀ a)}
    → is-prop (is-free-object-on U eta)

  free-object-unique : ∀ {x} (a b : Free-object-on U x) → a .free C.≅ b .free
```

<details>
<summary>The proofs follow the usual script for universal constructions,
so we will omit the details.</summary>

```agda
  free-object-unique a b =
    C.make-iso (a .eps (b .eta)) (b .eps (a .eta))
      (unique₂ b _ _ (U.popr (b .commute) ∙ a .commute) (D.eliml U.F-id))
      (unique₂ a _ _ (U.popr (a .commute) ∙ b .commute) (D.eliml U.F-id))

  is-free-object-on-is-prop {x = x} {a = a} {eta = eta} fo fo' = path where
    module fo = is-free-object-on fo
    module fo' = is-free-object-on fo'

    eps-path : ∀ {b} (f : D.Hom x (U.₀ b)) → fo.eps f ≡ fo'.eps f
    eps-path f = fo'.unique (fo.eps f) fo.commute

    path : fo ≡ fo' 
    path i .is-free-object-on.eps f = eps-path f i
    path i .is-free-object-on.commute {f = f} =
      is-prop→pathp (λ i → D.Hom-set _ _ (U.₁ (eps-path f i) D.∘ eta) f)
        fo.commute fo'.commute i
    path i .is-free-object-on.unique {f = f} o p =
      is-prop→pathp (λ i → C.Hom-set _ _ o (eps-path f i))
        (fo.unique o p) (fo'.unique o p) i
```
</details>

<!--
```agda
  private unquoteDecl free-obj-eqv = declare-record-iso free-obj-eqv (quote Free-object-on) 

  -- This lets us ignore 'is-free-object-on' when proving equality.
  Extensional-Free-object-on
    : ∀ {x ℓr}
    → ⦃ sa : Extensional (Σ[ a ∈ C.Ob ] (D.Hom x (U.₀ a))) ℓr ⦄
    → Extensional (Free-object-on U x) ℓr
  Extensional-Free-object-on ⦃ sa ⦄ =
    embedding→extensional
      (Iso→Embedding free-obj-eqv
      ∙emb Equiv→Embedding Σ-assoc
      ∙emb (fst , Subset-proj-embedding λ _ → is-free-object-on-is-prop))
      sa

  instance
    Extensionality-Free-object-on
      : ∀ {X}
      → Extensionality (Free-object-on U X)
    Extensionality-Free-object-on = record { lemma = quote Extensional-Free-object-on }
```
-->

## Free objects and adjoints

If $U$ has a left adjoint $F$, then every $X : \cD$ has a corresponding
free object given by $(F(X), \eta)$, where $\eta$ is the unit of the
adjunction.

```agda
  module _ {F : Functor D C} (F⊣U : F ⊣ U) where
    open is-free-object-on
    open _⊣_ F⊣U

    left-adjoint→unit-is-free : ∀ x → is-free-object-on U (unit.η x)
    left-adjoint→unit-is-free x .eps f = R-adjunct F⊣U f
    left-adjoint→unit-is-free x .commute = L-R-adjunct F⊣U _
    left-adjoint→unit-is-free x .unique other p =
      Equiv.injective (_ , L-adjunct-is-equiv F⊣U) (p ∙ sym (L-R-adjunct F⊣U _))

    left-adjoint→free-objects : ∀ x → Free-object-on U x
    left-adjoint→free-objects x .free = Functor.F₀ F x
    left-adjoint→free-objects x .eta = unit.η x
    left-adjoint→free-objects x .has-is-free = left-adjoint→unit-is-free x
```

Conversely, if $\cD$ has all free objects, then $U$ has a left adjoint.
We begin by constructing a functor $F : \cD \to \cC$ that assigns each
object to its free counterpart; functoriality is given by the universal
property.

```agda
  module _ (free-objects : ∀ x → Free-object-on U x) where
    private
      module free x = Free-object-on (free-objects x)
      open Functor
      open _=>_
      open _⊣_

    free-objects→functor : Functor D C
    free-objects→functor .F₀ = free.free
    free-objects→functor .F₁ f = free.eps _ (free.eta _ D.∘ f)
    free-objects→functor .F-id =
      sym $ free.unique _ C.id $ D.eliml U.F-id ∙ sym (D.idr _)
    free-objects→functor .F-∘ f g =
      sym $ free.unique _ _ $ U.popr (free.commute _) ∙ D.extendl (free.commute _)
```

The unit of the adjunction is given by $\eta$, and the counit by $\eps \id$.
Naturality and the zig-zag identities all follow from the universal property
of free objects.

```agda
    free-objects→left-adjoint : free-objects→functor ⊣ U
    free-objects→left-adjoint .unit .η = free.eta
    free-objects→left-adjoint .unit .is-natural x y f = sym (free.commute x)
    free-objects→left-adjoint .counit .η x = free.eps (U.₀ x) D.id
    free-objects→left-adjoint .counit .is-natural x y f =
      free.unique₂ (U.F₀ x) _ _
        (U.popr (free.commute _) ∙ D.cancell (free.commute _))
        (U.popr (free.commute _) ∙ D.idr _)
    free-objects→left-adjoint .zig =
      free.unique₂ _ _ _
        (U.popr (free.commute _) ∙ D.cancell (free.commute _))
        (D.eliml U.F-id)
    free-objects→left-adjoint .zag =
      free.commute _
```

If we round-trip a left adjoint through these two constructions, then
we obtain the same functor we started with. Moreover, we also obtain
the same unit/counit!


```agda
  left-adjoint→free-objects→left-adjoint
    : ∀ {F : Functor D C}
    → (F⊣U : F ⊣ U)
    → free-objects→functor (left-adjoint→free-objects F⊣U) ≡ F
  left-adjoint→free-objects→left-adjoint {F = F} F⊣U =
    Functor-path (λ _ → refl) λ f →
      ap (R-adjunct F⊣U) (unit.is-natural _ _ f)
      ∙ R-L-adjunct F⊣U (F.₁ f)
    where
      module F = Functor F
      open _⊣_ F⊣U

  adjoint-pair→free-objects→adjoint-pair
    : ∀ {F : Functor D C}
    → (F⊣U : F ⊣ U)
    → PathP (λ i → left-adjoint→free-objects→left-adjoint F⊣U i ⊣ U)
      (free-objects→left-adjoint (left-adjoint→free-objects F⊣U))
      F⊣U
  adjoint-pair→free-objects→adjoint-pair {F = F} F⊣U =
    adjoint-pathp _ _
      (Nat-pathp _ _ λ _ → refl)
      (Nat-pathp _ _ λ x → C.elimr F.F-id)
    where module F = Functor F
```

A similar result holds for a system of free objects.

```agda
  free-objects→left-adjoint→free-objects
    : ∀ (free-objects : ∀ x → Free-object-on U x)
    → left-adjoint→free-objects (free-objects→left-adjoint free-objects) ≡ free-objects
  free-objects→left-adjoint→free-objects free-objects = trivial!
```

We can assemble these pieces into an equivalence between systems of free
objects and left adjoints.

```agda
  free-objects≃left-adjoint
    : (∀ x → Free-object-on U x) ≃ (Σ[ F ∈ Functor D C ] F ⊣ U)
```

<details>
<summary>Constructing the equivalence is straightforward, as we
already have all the pieces laying about!
</summary>

```agda
  free-objects≃left-adjoint = Iso→Equiv $
    (λ free-objects →
      free-objects→functor free-objects ,
      free-objects→left-adjoint free-objects) ,
    iso (λ left-adj → left-adjoint→free-objects (left-adj .snd))
      (λ left-adj →
        left-adjoint→free-objects→left-adjoint (left-adj .snd) ,ₚ
        adjoint-pair→free-objects→adjoint-pair (left-adj .snd))
      free-objects→left-adjoint→free-objects
```
</details>

## Free objects and universal morphisms

<!--
```agda
module _
  {oc ℓc od ℓd}
  {C : Precategory oc ℓc}
  {D : Precategory od ℓd}
  (U : Functor C D)
  where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module U = Cat.Functor.Reasoning U

  open Free-object-on
```
-->

Up to a reorganization of data, free objects and [[universal morphisms]]
are identical: both encode the data of a universal pair $(A, \cD(X, U(A)))$.

```agda
  free-object≃universal-map : ∀ x → Free-object-on U x ≃ Universal-morphism x U
```

<details>
<summary>The proof really is just shuffling data around.
</summary>

```agda
  free-object≃universal-map x =
   Iso→Equiv (trivial-iso! free→univ univ→free)
    where
      open Initial

      free→univ : Free-object-on U x → Universal-morphism x U
      free→univ f .bot = ↓obj (f .eta)
      free→univ f .has⊥ x .centre = ↓hom (D.idr _ ∙ sym (f .commute))
      free→univ f .has⊥ x .paths g↓ = ext (sym (f .unique _ (sym (↓Hom.sq g↓) ∙ D.idr _)))

      univ→free : Universal-morphism x U → Free-object-on U x
      univ→free i .free = ↓Obj.y (i .bot)
      univ→free i .eta = ↓Obj.map (i .bot)
      univ→free i .has-is-free .is-free-object-on.eps f =
        ↓Hom.β (i .has⊥ (↓obj f) .centre)
      univ→free i .has-is-free .is-free-object-on.commute {f = f} =
        sym (↓Hom.sq (i .has⊥ (↓obj f) .centre)) ∙ D.idr _
      univ→free i .has-is-free .is-free-object-on.unique {f = f} g p =
        sym $ ap ↓Hom.β (i .has⊥ (↓obj f) .paths (↓hom (D.idr _ ∙ sym p)))
```
</details>

This lets us easily deduce that systems of universal morphisms are equivalent
to left adjoints.

```agda
  universal-maps≃left-adjoint
    : (∀ x → Universal-morphism x U) ≃ (Σ[ F ∈ Functor D C ] F ⊣ U)
  universal-maps≃left-adjoint =
    Π-cod≃ free-object≃universal-map e⁻¹ ∙e free-objects≃left-adjoint
```

<!--
```agda
module _
  {oc ℓc od ℓd}
  {C : Precategory oc ℓc}
  {D : Precategory od ℓd}
  {U : Functor C D}
  where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module U = Cat.Functor.Reasoning U

  open Free-object-on

  universal-maps→L : (∀ x → Universal-morphism x U) → Functor D C
  universal-maps→L = fst ⊙ Equiv.to (universal-maps≃left-adjoint U)

  universal-maps→L⊣R
    : (univ : ∀ x → Universal-morphism x U)
    → (universal-maps→L univ) ⊣ U
  universal-maps→L⊣R = snd ⊙ Equiv.to (universal-maps≃left-adjoint U)

  L⊣R→universal-maps : ∀ {F : Functor D C} → F ⊣ U → ∀ x → Universal-morphism x U
  L⊣R→universal-maps {F = F} F⊣U = Equiv.from (universal-maps≃left-adjoint U) (F , F⊣U)
```
-->

## Free objects and initiality

In categorical semantics, syntax for a theory $\bT$ is often
presented in 2 seemingly unconnected ways:

1. Via a left adjoint to the forgetful functor that forgets the structure
  of a $\bT$-model; or
2. As an [[initial object]] in the category of $\bT$-models.

Left adjoints encode the universal property "syntax with generators":
structure-preserving maps $\cC(F(X),A)$ out of the syntax generated by $X$
are given by non-structure $\cD(X,U(A))$ on the generators. Conversely,
initial objects give us the universal property of "syntax without generators":
there is a unique structure-preserving map out of the syntax into each model.

We can somewhat reconcile these views by recalling that
[[left adjoints preserve colimits|lapc]]. The initial object is a colimit,
so the initial object in the category $\bT$-models is $F(\bot)$. In other
words: "syntax without generators" and "syntax on 0 generators" coincide.
This correspondence remains intact even when we lack a full left adjoint.

For the remainder of this section, assume that $\cD$ has an initial object
$\bot_{\cD}$. If there is a free object $A : \cC$ on $\bot_{\cD}$, then
$A$ is an initial object in $\cC$.

```agda
  module _ (initial : Initial D) where
    open Initial initial
    open is-free-object-on

    free-on-initial→initial
      : (F[⊥] : Free-object-on U bot)
      → is-initial C (F[⊥] .free)
    free-on-initial→initial F[⊥] x .centre = F[⊥] .eps ¡
    free-on-initial→initial F[⊥] x .paths f =
      sym $ F[⊥] .unique f (sym (¡-unique _))
```

Conversely, if $\cC$ has an initial object $\bot_{\cC}$, then $\bot_{\cC}$
is a free object for $\bot_{\cC}$.

```agda
    is-initial→free-on-initial
      : (c-initial : Initial C)
      → is-free-object-on U {a = Initial.bot c-initial} ¡ 
    is-initial→free-on-initial c-initial .eps _ =
      Initial.¡ c-initial
    is-initial→free-on-initial c-initial .commute =
      ¡-unique₂ _ _
    is-initial→free-on-initial c-initial .unique _ _ =
      sym $ Initial.¡-unique c-initial _
```

Note an initial object in $\cC$ does not guarantee an initial object in
$\cD$, regardless of how many free objects there are. Put syntactically,
a notion of "syntax without generators" does not imply that there is a
set of 0 generators!

<!-- [TODO: Reed M, 27/01/2024] Link to relative adjoints once that is written -->
