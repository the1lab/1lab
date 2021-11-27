```agda
open import 1Lab.HLevel.Retracts
open import 1Lab.Univalence.SIP
open import 1Lab.Path.Groupoid
open import 1Lab.Univalence
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Algebra.Monoid

module Algebra.Group where
```

# Groups

A **group** is a [monoid] where every element is `invertible`{.Agda}.
Since being invertible is [a proposition],
the [structure] of a group can be obtained by [imposing axioms] on
monoids. An element $x$ of a monoid $M$ is **invertible** if there is an
element $y$ such that both $x \star y$ and $y \star x$ are the identity:

[monoid]: agda://Algebra.Monoid
[structure]: agda://1Lab.Univalence.SIP#SNS
[a proposition]: agda://1Lab.HLevel#isProp
[imposing axioms]: 1Lab.Univalence.SIP.html#adding-axioms

```agda
module _ {ℓ : _} {X : Type ℓ} (M : MonoidStr X) where
  open isMonoid (M .snd)

  invertible : X → _
  invertible x = Σ[ y ∈ X ] (x · y ≡ unit) × (y · x ≡ unit)
```

If an element $x$ has two inverses $y$ and $y'$, then $y = y'$. Since
`monoids are sets`{.Agda ident=monoid-set} --- thus making the paths `x
· y ≡ unit` and `y · x ≡ unit` "immaterial" --- we then have that
`invertible`{.Agda} `is a proposition`{.Agda ident=isProp-invertible}.

```agda
  inverses-unique : (x : X) (y y' : invertible x) → y .fst ≡ y' .fst
  inverses-unique x (y , y-r , y-l) (y' , y'-r , y'-l ) =
    y            ≡⟨ sym monoid-idʳ ⟩
    y · unit     ≡⟨ ap₂ _·_ refl (sym y'-r) ⟩
    y · (x · y') ≡⟨ sym monoid-assoc ⟩
    (y · x) · y' ≡⟨ ap₂ _·_ y-l refl ⟩
    unit · y'    ≡⟨ monoid-idˡ ⟩
    y'           ∎

  isProp-invertible : {x : X} → isProp (invertible x)
  isProp-invertible x y =
    Σ-Path (inverses-unique _ x y)
           (Σ-PathP (monoid-set _ _ _ _) (monoid-set _ _ _ _))
```

From this we immediately get a `SNS`{.Agda} for groups as the monoids
where every element is invertible:

```agda
isGroup : {ℓ : _} {X : Type ℓ} → MonoidStr X → _
isGroup {X = X} M = (y : X) → invertible M y

GroupStr : {ℓ : _} → Type ℓ → Type ℓ
GroupStr X = Σ[ M ∈ MonoidStr X ] (isGroup M)

Group-SNS : {ℓ : _} → SNS (GroupStr {ℓ})
Group-SNS =
  add-axioms Monoid-SNS
    (λ _ → isGroup)
    (λ {X} {s} → isHLevelΠ 1 (λ e → isProp-invertible s))
```

A `Group`{.Agda} is a type equipped with a monoid structure, satisfying
the group axiom. By the [structure identity principle], a path between
groups is the same thing as an equivalence of the underlying types that
preserves the monoid structure:

[structure identity principle]: agda://1Lab.Univalence.SIP

```agda
Group : (ℓ : _) → Type (lsuc ℓ)
Group ℓ = Σ GroupStr

GroupPath : {ℓ : _} {A B : Group ℓ} → (A ≡ B) ≃ (A ≃[ Group-SNS ] B)
GroupPath = SIP Group-SNS
```

## Friendly Interface

Since the way `Group`{.Agda} is associated is very inconvenient, the
following module can be used to bring the group data into scope using
more friendly names.

```agda
module Group {ℓ : _} (group : Group ℓ) where
  private
    module M = isMonoid (group .snd .fst .snd)

  G : Type _

  _⋆_ : G → G → G
  unit : G
  _¯¹ : G → G

  ⋆-assoc-l→r : {x y z : G} → (x ⋆ y) ⋆ z ≡ x ⋆ y ⋆ z
  ⋆-assoc-r→l : {x y z : G} → x ⋆ y ⋆ z ≡ (x ⋆ y) ⋆ z
  ⋆-unitˡ : {z : G} → unit ⋆ z ≡ z
  ⋆-unitʳ : {z : G} → z ⋆ unit ≡ z
  ⋆-invˡ : {z : G} → z ⋆ z ¯¹ ≡ unit
  ⋆-invʳ : {z : G} → z ¯¹ ⋆ z ≡ unit
```

<!--
```
  G = group .fst

  -- Structure
  x ⋆ y = x M.· y
  unit = M.unit
  _¯¹ x = group .snd .snd x .fst

  infixr 30 _⋆_
  infixl 40 _¯¹

  -- Properties
  ⋆-assoc-l→r = M.monoid-assoc
  ⋆-assoc-r→l = sym M.monoid-assoc
  ⋆-unitˡ = M.monoid-idˡ
  ⋆-unitʳ = M.monoid-idʳ
  ⋆-invˡ {z} = group .snd .snd z .snd .fst
  ⋆-invʳ {z} = group .snd .snd z .snd .snd
```
-->

# Symmetric groups

The **symmetric group** on a _set_ $X$ is given the set of its
automorphisms under composition. Note that since we're dealing with
groups, and not general $\infty$-groups, we require that the type be, in
fact, a [set].

[set]: agda://1Lab.HLevel#isSet

```agda
Sym : {ℓ : _} → Set ℓ → Group ℓ
Sym (X , X-Set) = X ≃ X , groupStr where
  monoidStr : MonoidStr (X ≃ X)
  monoidStr .fst .fst = _∙e_
  monoidStr .fst .snd = _ , idEquiv
```

The pointed magma structure is given by `composition of
equivalences`{.Agda ident=_∙e_}, with the `identity equivalence`{.Agda
ident=idEquiv} as the unit;

```agda
  monoidStr .snd .isMonoid.monoid-set =
    isHLevelΣ 2 (isHLevel→ 2 X-Set)
                (λ f → isProp→isSet (isProp-isEquiv f))

  monoidStr .snd .isMonoid.monoid-idʳ =
    Σ-Path refl (isProp-isEquiv _ _ _)

  monoidStr .snd .isMonoid.monoid-idˡ =
    Σ-Path refl (isProp-isEquiv _ _ _)

  monoidStr .snd .isMonoid.monoid-assoc =
    Σ-Path refl (isProp-isEquiv _ _ _)
```

The `monoid laws`{.Agda ident=isMonoid} all follow from $X$ being a
`Set`{.Agda}, and from `isEquiv` `being a proposition`{.Agda
ident=isProp-isEquiv}; The underlying functions are equal by computation.

```agda
  groupStr : GroupStr (X ≃ X)
  groupStr .fst = monoidStr
  groupStr .snd eqv .fst = eqv e¯¹
  groupStr .snd eqv .snd .fst =
    Σ-Path (funext (isEquiv→isIso (eqv .snd) .isIso.left-inverse))
           (isProp-isEquiv _ _ _)
  groupStr .snd eqv .snd .snd =
    Σ-Path (funext (isEquiv→isIso (eqv .snd) .isIso.right-inverse))
           (isProp-isEquiv _ _ _)
```

To prove that this monoid is a group, we send each equivalence to its
inverse; This works the left- and right- identity laws because
`equivalences are isomorphisms`{.Agda ident=isEquiv→isIso}, and
isomorphisms have data expressing that composing in either direction
leaves you with the identity.
