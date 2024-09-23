<!--
```agda
open import Cat.Diagram.Limit.Base
open import Cat.Prelude

import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Diagram.Equaliser.Joint {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
open Functor
open Cat C
open _=>_
```
-->

# Joint equalisers

The **joint equaliser** of a family $(F_i : \hom(a, b))_i$ of parallel
maps is a straightforward generalisation of the notion of [[equaliser]]
to more than two maps. The universal property is straightforward to
state: the joint equaliser of the $F_i$ is an arrow $e : E \to a$,
satisfying $F_i e = F_j e$, which is universal with this property.

```agda
record is-joint-equaliser {ℓ'} {I : Type ℓ'} {E x y} (F : I → Hom x y) (equ : Hom E x) : Type (o ⊔ ℓ ⊔ ℓ') where
  field
    equal     : ∀ {i j} → F i ∘ equ ≡ F j ∘ equ
    universal : ∀ {E'} {e' : Hom E' x} (eq : ∀ i j → F i ∘ e' ≡ F j ∘ e') → Hom E' E
    factors   : ∀ {E'} {e' : Hom E' x} {eq : ∀ i j → F i ∘ e' ≡ F j ∘ e'} → equ ∘ universal eq ≡ e'
    unique
      : ∀ {E'} {e' : Hom E' x} {eq : ∀ i j → F i ∘ e' ≡ F j ∘ e'} {o : Hom E' E}
      → equ ∘ o ≡ e'
      → o ≡ universal eq
```

<!--
```agda
  unique₂
    : ∀ {E'} {e' : Hom E' x} {o1 o2 : Hom E' E}
    → (∀ i j → F i ∘ e' ≡ F j ∘ e')
    → equ ∘ o1 ≡ e'
    → equ ∘ o2 ≡ e'
    → o1 ≡ o2
  unique₂ eq p q = unique {eq = eq} p ∙ sym (unique q)
```
-->

A simple calculation tells us that joint equalisers are [[monic]], much
like binary equalisers:

```agda
  is-joint-equaliser→is-monic : is-monic equ
  is-joint-equaliser→is-monic g h x = unique₂ (λ i j → extendl equal) refl (sym x)
```

<!--
```agda
record Joint-equaliser {ℓ'} {I : Type ℓ'} {x y} (F : I → Hom x y) : Type (o ⊔ ℓ ⊔ ℓ') where
  field
    {apex} : Ob
    equ : Hom apex x
    has-is-je : is-joint-equaliser F equ
  open is-joint-equaliser has-is-je public

open is-joint-equaliser
```
-->

## Computation

Joint equalisers are also limits. We can define the figure shape that
they are limits over as a straightforward generalisation of the
parallel-arrows category, where there is an arbitrary [[set]] of arrows
between the two objects.

```agda
module _ {ℓ'} {I : Type ℓ'} ⦃ _ : H-Level I 2 ⦄ {x y} (F : I → Hom x y) where
  private module P = Precategory

  private
    shape : Precategory _ _
    shape .P.Ob              = Bool
    shape .P.Hom false false = Lift ℓ' ⊤
    shape .P.Hom false true  = I
    shape .P.Hom true false  = Lift ℓ' ⊥
    shape .P.Hom true true   = Lift ℓ' ⊤
```

<details>
<summary>Giving this the structure of a category is trivial: other than
the $I$-many parallel arrows, there is nothing to compose
with.</summary>

```agda
    shape .P.Hom-set true true = hlevel 2
    shape .P.Hom-set true false = hlevel 2
    shape .P.Hom-set false true = hlevel 2
    shape .P.Hom-set false false = hlevel 2
    shape .P.id {true} = _
    shape .P.id {false} = _
    shape .P._∘_ {true}  {true}  {true}  f g = lift tt
    shape .P._∘_ {false} {true}  {true}  f g = g
    shape .P._∘_ {false} {false} {true}  f g = f
    shape .P._∘_ {false} {false} {false} f g = lift tt
    shape .P.idr {true}  {true}  f = refl
    shape .P.idr {false} {true}  f = refl
    shape .P.idr {false} {false} f = refl
    shape .P.idl {true}  {true}  f = refl
    shape .P.idl {false} {true}  f = refl
    shape .P.idl {false} {false} f = refl
    shape .P.assoc {true}  {true}  {true}  {true}  f g h = refl
    shape .P.assoc {false} {true}  {true}  {true}  f g h = refl
    shape .P.assoc {false} {false} {true}  {true}  f g h = refl
    shape .P.assoc {false} {false} {false} {true}  f g h = refl
    shape .P.assoc {false} {false} {false} {false} f g h = refl
```

</details>

The family of arrows $I \to \hom(x, y)$ extends straightforwardly to a
functor from this `shape`{.Agda} category to $\cC$.

```agda
    diagram : Functor shape C
    diagram .F₀ true  = y
    diagram .F₀ false = x
    diagram .F₁ {true} {true} f = id
    diagram .F₁ {false} {true} i = F i
    diagram .F₁ {false} {false} f = id
    diagram .F-id {true} = refl
    diagram .F-id {false} = refl
    diagram .F-∘ {true} {true} {true} f g = introl refl
    diagram .F-∘ {false} {true} {true} f g = introl refl
    diagram .F-∘ {false} {false} {true} f g = intror refl
    diagram .F-∘ {false} {false} {false} f g = introl refl
```

If the family is pointed, and the `diagram`{.Agda} has a limit, then
this limit is a joint equaliser of the given arrows. The requirement for
a point in the family ensures that we're not taking the joint equaliser
of *no* arrows. The construction is invariant under the choice of point
(since joint equalisers, as limits, are unique), but we won't need this.

```agda
  is-limit→joint-equaliser : ∀ {L} {l} → I → is-limit diagram L l → is-joint-equaliser F (l .η false)
  is-limit→joint-equaliser {L} {l} ix lim = je where
    module l = is-limit lim
    je : is-joint-equaliser F (l .η false)
    je .equal = sym (l .is-natural false true _) ∙ l .is-natural false true _
    je .universal {E'} {e'} eq = l.universal
      (λ { true → F ix ∘ e' ; false → e' })
      λ { {true}  {true}  f → eliml refl
        ; {false} {true}  f → eq f ix
        ; {false} {false} f → eliml refl }
    je .factors = l.factors _ _
    je .unique p = l.unique _ _ _ λ where
      true  → ap₂ _∘_ (intror refl ∙ l .is-natural false true ix) refl ∙ pullr p
      false → p

  open Joint-equaliser

  Limit→Joint-equaliser : I → Limit diagram → Joint-equaliser F
  Limit→Joint-equaliser ix lim .apex = Limit.apex lim
  Limit→Joint-equaliser ix lim .equ = Limit.cone lim .η false
  Limit→Joint-equaliser ix lim .has-is-je = is-limit→joint-equaliser ix (Limit.has-limit lim)
```
