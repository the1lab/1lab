<!--
```agda
open import Cat.Instances.Functor
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Prelude

open import Data.Bool

open import Order.Base
open import Order.Cat

import Order.Reasoning as Poset
```
-->

```agda
module Cat.Instances.Shape.Interval where
```

<!--
```agda
open is-product
open Terminal
open Product
open Functor
```
-->

# Interval category

The interval category is the category with two points, called (as a form
of endearment) $0$ and $1$, and a single arrow between them.
Correspondingly, in shorthand this category is referred to as $\intcat$.
Since it has a single (non-trivial) arrow, it is a [[partial order]]; In fact,
it is the partial order generated by the type of [booleans] and the natural
ordering on them, with $\bot \le \top$.

[booleans]: Data.Bool.html

```agda
open Precategory

Bool-poset : Poset lzero lzero
Bool-poset = po where
  R : Bool → Bool → Type
  R false false = ⊤
  R false true  = ⊤
  R true  false = ⊥
  R true  true  = ⊤
```

:::{.note}
We define the relation by recursion, rather than by induction,
to avoid the issues with computational behaviour with indexed inductive
types in Cubical Agda. The interval category is the category underlying
the poset of booleans:
:::

<!--
```agda
  Rrefl : ∀ {x} → R x x
  Rrefl {false} = tt
  Rrefl {true} = tt

  Rtrans : ∀ {x y z} → R x y → R y z → R x z
  Rtrans {false} {false} {false} tt tt = tt
  Rtrans {false} {false} {true}  tt tt = tt
  Rtrans {false} {true}  {false} tt ()
  Rtrans {false} {true}  {true}  tt tt = tt
  Rtrans {true}  {false} {false} () tt
  Rtrans {true}  {false} {true}  () tt
  Rtrans {true}  {true}  {false} tt ()
  Rtrans {true}  {true}  {true}  tt tt = tt

  Rantisym : ∀ {x y} → R x y → R y x → x ≡ y
  Rantisym {false} {false} tt tt = refl
  Rantisym {false} {true}  tt ()
  Rantisym {true}  {false} () tt
  Rantisym {true}  {true}  tt tt = refl

  Rprop : ∀ {x y} (p q : R x y) → p ≡ q
  Rprop {false} {false} tt tt = refl
  Rprop {false} {true}  tt tt = refl
  Rprop {true}  {false} () ()
  Rprop {true}  {true}  tt tt = refl

  po : Poset _ _
  po .Poset.Ob = Bool
  po .Poset._≤_ = R
  po .Poset.≤-thin = Rprop
  po .Poset.≤-refl = Rrefl
  po .Poset.≤-trans = Rtrans
  po .Poset.≤-antisym = Rantisym
```
-->

```agda
0≤1 : Precategory lzero lzero
0≤1 = poset→category Bool-poset
```

## Meets

Note that the category $\intcat$ is [[finitely complete]] (i.e. it is
bounded, and has binary meets for every pair of elements): The top
element is $\top$ (go figure), and meets are given by the boolean "and"
function.

```agda
0≤1-top : Terminal 0≤1
0≤1-top .top = true

0≤1-top .has⊤ false .centre = tt
0≤1-top .has⊤ false .paths tt = refl

0≤1-top .has⊤ true  .centre = tt
0≤1-top .has⊤ true  .paths tt = refl

0≤1-products : ∀ A B → Product 0≤1 A B
0≤1-products A B .apex = and A B
```

<details>
<summary>
A ridiculous amount of trivial pattern matching is needed to establish
that this cone is universal, but fortunately, we can appeal to thinness
to establish commutativity and uniqueness.
</summary>

```agda
0≤1-products false false .π₁ = tt
0≤1-products false true  .π₁ = tt
0≤1-products true  false .π₁ = tt
0≤1-products true  true  .π₁ = tt

0≤1-products false false .π₂ = tt
0≤1-products false true  .π₂ = tt
0≤1-products true  false .π₂ = tt
0≤1-products true  true  .π₂ = tt

0≤1-products A B .has-is-product .⟨_,_⟩ = meet _ _ _ where
  meet : ∀ A B Q (p : Hom 0≤1 Q A) (q : Hom 0≤1 Q B) → Hom 0≤1 Q (and A B)
  meet false false false tt tt = tt
  meet false false true  () ()
  meet false true  false tt tt = tt
  meet false true  true  () tt
  meet true  false false tt tt = tt
  meet true  false true  tt ()
  meet true  true  false tt tt = tt
  meet true  true  true  tt tt = tt
```

</details>

```agda
0≤1-products A B .has-is-product .π₁∘⟨⟩ = Poset.≤-thin Bool-poset _ _
0≤1-products A B .has-is-product .π₂∘⟨⟩ = Poset.≤-thin Bool-poset _ _
0≤1-products A B .has-is-product .unique _ _ = Poset.≤-thin Bool-poset _ _
```

# The space of arrows

The total space of the $\hom$ family of a precategory is referred to as
its "space of arrows". A point in this space is a "free-standing arrow":
it comes equipped with its own domain and codomain. We note that, since
a precategory has no upper bound on the h-level of its space of objects,
its space of arrows also need not be particularly truncated. However,
for a [[univalent category]] it is a groupoid, and for a [[poset|posets
as categories]] it is a set.

An equivalent description of the space of arrows is as the collection of
functors $[ \intcat, \cC ]$: a functor out of $\intcat$ corresponds
rather directly to picking out an arrow in $\cC$. Its domain is the
object that $\bot$ maps to, and is codomain is the object that $\top$
maps to.

<!--
```agda
private variable
  o ℓ : Level
```
-->

```agda
Arrows : Precategory o ℓ → Type (o ⊔ ℓ)
Arrows C = Σ[ A ∈ C ] Σ[ B ∈ C ] (C.Hom A B)
  where module C = Precategory C
```

<!--
```agda
module _ (C : Precategory o ℓ) where
  Hom→Arrow : {a b : Ob C} → Hom C a b → Arrows C
  Hom→Arrow f = _ , _ , f

  Arrows-path
    : {a b : Arrows C}
    → (p : a .fst ≡ b .fst)
    → (q : a .snd .fst ≡ b .snd .fst)
    → PathP (λ i → Hom C (p i) (q i)) (a .snd .snd) (b .snd .snd)
    → a ≡ b
  Arrows-path p q r i = p i , q i , r i
```
-->

We now fix a category and prove the correspondence between the space of
arrows $\Arr{\cC}$, as defined above, and the space of functors $[
\intcat, \cC ]$.

```agda
module _ {C : Precategory o ℓ} where
  import Cat.Reasoning C as C

  arrow→functor : Arrows C → Functor 0≤1 C
  arrow→functor (A , B , f) = fun where
    fun : Functor _ _
    fun .F₀ false = A
    fun .F₀ true = B
    fun .F₁ {false} {false} tt = C.id
    fun .F₁ {false} {true}  tt = f
    fun .F₁ {true}  {false} ()
    fun .F₁ {true}  {true}  tt = C.id
```

<!--
```agda
    fun .F-id {false} = refl
    fun .F-id {true} = refl
    fun .F-∘ {false} {false} {false} tt tt = sym (C.idl _)
    fun .F-∘ {false} {false} {true}  tt tt = sym (C.idr _)
    fun .F-∘ {false} {true}  {false} () g
    fun .F-∘ {false} {true}  {true}  tt tt = sym (C.idl _)
    fun .F-∘ {true}  {false} {false} tt ()
    fun .F-∘ {true}  {false} {true}  tt ()
    fun .F-∘ {true}  {true}  {false} () g
    fun .F-∘ {true}  {true}  {true}  tt tt = sym (C.idr _)
```
-->

The other direction, turning a functor into an object of `Arr`{.Agda},
is mostly immediate: we can extract the non-trivial arrow by seeing what
the non-trivial arrow $0 \le 1$ maps to, and the domain/codomain can be
inferred by Agda.

```agda
  functor→arrow : Functor 0≤1 C → Arrows C
  functor→arrow F = _ , _ , F .F₁ {false} {true} tt
```

That this function is an equivalence is also straightforward: The only
non-trivial step is appealing to functoriality of $F$, specifically that
it must preserve identity arrows. The converse direction (going functor
→ arrow → functor) is definitionally the identity.

```agda
  arrow≃functor : is-equiv arrow→functor
  arrow≃functor = is-iso→is-equiv (iso functor→arrow rinv linv) where
    rinv : is-right-inverse functor→arrow arrow→functor
    rinv F =
      Functor-path
        (λ { true → refl ; false → refl })
        (λ { {false} {false} tt → sym (F-id F)
           ; {false} {true}  tt → refl
           ; {true}  {false} ()
           ; {true}  {true}  tt → sym (F-id F) })

    linv : is-left-inverse functor→arrow arrow→functor
    linv x = refl
```

Correspondingly, we _define_ the arrow category $\Arr{\cC}$ as the
functor category $[ \intcat, \cC ]$.

```agda
Arr : Precategory o ℓ → Precategory (o ⊔ ℓ) ℓ
Arr C = Cat[ 0≤1 , C ]
```
