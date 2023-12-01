<!--
```agda
open import Cat.Displayed.Cartesian
open import Cat.Diagram.Pullback
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism as DM
import Cat.Reasoning as CR
```
-->

```agda
module Cat.Displayed.Total
  {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ') where

open Displayed E
open DR E
open DM E
open CR B
```

# The total category of a displayed category {defines=total-category}

So far, we've been thinking of [[displayed categories]] as "categories of
structures" over some base category. However, it's often useful to
consider a more "bundled up" notion of structure, where the carrier and
the structure are considered as a singular object. For instance, if we
consider the case of algebraic structures, we often want to think about
"a monoid" as a singular thing, as opposed to structure imposed atop
some set.

Constructing the total category does exactly this. The objects
are pairs of an object from the base, an object from the displayed
category that lives over it.

Note that we use a sigma type here instead of a record for technical
reasons: this makes it simpler to work with algebraic structures.

```agda
Total : Type (o ⊔ o')
Total = Σ[ Carrier ∈ Ob ] Ob[ Carrier ]
```

The situation is similar for morphisms: we bundle up a morphism from the
base category along with a morphism that lives above it.

```agda
record Total-hom (X Y : Total) : Type (ℓ ⊔ ℓ') where
  constructor total-hom
  field
    hom       : Hom (X .fst) (Y .fst)
    preserves : Hom[ hom ] (X .snd) (Y .snd)

open Total-hom
```

<!--
```agda
private unquoteDecl eqv = declare-record-iso eqv (quote Total-hom)
```
-->

As is tradition, we need to prove some silly lemmas showing that
the bundled morphisms form an hset, and another characterizing
the paths between morphisms.

```agda
total-hom-is-set : ∀ (X Y : Total) → is-set (Total-hom X Y)
total-hom-is-set X Y = Iso→is-hlevel 2 eqv $
  Σ-is-hlevel 2 (hlevel 2) (λ a → Hom[ _ ]-set _ _)

total-hom-path : ∀ {X Y : Total} {f g : Total-hom X Y}
               → (p : f .hom ≡ g .hom) → f .preserves ≡[ p ] g .preserves → f ≡ g
total-hom-path p p' i .hom = p i
total-hom-path {f = f} {g = g} p p' i .preserves = p' i
```

<!--
```agda
total-hom-pathp
  : ∀ {X X' Y Y' : Total} {f : Total-hom X Y} {g : Total-hom X' Y'}
  → (p : X ≡ X') (q : Y ≡ Y')
  → (r : PathP (λ z → Hom (p z .fst) (q z .fst)) (f .hom) (g .hom))
  → PathP (λ z → Hom[ r z ] (p z .snd) (q z .snd)) (f .preserves) (g .preserves)
  → PathP (λ i → Total-hom (p i) (q i)) f g
total-hom-pathp p q r s i .hom = r i
total-hom-pathp p q r s i .preserves = s i
```
-->

With all that in place, we can construct the total category!

```agda
∫ : Precategory (o ⊔ o') (ℓ ⊔ ℓ')
∫ .Precategory.Ob = Total
∫ .Precategory.Hom = Total-hom
∫ .Precategory.Hom-set = total-hom-is-set
∫ .Precategory.id .hom = id
∫ .Precategory.id .preserves = id'
∫ .Precategory._∘_ f g .hom = f .hom ∘ g .hom
∫ .Precategory._∘_ f g .preserves = f .preserves ∘' g .preserves
∫ .Precategory.idr _ = total-hom-path (idr _) (idr' _)
∫ .Precategory.idl _ = total-hom-path (idl _) (idl' _)
∫ .Precategory.assoc _ _ _ = total-hom-path (assoc _ _ _) (assoc' _ _ _)
```

<!--
```agda
πᶠ : Functor ∫ B
πᶠ .Functor.F₀ = fst
πᶠ .Functor.F₁ = Total-hom.hom
πᶠ .Functor.F-id = refl
πᶠ .Functor.F-∘ f g = refl
```
-->

## Morphisms in the total category

Isomorphisms in the total category of $E$ consist of pairs of
isomorphisms in $B$ and $E$.

```agda
private module ∫E = CR ∫

total-iso→iso : ∀ {x y} → x ∫E.≅ y → x .fst ≅ y .fst
total-iso→iso f = make-iso
    (∫E._≅_.to f .hom)
    (∫E._≅_.from f .hom)
    (ap hom $ ∫E._≅_.invl f)
    (ap hom $ ∫E._≅_.invr f)

total-iso→iso[] : ∀ {x y} → (f : x ∫E.≅ y) → x .snd ≅[ total-iso→iso f ] y .snd
total-iso→iso[] f = make-iso[ total-iso→iso f ]
    (∫E._≅_.to f .preserves)
    (∫E._≅_.from f .preserves)
    (ap preserves $ ∫E._≅_.invl f)
    (ap preserves $ ∫E._≅_.invr f)
```

## Pullbacks in the total category

[[Pullbacks]] in the total category of $\cE$ have a particularly nice
characterization. Consider the following pair of commuting squares.

~~~{.quiver .tall-2}
\begin{tikzcd}
  & {P'} && {Y'} \\
  {X'} && {X'} \\
  & P && Y \\
  X && Z \\
  \arrow[lies over, from=2-1, to=4-1]
  \arrow[lies over, from=1-4, to=3-4]
  \arrow["f", from=4-1, to=4-3]
  \arrow["{p_1}"', from=3-2, to=4-1]
  \arrow["{p_2}"{pos=0.3}, from=3-2, to=3-4]
  \arrow["g", from=3-4, to=4-3]
  \arrow[lies over, from=2-3, to=4-3]
  \arrow[lies over, from=1-2, to=3-2]
  \arrow["{p_1'}"', from=1-2, to=2-1]
  \arrow["{f'}"{pos=0.7}, from=2-1, to=2-3]
  \arrow["{p_2'}", from=1-2, to=1-4]
  \arrow["g", from=1-4, to=2-3]
\end{tikzcd}
~~~

If the bottom square is a pullback square, and both $p_1'$ and $g'$ are
cartesian, then the upper square is a pullback in the total category of
$\cE$.

```agda
cartesian+pullback→total-pullback
  : ∀ {p x y z p' x' y' z'}
  → {p₁ : Hom p x} {f : Hom x z} {p₂ : Hom p y} {g : Hom y z}
  → {p₁' : Hom[ p₁ ] p' x'} {f' : Hom[ f ] x' z'}
  → {p₂' : Hom[ p₂ ] p' y'} {g' : Hom[ g ] y' z'}
  → is-cartesian E p₁ p₁'
  → is-cartesian E g g'
  → (pb : is-pullback B p₁ f p₂ g)
  → (open is-pullback pb)
  → f' ∘' p₁' ≡[ square ] g' ∘' p₂'
  → is-pullback ∫
      (total-hom p₁ p₁') (total-hom f f')
      (total-hom p₂ p₂') (total-hom g g')
```

As the lower square is already a pullback, all that remains is
constructing a suitable universal morphism in $\cE$. Luckily, $p_1'$
is cartesian, so we can factorise maps $A' \to X'$ in $\cE$ to obtain
a map $A' \to P'$. We then use the fact that $g'$ is cartesian to show
that the map we've constructed factorises maps $A' \to Y'$ as well.
Uniqueness follows from the fact that $p_1'$ is cartesian.

```agda
cartesian+pullback→total-pullback p₁-cart g-cart pb square' = total-pb where
  open is-pullback
  open Total-hom
  module p₁' = is-cartesian p₁-cart
  module g' = is-cartesian g-cart

  total-pb : is-pullback ∫ _ _ _ _
  total-pb .square = total-hom-path (pb .square) square'
  total-pb .universal {a , a'} {p₁''} {p₂''} p =
    total-hom (pb .universal (ap hom p))
      (p₁'.universal' (pb .p₁∘universal) (p₁'' .preserves))
  total-pb .p₁∘universal =
    total-hom-path (pb .p₁∘universal) (p₁'.commutesp _ _)
  total-pb .p₂∘universal {p = p} =
    total-hom-path (pb .p₂∘universal) $
      g'.uniquep₂ _ _ _ _ _
        (pulll[] _ (symP square')
        ∙[] pullr[] _ (p₁'.commutesp (pb .p₁∘universal) _))
        (symP $ ap preserves p)
  total-pb .unique p q =
    total-hom-path (pb .unique (ap hom p) (ap hom q)) $
      p₁'.uniquep _ _ (pb .p₁∘universal) _ (ap preserves p)
```

We can also show the converse, provided that $\cE$ is a [[fibration|cartesian fibration]].

```agda
cartesian+total-pullback→pullback
  : ∀ {p x y z p' x' y' z'}
  → {p₁ : Hom p x} {f : Hom x z} {p₂ : Hom p y} {g : Hom y z}
  → {p₁' : Hom[ p₁ ] p' x'} {f' : Hom[ f ] x' z'}
  → {p₂' : Hom[ p₂ ] p' y'} {g' : Hom[ g ] y' z'}
  → Cartesian-fibration E
  → is-cartesian E p₁ p₁'
  → is-cartesian E g g'
  → is-pullback ∫
      (total-hom p₁ p₁') (total-hom f f')
      (total-hom p₂ p₂') (total-hom g g')
  → is-pullback B p₁ f p₂ g
```

As we already have a pullback in the total category, the crux will be
constructing enough structure in $\cE$ so that we can invoke the universal
property of the pullback. We can do this by appealing to the fact that
$\cE$ is a fibration, which allows us to lift morphisms in the base
to obtain a cone in $\cE$. From here, we use the fact that $p_1'$ and
$g'$ are cartesian to construct the relevant paths.

```agda
cartesian+total-pullback→pullback
  {p} {x} {y} {z}
  {p₁ = p₁} {f} {p₂} {g} {p₁'} {f'} {p₂'} {g'} fib p₁-cart g-cart total-pb = pb where
  open is-pullback
  open Total-hom
  open Cartesian-fibration fib
  module p₁' = is-cartesian p₁-cart
  module g' = is-cartesian g-cart

  pb : is-pullback B _ _ _ _
  pb .square = ap hom (total-pb .square)
  pb .universal {P} {p₁''} {p₂''} sq =
    total-pb .universal
      {p₁' = total-hom p₁'' (has-lift.lifting p₁'' _)}
      {p₂' = total-hom p₂'' (g'.universal' (sym sq) (f' ∘' has-lift.lifting p₁'' _))}
      (total-hom-path sq (symP (g'.commutesp (sym sq) _))) .hom
  pb .p₁∘universal =
    ap hom $ total-pb .p₁∘universal
  pb .p₂∘universal =
    ap hom $ total-pb .p₂∘universal
  pb .unique {p = p} q r =
    ap hom $ total-pb .unique
      (total-hom-path q (p₁'.commutesp q _))
      (total-hom-path r (g'.uniquep _ _ (sym $ p) _
        (pulll[] _ (symP $ ap preserves (total-pb .square))
        ∙[] pullr[] _ (p₁'.commutesp q _))))
```
