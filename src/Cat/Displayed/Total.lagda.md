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
module Cat.Displayed.Total where
```

<!--
```agda
module _ {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ') where
  open CR B
  open DR E
  open DM E
```
-->

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
  Total = Σ[ Carrier ∈ B ] Ob[ Carrier ]
```

The situation is similar for morphisms: we bundle up a morphism from the
base category along with a morphism that lives above it.

```agda
  record ∫Hom (X Y : Total) : Type (ℓ ⊔ ℓ') where
    constructor ∫hom
    field
      fst : Hom (X .fst) (Y .fst)
      snd : Hom[ fst ] (X .snd) (Y .snd)

  open ∫Hom
```

<!--
```agda
  unquoteDecl H-Level-∫Hom = declare-record-hlevel 2 H-Level-∫Hom (quote ∫Hom)
```
-->

As is tradition, we need to prove some silly lemmas showing that
the bundled morphisms form an hset, and another characterizing
the paths between morphisms.

```agda
  ∫Hom-path : ∀ {X Y : Total} {f g : ∫Hom X Y}
            → (p : f .fst ≡ g .fst) → f .snd ≡[ p ] g .snd → f ≡ g
  ∫Hom-path p p' i .fst = p i
  ∫Hom-path {f = f} {g = g} p p' i .snd = p' i
```

<!--
```agda
  ∫Hom-pathp
    : ∀ {X X' Y Y' : Total} {f : ∫Hom X Y} {g : ∫Hom X' Y'}
    → (p : X ≡ X') (q : Y ≡ Y')
    → (r : PathP (λ z → Hom (p z .fst) (q z .fst)) (f .fst) (g .fst))
    → PathP (λ z → Hom[ r z ] (p z .snd) (q z .snd)) (f .snd) (g .snd)
    → PathP (λ i → ∫Hom (p i) (q i)) f g
  ∫Hom-pathp p q r s i .fst = r i
  ∫Hom-pathp p q r s i .snd = s i
```
-->

With all that in place, we can construct the total category!

```agda
  ∫ : Precategory (o ⊔ o') (ℓ ⊔ ℓ')
  ∫ .Precategory.Ob = Total
  ∫ .Precategory.Hom = ∫Hom
  ∫ .Precategory.Hom-set _ _ = hlevel 2
  ∫ .Precategory.id .fst = id
  ∫ .Precategory.id .snd = id'
  ∫ .Precategory._∘_ f g .fst = f .fst ∘ g .fst
  ∫ .Precategory._∘_ f g .snd = f .snd ∘' g .snd
  ∫ .Precategory.idr _ = ∫Hom-path (idr _) (idr' _)
  ∫ .Precategory.idl _ = ∫Hom-path (idl _) (idl' _)
  ∫ .Precategory.assoc _ _ _ = ∫Hom-path (assoc _ _ _) (assoc' _ _ _)
```

The total category comes equipped with a projection onto the base category.

```agda
  πᶠ : Functor ∫ B
  πᶠ .Functor.F₀ = fst
  πᶠ .Functor.F₁ = ∫Hom.fst
  πᶠ .Functor.F-id = refl
  πᶠ .Functor.F-∘ f g = refl
```

## Morphisms in the total category

Isomorphisms in the total category of $E$ consist of pairs of
isomorphisms in $B$ and $E$.

```agda
  private module ∫E = CR ∫

  total-iso→iso : ∀ {x y} → x ∫E.≅ y → x .fst ≅ y .fst
  total-iso→iso f = make-iso
    (∫E._≅_.to f .fst)
    (∫E._≅_.from f .fst)
    (ap fst $ ∫E._≅_.invl f)
    (ap fst $ ∫E._≅_.invr f)

  total-iso→iso[] : ∀ {x y} → (f : x ∫E.≅ y) → x .snd ≅[ total-iso→iso f ] y .snd
  total-iso→iso[] f = make-iso[ total-iso→iso f ]
    (∫E._≅_.to f .snd)
    (∫E._≅_.from f .snd)
    (ap snd $ ∫E._≅_.invl f)
    (ap snd $ ∫E._≅_.invr f)
```

## Pullbacks in the total category

[[Pullbacks]] in the total category of $\cE$ have a particularly nice
characterization. Consider the following pair of commuting squares.

~~~{.quiver}
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
        (∫hom p₁ p₁') (∫hom f f')
        (∫hom p₂ p₂') (∫hom g g')
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
    open ∫Hom
    module p₁' = is-cartesian p₁-cart
    module g' = is-cartesian g-cart

    total-pb : is-pullback ∫ _ _ _ _
    total-pb .square = ∫Hom-path (pb .square) square'
    total-pb .universal {a , a'} {p₁''} {p₂''} p =
      ∫hom (pb .universal (ap fst p))
        (p₁'.universal' (pb .p₁∘universal) (p₁'' .snd))
    total-pb .p₁∘universal =
      ∫Hom-path (pb .p₁∘universal) (p₁'.commutesp _ _)
    total-pb .p₂∘universal {p = p} =
      ∫Hom-path (pb .p₂∘universal) $
        g'.uniquep₂ _ _ _ _ _
          (pulll[] _ (symP square')
          ∙[] pullr[] _ (p₁'.commutesp (pb .p₁∘universal) _))
          (symP $ ap snd p)
    total-pb .unique p q =
      ∫Hom-path (pb .unique (ap fst p) (ap fst q)) $
        p₁'.uniquep _ _ (pb .p₁∘universal) _ (ap snd p)
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
        (∫hom p₁ p₁') (∫hom f f')
        (∫hom p₂ p₂') (∫hom g g')
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
    open ∫Hom
    open Cartesian-fibration E fib
    module p₁' = is-cartesian p₁-cart
    module g' = is-cartesian g-cart

    pb : is-pullback B _ _ _ _
    pb .square = ap fst (total-pb .square)
    pb .universal {P} {p₁''} {p₂''} sq =
      total-pb .universal
        {p₁' = ∫hom p₁'' (π* p₁'' _)}
        {p₂' = ∫hom p₂'' (g'.universal' (sym sq) (f' ∘' π* p₁'' _))}
        (∫Hom-path sq (symP (g'.commutesp (sym sq) _))) .fst
    pb .p₁∘universal =
      ap fst $ total-pb .p₁∘universal
    pb .p₂∘universal =
      ap fst $ total-pb .p₂∘universal
    pb .unique {p = p} q r =
      ap fst $ total-pb .unique
        (∫Hom-path q (p₁'.commutesp q _))
        (∫Hom-path r (g'.uniquep _ _ (sym $ p) _
          (pulll[] _ (symP $ ap snd (total-pb .square))
          ∙[] pullr[] _ (p₁'.commutesp q _))))
```

<!--
```agda
module _ {o ℓ o' ℓ'} {B : Precategory o ℓ} {E : Displayed B o' ℓ'} where
  open CR B

  instance
    Funlike-∫Hom
      : ∀ {ℓ'' ℓ'''} {A : Type ℓ''} {B : A → Type ℓ'''}
      → {X Y : Total E} ⦃ i : Funlike (Hom (X .fst) (Y .fst)) A B ⦄
      → Funlike (∫Hom E X Y) A B
    Funlike-∫Hom ⦃ i ⦄ .Funlike._·_ f x = f .∫Hom.fst · x

    H-Level-∫Hom' : ∀ {X Y} {n} → H-Level (∫Hom E X Y) (2 + n)
    H-Level-∫Hom' = H-Level-∫Hom E
```
-->
