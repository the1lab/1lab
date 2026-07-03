<!--
```agda
open import Cat.Monoidal.Instances.Cartesian
open import Cat.Monoidal.Diagram.Monoid
open import Cat.Diagram.Product.Solver
open import Cat.Diagram.Comonad
open import Cat.Diagram.Product
open import Cat.Diagram.Monad
open import Cat.Cartesian
open import Cat.Prelude

import Cat.Reasoning as Cat

open Comonad-on
open is-comonad
open is-monad
open Monad-on
open Functor
open _=>_
```
-->

```agda
module Cat.Diagram.Comonad.Writer where
```

# Writer (co)monads {defines="writer-comonad"}

If $A$ is an object in a [[Cartesian monoidal category]] $\cC$, then the
functor "product with $A$" functor, $A \times (-)$, can naturally be
equipped with the structure of a [[comonad]]. This structure embodies a
particular view of $A$ as a *resource*, which in particular can be
freely dropped and duplicated. Dropping is necessary to form the counit
map $\eta_X : A \times X \to X$, and duplicating becomes the
comultiplication $\delta_X : A \times X \to A \times (A \times X)$.

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) (A : ⌞ C ⌟) (prod : ∀ B → Product C A B) where
  open Cat C

  private module _ {B} where open Product (prod B) using (⟨_,_⟩ ; π₁ ; π₂ ; π₁∘⟨⟩ ; π₂∘⟨⟩ ; ⟨⟩∘ ; unique ; unique₂) public
  private module _ B where open Product (prod B) renaming (apex to A×) using () public
```
-->

To functional programmers, the functor $A \times (-)$ is of particular
importance when $A$ is equipped with a [[monoid]] structure, in which
case we can make $A \times (-)$ into a [[mon**ad**]]: the
`Writer`{.Agda} monad with values in $A$. We will keep with this name
even in the comonadic setting.

```agda
  Writer : Functor C C
  Writer .F₀   = A×
  Writer .F₁ f = ⟨ π₁ , f ∘ π₂ ⟩
  Writer .F-id = sym (unique (idr _) id-comm)
  Writer .F-∘ f g = sym (unique (pulll π₁∘⟨⟩ ∙ π₁∘⟨⟩) (pulll π₂∘⟨⟩ ∙ extendr π₂∘⟨⟩))
```

Since we've already decided that the comonad structure is built on
dropping and duplicating, our structure maps are essentially forced on
us:

```agda
  Writer-comonad : Comonad-on Writer
  Writer-comonad .counit .η x = π₂
  Writer-comonad .comult .η x = ⟨ π₁ , id ⟩
```

<details>
<summary>The proof that these maps equip $\rm{Writer}(A)$ with a comonad
structure are routine reasoning about products, and so we will leave
them in this `<details>`{.html} block for the curious reader.</summary>

```agda
  Writer-comonad .counit .is-natural x y f = π₂∘⟨⟩
  Writer-comonad .comult .is-natural x y f = unique₂
    (pulll π₁∘⟨⟩ ∙ π₁∘⟨⟩) (pulll π₂∘⟨⟩ ∙ idl _)
    (pulll π₁∘⟨⟩ ∙ π₁∘⟨⟩) (pulll π₂∘⟨⟩ ∙ cancelr π₂∘⟨⟩)
  Writer-comonad .has-is-comonad .δ-unitl = unique₂
    (pulll π₁∘⟨⟩ ∙ π₁∘⟨⟩) (pulll π₂∘⟨⟩ ∙ cancelr π₂∘⟨⟩)
    (idr _) (idr _)
  Writer-comonad .has-is-comonad .δ-unitr = π₂∘⟨⟩
  Writer-comonad .has-is-comonad .δ-assoc = ⟨⟩∘ _ ∙ ap₂ ⟨_,_⟩ refl (pullr π₂∘⟨⟩ ∙ id-comm) ∙ sym (⟨⟩∘ _)
```

</details>

## Writer monads

We will now prove that the construction of `Writer`{.Agda} as a monad,
familiar from functional programming, works in the generality of letting
$\cC$ be an arbitrary Cartesian monoidal category, and with $A$ equipped
with an arbitrary monoid structure.

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) (cartesian : Cartesian-category C) (A : ⌞ C ⌟) where
  open Cartesian-category cartesian
```
-->

The key take-away is that the usual definition works: at the level of
generalised elements, the unit of the mon*ad* maps $x$ to $\langle 1, x
\rangle$, where $1$ is the unit of the mon*oid*; similarly, the
multiplication sends $\langle x , \langle y , z \rangle \rangle$ to
$\langle xy , z \rangle$, where we write the mon*oid*'s multiplication
by juxtaposition.

```agda
  monoid→writer-monad
    : Monoid-on (Cartesian-monoidal cartesian) A → Monad-on (Writer C A (products A))
  monoid→writer-monad monoid = mk where
    module m = Monoid-on monoid

    mk : Monad-on _
    mk .unit .η x = ⟨ m.η ∘ ! , id ⟩
    mk .mult .η x = ⟨ m.μ ∘ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩
```

Above, we have written these structure maps in point-free style. The
proof *strategy* for showing that these obey the monad laws is noting
that this can be shown componentwise. On the "$A$ component" of the
pair, we have a monoid law; and the right component is preserved.
Implementing this is, again, mostly an exercise in dealing with
products.

```agda
    mk .unit .is-natural x y f = ⟨⟩-unique₂ (pulll π₁∘⟨⟩) (pulll π₂∘⟨⟩ ∙ idl f)
      (pulll π₁∘⟨⟩ ∙ π₁∘⟨⟩ ∙ sym (pullr (!-unique _)))
      (pulll π₂∘⟨⟩ ∙ pullr π₂∘⟨⟩ ∙ idr f)
    mk .mult .is-natural x y f = products! products
    mk .has-is-monad .μ-unitr =
      let
        lemma =
          m.μ ∘ ⟨ π₁ , m.η ∘ ! ∘ π₂ ⟩               ≡˘⟨ ap₂ _∘_ refl (⟨⟩-unique (pulll π₁∘⟨⟩ ∙ pullr π₁∘⟨⟩ ∙ idl π₁) (pulll π₂∘⟨⟩ ∙ pullr π₂∘⟨⟩ ∙ ap₂ _∘_ refl (sym (!-unique _)))) ⟩
          m.μ ∘ ⟨ id ∘ π₁ , m.η ∘ π₂ ⟩ ∘ ⟨ π₁ , ! ⟩ ≡⟨ pulll m.μ-unitr ⟩
          π₁ ∘ ⟨ π₁ , ! ⟩                           ≡⟨ π₁∘⟨⟩ ⟩
          π₁                                        ∎
      in ⟨⟩-unique₂ (products! products ∙ lemma) (products! products) (idr π₁) (idr π₂)
    mk .has-is-monad .μ-unitl =
      let
        lemma =
          m.μ ∘ ⟨ m.η ∘ ! , π₁ ⟩                    ≡˘⟨ ap₂ _∘_ refl (⟨⟩-unique (pulll π₁∘⟨⟩ ∙ pullr π₁∘⟨⟩) (pulll π₂∘⟨⟩ ∙ pullr π₂∘⟨⟩ ∙ idl π₁)) ⟩
          m.μ ∘ ⟨ m.η ∘ π₁ , id ∘ π₂ ⟩ ∘ ⟨ ! , π₁ ⟩ ≡⟨ pulll m.μ-unitl ⟩
          π₂ ∘ ⟨ ! , π₁ ⟩                           ≡⟨ π₂∘⟨⟩ ⟩
          π₁                                        ∎
      in ⟨⟩-unique₂ (products! products ∙ lemma) (products! products) (idr π₁) (idr π₂)
    mk .has-is-monad .μ-assoc {x} =
      let
        lemma =
          π₁ ∘ ⟨ m.μ ∘ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩ ∘ ⟨ π₁ , ⟨ m.μ ∘ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩ ∘ π₂ ⟩
            ≡˘⟨ products! products ⟩
          m.μ ∘ ⟨ id ∘ π₁ , m.μ ∘ π₂ ⟩ ∘ ⟨ π₁ , ⟨ π₁ , π₁ ∘ π₂ ⟩ ∘ π₂ ⟩
            ≡⟨ extendl m.μ-assoc ⟩
          m.μ ∘ (⟨ m.μ ∘ π₁ , id ∘ π₂ ⟩ ∘ ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩) ∘ ⟨ π₁ , ⟨ π₁ , π₁ ∘ π₂ ⟩ ∘ π₂ ⟩
            ≡⟨ products! products ⟩
          m.μ ∘ ⟨ m.μ ∘ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₁ ∘ π₂ ∘ π₂ ⟩
            ∎
      in ⟨⟩-unique₂ lemma (products! products)
        (pulll π₁∘⟨⟩ ∙ pullr (⟨⟩-unique (pulll π₁∘⟨⟩ ∙ π₁∘⟨⟩) (pulll π₂∘⟨⟩ ∙ pullr π₂∘⟨⟩)))
        (pulll π₂∘⟨⟩ ∙ pullr π₂∘⟨⟩)

```
