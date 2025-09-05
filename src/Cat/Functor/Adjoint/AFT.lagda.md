<!--
```agda
open import Cat.Displayed.Instances.Subobjects
open import Cat.Diagram.Product.Indexed
open import Cat.Instances.Comma.Limits
open import Cat.Diagram.Limit.Initial
open import Cat.Diagram.Limit.Product
open import Cat.Diagram.Product.Power
open import Cat.Diagram.Initial.Weak
open import Cat.Diagram.Coseparator
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Initial
open import Cat.Functor.Adjoint
open import Cat.Instances.Comma
open import Cat.Prelude

import Cat.Reasoning as Cat
import Cat.Morphism as Morb
```
-->

```agda
module Cat.Functor.Adjoint.AFT where
```

# The adjoint functor theorem {defines="adjoint-functor-theorem"}

The **adjoint functor theorem** states a sufficient condition for a
[[continuous functor]] $F : \cC \to \cD$ from a locally small,
[[complete category]] to have a [[left adjoint]].

In an ideal world, this would always be the case: we want to compute an
[[initial object]] $Lx$ in the [[comma category]] $x \swarrow F$, for
each $x : \cD$. Generalising from the case of [[partial orders]], where
a [[bottom element]] is the intersection of everything in the poset, we
might try to find $Lx$ as the limit of the identity functor on $x
\swarrow F$. Furthermore, each of these comma categories are
[[complete|complete category]], by completeness of $\cC$ and continuity
of $F$, so this functor should have a limit!

Unfortunately, the only categories which can be shown to admit arbitrary
limits indexed by themselves are the preorders; The existence of a
large-complete *non*-preorder would contradict excluded middle, which we
neither assume nor reject. Therefore, we're left with the task of
finding a condition on the functor $F$ which ensures that we can compute
the limit of $\Id : x \swarrow F \to x \swarrow F$ using only small
data. The result is a technical device called a **solution set**.

<!--
```agda
module _ {o ℓ o'} {C : Precategory o ℓ} {D : Precategory o' ℓ} (F : Functor C D) where
  open ↓Obj

  private
    module C = Cat C
    module D = Cat D
    module F = Functor F
```
-->

A solution set (for $F$ with respect to $Y : \cD$) is a [[set]] $I$,
together with an $I$-indexed family of objects $X_i$ and morphisms $m_i
: Y \to F(X_i)$, which commute in the sense that, for every $X'$ and $h
: Y \to X'$, there exists a $j : I$ and $t : X_i \to X'$ which satisfy
$h = F(t)m_i$.

```agda
  record Solution-set (Y : ⌞ D ⌟) : Type (o ⊔ lsuc ℓ) where
    field
      {index}    : Type ℓ
      has-is-set : is-set index

      dom    : index → ⌞ C ⌟
      map    : ∀ i → D.Hom Y (F.₀ (dom i))
      factor : ∀ {X'} (h : D.Hom Y (F.₀ X')) → ∃[ i ∈ index ] (Σ[ t ∈ C.Hom (dom i) X' ] (h ≡ F.₁ t D.∘ map i))
```

<!--
```agda
  open Solution-set
```
-->

Put another way, $F$ has a solution set with respect to $X$ if the
[[comma category]] $X \swarrow F$ has a [[weakly initial family]] of
objects, given by the $m_i$ and their domains, with the complicated
factoring condition corresponding to weak initiality.

```agda
  module _ {X} (S :  Solution-set X) where
    solution-set→family : S .index → ⌞ X ↙ F ⌟
    solution-set→family i .dom = tt
    solution-set→family i .cod = S .dom i
    solution-set→family i .map = S .map i

    solution-set→family-is-weak-initial
      : is-weak-initial-fam (X ↙ F) solution-set→family
    solution-set→family-is-weak-initial Y = do
      (i , t , p) ← S .factor (Y .map)
      pure (i , ↓hom (D.elimr refl ∙ p))
```

Then, we can put together the adjoint functor theorem, by showing that
the sea has risen above it:

* Since $\cC$ is small-complete and $F$ is small-continuous, then each
  comma category $x \swarrow F$ is small-complete, by `limits in comma
  categories`{.Agda ident=comma-is-complete};
* Each $x \swarrow F$ has a weakly initial family, and all small
  [[equalisers]], so they all have initial objects;
* An initial object for $x \swarrow F$ is exactly a [[universal morphism]]
  into $F$, and if $F$ admits all universal maps, then it has a left
  adjoint.

```agda
  solution-set→left-adjoint
    : is-complete ℓ ℓ C
    → is-continuous ℓ ℓ F
    → (∀ y → Solution-set y)
    → Σ[ G ∈ Functor D C ] G ⊣ F
  solution-set→left-adjoint c-compl F-cont ss =
    _ , universal-maps→left-adjoint init where module _ x where
    instance
      H-Level-ix : ∀ {n} → H-Level (ss x .index) (2 + n)
      H-Level-ix = basic-instance 2 (ss x .has-is-set)

    init : Initial (x ↙ F)
    init = is-complete-weak-initial→initial (x ↙ F)
      (solution-set→family (ss x))
      (comma-is-complete F c-compl F-cont)
      (solution-set→family-is-weak-initial (ss x))
```

# The "Kan" adjoint functor theorem

The above adjoint functor theorem, which is sometimes called the Freyd
adjoint functor theorem (for example, by @[Maclane:cwm, §5.6]), and
sidesteps the issues of size by use of a small solution set.

We may also state an adjoint functor theorem using existence of limits
from the comma category of $F$, which all must exist if $F$ has a left
adjoint.

```agda
module _ {o ℓ o'} {C : Precategory o ℓ} {D : Precategory o' ℓ} (F : Functor C D) (F-cont : is-continuous (o ⊔ ℓ) ℓ F) where
  formal-aft : (a-pres-comma-limits : ∀ {x} (Q : Functor (x ↙ F) C) → Limit Q) → Σ[ G ∈ Functor D C ] G ⊣ F
  formal-aft a-pres .fst = _
  formal-aft a-pres .snd = universal-maps→left-adjoint λ x → Id-limit→Initial $ Cod-lift-limit F F-cont $ a-pres _
```
