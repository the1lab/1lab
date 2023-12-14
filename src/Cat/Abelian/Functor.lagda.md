<!--
```agda
open import Algebra.Group.Ab
open import Algebra.Group

open import Cat.Functor.FullSubcategory
open import Cat.Abelian.Base
open import Cat.Diagram.Zero
open import Cat.Prelude
```
-->

```agda
module Cat.Abelian.Functor where
```

# Ab-enriched functors

Since [$\Ab$-categories] are additionally equipped with the structure of
[[abelian groups]] on their $\hom$-sets, it's natural that we ask that
functors between $\Ab$-categories preserve this structure. In
particular, since every functor $F : \cC \to \cD$ has an action $F(-) :
\hom(a,b) \to \hom(Fa,Fb)$ which is a map of sets, when $\cC$ and $\cD$
are considered to be abelian groups, we should require that the action
$F(-)$ be a group homomorphism.

[$\Ab$-categories]: Cat.Abelian.Base.html#ab-enriched-categories

<!--
```agda
module
  _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    (A : Ab-category C) (B : Ab-category D)
  where
  private
    module A = Ab-category A
    module B = Ab-category B
```
-->

```agda
  record Ab-functor : Type (o ⊔ o' ⊔ ℓ ⊔ ℓ') where
    field
      functor : Functor C D

    open Functor functor public

    field
      F-+ : ∀ {a b} (f g : A.Hom a b) → F₁ (f A.+ g) ≡ F₁ f B.+ F₁ g
```

In passing we note that, since the $\hom$-abelian-groups are _groups_,
preservation of addition automatically implies preservation of the zero
morphism, preservation of inverses, and thus preservation of
subtraction.

```agda
    F-hom : ∀ {a b} → is-group-hom
      (Abelian→Group-on (A.Abelian-group-on-hom a b))
      (Abelian→Group-on (B.Abelian-group-on-hom _ _))
      F₁
    F-hom .is-group-hom.pres-⋆ = F-+

    F-0m : ∀ {a b} → F₁ {a} {b} A.0m ≡ B.0m
    F-0m = is-group-hom.pres-id F-hom

    F-diff : ∀ {a b} (f g : A.Hom a b) → F₁ (f A.- g) ≡ F₁ f B.- F₁ g
    F-diff _ _ = is-group-hom.pres-diff F-hom

    F-inv : ∀ {a b} (f : A.Hom a b) → F₁ (A.Hom.inverse f) ≡ B.Hom.inverse (F₁ f)
    F-inv _ = is-group-hom.pres-inv F-hom
```

Since the zero object $\emptyset$ in an $\Ab$-category is characterised
as the unique object having $\id[\emptyset] = 0$, and $\Ab$-functors
preserve both $\id$ and $0$, every $\Ab$-functor preserves zero objects.
We say that the zero object, considered as a colimit, is
**absolute**, i.e., preserved by every (relevant) functor.

```agda
Ab-functor-pres-∅
  : ∀ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    {A : Ab-category C} {B : Ab-category D}
  → (F : Ab-functor A B) (∅A : Zero C)
  → is-zero D (Ab-functor.F₀ F (Zero.∅ ∅A))
Ab-functor-pres-∅ {A = A} {B = B} F ∅A =
  id-zero→zero B $
    B.id     ≡˘⟨ F.F-id ⟩
    F.₁ A.id ≡⟨ ap F.₁ (is-contr→is-prop (Zero.has⊤ ∅A (Zero.∅ ∅A)) _ _) ⟩
    F.₁ A.0m ≡⟨ F.F-0m ⟩
    B.0m     ∎
  where
    module A = Ab-category A
    module B = Ab-category B
    module F = Ab-functor F
```
