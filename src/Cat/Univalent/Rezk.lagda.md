```agda
open import Cat.Functor.FullSubcategory
open import Cat.Instances.Functor
open import Cat.Instances.Sets
open import Cat.Functor.Hom
open import Cat.Prelude

module Cat.Univalent.Rezk where
```

<!--
```agda
private variable
  o h o' h' : Level
open Precategory
open Functor
```
-->

# The Rezk completion

In the same way that we can [freely] [complete] a [proset] into a
[poset], it is possible to, in a universal way, replace any precategory
$\ca{A}$ by a category $\widehat{\ca{A}}$, such that there is a weak
equivalence (a [fully faithful], [essentially surjective] functor)
$\ca{A} \to \widehat{\ca{A}}$, such that any map from $\ca{A}$ to a
[univalent category] $\ca{C}$ factors uniquely through $\widehat{\ca{A}}$.

[freely]: Cat.Functor.Adjoint.html
[complete]: Cat.Thin.Completion.html
[proset]: Cat.Thin.html#thin-categories
[poset]: Cat.Thin.Completion.html#posets
[fully faithful]: Cat.Functor.Base.html#ff-functors
[essentially surjective]: Cat.Functor.Base.html#essential-fibres
[univalent category]: Cat.Univalent.html

The construction is essentially piecing together a handful of
pre-existing results: The univalence principle for $n$-types implies
that [Sets is a univalent category][setu], and [functor categories with
univalent codomain are univalent][funcu]; The [Yoneda lemma] implies
that any precategory $\ca{A}$ admits a [full inclusion] into
$[\ca{A}\op, \sets]$, and [full subcategories of univalent categories
are univalent][fullu] --- so, like Grothendieck cracking the nut, the
sea of theory has risen to the point where our result is trivial:

[setu]: Cat.Instances.Sets.html
[funcu]: Cat.Instances.Functor.html#functor-categories
[Yoneda lemma]: Cat.Functor.Hom.html#the-yoneda-embedding
[full inclusion]: Cat.Functor.FullSubcategory.html#from-full-inclusions
[fullu]: Cat.Functor.FullSubcategory.html#univalence

```agda
Rezk-completion : Precategory o h → Precategory (o ⊔ lsuc h) (o ⊔ h)
Rezk-completion A = Full-inclusion→Full-subcat {F = よ A} (よ-is-fully-faithful A)

Rezk-completion-is-category
  : ∀ {A : Precategory o h} → is-category (Rezk-completion A)
Rezk-completion-is-category {o} {h} {A} =
  Restrict-is-category _ (λ _ → squash)
    (Functor-is-category Sets-is-category)
```
