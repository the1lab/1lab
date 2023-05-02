<!--
```agda
open import Cat.Displayed.Base
open import Cat.Displayed.Cartesian
open import Cat.Prelude
```
-->

```agda
module Cat.Displayed.GenericObject
  {o ℓ o' ℓ'} {B : Precategory o ℓ}
  (E : Displayed B o' ℓ')
  where
```

<!--
```agda
open Precategory B
open Displayed E
```
-->

# Generic Objects

There are 2 perspectives one can take on generic objects. The first is
a purely logical one: generic objects provide us a tool for giving
categorical models of higher order logics. The second perspective is
that generic objects are a categorical way of describing the size of
fibrations, and their ability to be internalized in the base category.
We shall use both perspectives interchangeably!

::: warning
The terminology surrounding generic objects is a bit of a disaster.
What we refer to as a generic object is referred to as a
*weak* generic object in [@Jacobs:2001]. However, we follow the
terminology set out in [@Sterling:2023], as generic objects in the sense
of Jacobs are quite rare.
:::

With that caveat out of the way, we define a generic object to be some
object $T : \cE_{U}$ with the property that for any $X' : \cE_{X}$, we
have a (not necessarily unique) cartesian map $X' \to T$.

```agda
record is-generic-object {t} (t′ : Ob[ t ]) : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
  field
    classify  : ∀ {x} → (x′ : Ob[ x ]) → Hom x t
    classify′ : ∀ {x} → (x′ : Ob[ x ]) → Hom[ classify x′ ] x′ t′
    classify-cartesian : ∀ {x} (x′ : Ob[ x ])
                       → is-cartesian E (classify x′) (classify′ x′)

  module classify-cartesian {x} (x′ : Ob[ x ]) = is-cartesian (classify-cartesian x′)
```

The intuition for this definition is that if $\cE$ has a generic object,
then every object of $\cE$ arises as a reindexing of $T$ along *some*
morphism in the base.

If we think of $\cE$ as some sort of logic over some syntactic category,
then a generic object behaves like $\mathrm{Prop}$, the type of
propositions. To see why, recall that an object $\cE_{\Gamma}$ over a
classifying category is a proposition in ranging over some free
variables of type $\Gamma$. The classifying map in the base yields a
substitution $\Gamma \to \mathrm{Prop}$, or in other words, a term of
type $\mathrm{Prop}$ in context $\Gamma$.  Furthermore, the classifying
map upstairs gives an implication between the original proposition in
$\cE_{\Gamma}$ and a proof of the corresponding element of $\mathrm{Prop}$.

The size-based perspective on generic objects hinges on the
fact that [the family fibration on $\cC$ has a generic object if and
only if $\cC$ is equivalent to a small, strict category][fam-generic].
Fibred structure in the family fibration corresponds to structure in
$\cC$, so we can see the generic objects as a generalization of both
a strictness and size condition.

[fam-generic]: Cat.Displayed.Instances.Family.html#generic-objects

With this size based perspective in mind, we say that a displayed
category is globally small if it has a generic object.

```agda
record Globally-small : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
  field
    {U} : Ob
    Gen : Ob[ U ]
    has-generic-ob : is-generic-object Gen

  open is-generic-object has-generic-ob public
```
