<!--
```agda
open import Cat.Prelude
```
-->

```agda
module Cat.Strict where
```

# Strict precategories {defines="strict-category strict-categories"}

::: {.popup .keep}
We call a precategory $\cC$ **strict** if its type of objects is a [[set]].

```agda
is-strict : ∀ {o ℓ} → Precategory o ℓ → Type o
is-strict C = is-set ⌞ C ⌟
```
:::

Strictness is a very strong condition to impose on categories, since it
classifies the "categories-as-algebras", or _petit_, view on categories,
which regards categories _themselves_ as set-level structures, which
could be compared to [[monoids]] or [[groups]]. For example, the [[free
category]] on a directed [[graph]] is naturally regarded as strict. Moreover,
[[strict categories form a precategory|category of strict categories]].

This is in contrast with the "categories-as-universes", or _gros_, view
on categories. From this perspective, categories serve to organise
objects at the set-level, like [$\thecat{Mon}$] or [$\Grp$]. These
categories tend to be [[univalent|univalent category]], with a proper
underlying _groupoid_ of objects.

[$\thecat{Mon}$]: Algebra.Monoid.Category.html
[$\Grp$]: Algebra.Group.Cat.Base.html
