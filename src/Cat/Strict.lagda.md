<!--
```agda
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Strict where
```

# Strict Precategories

We call a precategory **strict** if it's space of objects is a
`Set`{.Agda ident=is-set}.j

```agda
is-strict : ∀ {o ℓ} → Precategory o ℓ → Type o
is-strict C = is-set (Precategory.Ob C)
```

Strictness is quite a strong condition, and rules out many naturally
occurring categories (for instance, the category of sets), as they
are too homotopically interesting. However, this lack of higher
dimensional structure does have its benefits: for instance,
[strict categories form a precategory][strcat].

[strcat]: Cat.Instances.StrictCat.html
