<!--
```agda
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Groupoid where
```

# Groupoids {defines="pregroupoid"}

A category $\cC$ is a (pre)**groupoid** if every morphism of $\cC$ is
invertible.

```agda
is-pregroupoid : ∀ {o ℓ} → Precategory o ℓ → Type (o ⊔ ℓ)
is-pregroupoid C = ∀ {x y} (f : Hom x y) → is-invertible f
  where open Cat.Reasoning C
```

<!--
```agda
module is-pregroupoid {o ℓ} {C : Precategory o ℓ} (gpd : is-pregroupoid C) where
  open Cat.Reasoning C

  hom→iso : ∀ {x y} → Hom x y → x ≅ y
  hom→iso f = invertible→iso f (gpd f)
```
-->
