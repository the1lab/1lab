<!--
```agda
open import Cat.Internal.Base
open import Cat.Prelude

import Cat.Strict.Reasoning
```
-->

```agda
module Cat.Internal.Sets where
```

# Internal categories in Set

Categories that are internal to set are [[strict categories]]:
precategories with a `Set`{.Agda ident=is-set} of objects. Starting from
a category $\bC$ internal to $\Sets$ and ending up with a strict
category is quite unremarkable:

```agda
Internal-cat→Precategory : ∀ {κ} → Internal-cat (Sets κ) → Precategory κ κ
Internal-cat→Precategory {κ} ℂ = cat where
  open Internal-cat ℂ
  open Internal-hom
  open Precategory

  cat : Precategory _ _
  cat .Ob = ∣ C₀ ∣
  cat .Hom x y = Homi {C₀} (λ _ → x) λ _ → y
  cat .Hom-set _ _ = Internal-hom-set (Sets κ)
  cat .id = idi _
  cat ._∘_ = _∘i_
  cat .idr f = Internal-hom-path _ (ap ihom (idri f))
  cat .idl f = Internal-hom-path _ (ap ihom (idli f))
  cat .assoc f g h = Internal-hom-path _ (ap ihom (associ f g h))
```

Defining an internal category from a strict category is a lot more
annoying.

```agda
Strict-cat→Internal-cat
  : ∀ {o ℓ}
  → (C : Precategory o ℓ)
  → is-set ⌞ C ⌟
  → Internal-cat (Sets (o ⊔ ℓ))
Strict-cat→Internal-cat {o} {ℓ} C ob-set = icat where
```

<!--
```agda
  open Precategory C
  open Cat.Strict.Reasoning C ob-set
  open Internal-cat
  open Internal-cat-on
  open Internal-hom
  open Lift
  instance
    H-Level-Ob : ∀ {n} → H-Level Ob (2 + n)
    H-Level-Ob = basic-instance 2 ob-set
```
-->

The object-of-objects is straightforward to define, since we already
assumed that the category we're internalising has a set of objects.
Morphisms are a bit more complicated. Since an internal category has a
single object-of-morphisms, we have to work with the total space of
$\cC(-,-)$, rather than any particular fibre.

```agda
  icat : Internal-cat (Sets (o ⊔ ℓ))
  icat .C₀ = el! (Lift ℓ Ob)
  icat .C₁ = el! (Σ[ x ∈ C ] Σ[ y ∈ C ] (Hom x y))
  icat .src (x , _ , _) = lift x
  icat .tgt (_ , y , _) = lift y
```

The internal identity morphism is simply the identity morphism.

```agda
  icat .has-internal-cat .idi x .ihom γ =
    lower (x γ) , lower (x γ) , id
  icat .has-internal-cat .idi x .has-src = refl
  icat .has-internal-cat .idi x .has-tgt = refl
```

Composition is where the complication shows up. Rather than composing
two arrows $f : x \to y$ and $g : y \to z$, we have to compose arrows $f
: x \to y$, $g : y' \to z$, _and_ a path $y = y'$. This forces us to
transport $f$, which gunks up the computations.

```agda
  icat .has-internal-cat ._∘i_ f g .ihom γ =
    g .ihom γ .fst ,
    f .ihom γ .snd .fst ,
    f .ihom γ .snd .snd
    ∘ cast-cod (ap lower (g .has-tgt $ₚ γ ∙ sym (f .has-src $ₚ γ)))
      (g .ihom γ .snd .snd)
  icat .has-internal-cat ._∘i_ f g .has-src = g .has-src
  icat .has-internal-cat ._∘i_ f g .has-tgt = f .has-tgt
```

As mentioned, establishing the laws is slightly hampered by the stuck
transports.

```agda
  icat .has-internal-cat .idli f =
    Internal-hom-path _ $
    funext λ γ →
    refl ,ₚ ap lower (sym (f .has-tgt $ₚ γ)) ,ₚ
    to-pathp⁻ (idl _ ∙ recast-cod _ _)
  icat .has-internal-cat .idri f =
    Internal-hom-path _ $
    funext λ γ →
    ap lower (sym (f .has-src $ₚ γ)) ,ₚ refl ,ₚ
    to-pathp⁻ (cast-cod-idr _ _ ∙ recast-dom _ _)
  icat .has-internal-cat .associ f g h =
    Internal-hom-path _ $
    funext λ γ →
    refl ,ₚ refl ,ₚ ap₂ _∘_ refl (cast-cod-∘ _) ∙ assoc _ _ _
```

Fortunately, naturality does not get too far in the way.

```agda
  icat .has-internal-cat .idi-nat _ =
    Internal-hom-path _ refl
  icat .has-internal-cat .∘i-nat f g σ =
    Internal-hom-path _ $
    funext λ γ →
    refl ,ₚ refl ,ₚ ap₂ _∘_ refl (recast-cod _ _)
```
