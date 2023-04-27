<!--
```agda
open import Cat.Internal.Base

open import Cat.Instances.Sets
open import Cat.Instances.StrictCat
open import Cat.Prelude

import Cat.Strict.Reasoning
```
-->

```agda
module Cat.Internal.Sets where
```

# Internal categories in Set

Categories that are internal to set are [strict categories], IE:
precategories with a `Set`{.Agda ident=is-set} of objects.

[strict categories]: Cat.Instances.StrictCat.html

It is quite easy to show that internal categories yield strict
categories; the proof is mostly just shuffling data around.

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

The other direction is... not so easy.

```agda
Strict-cat→Internal-cat
  : ∀ {o ℓ}
  → (C : Precategory o ℓ) → is-set (Precategory.Ob C)
  → Internal-cat (Sets (o ⊔ ℓ))
Strict-cat→Internal-cat {o} {ℓ} C ob-set = icat where
  open Precategory C
  open Cat.Strict.Reasoning C ob-set
  open Internal-cat
  open Internal-cat-on
  open Internal-hom
  open Lift
```

<!--
```agda
  instance
    H-Level-Ob : ∀ {n} → H-Level Ob (2 + n)
    H-Level-Ob = basic-instance 2 ob-set
```
-->

The set of objects is straightforward: it's just the set of objects
(modulo universe levels). However, morphisms are a bit more tricky; we
need to create the type of *all* morphisms, which is kind of a pain to
work with.

```agda
  icat : Internal-cat (Sets (o ⊔ ℓ))
  icat .C₀ = el! (Lift ℓ Ob)
  icat .C₁ = el! (Σ[ x ∈ Ob ] Σ[ y ∈ Ob ] (Hom x y))
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

Composition is much worse. Note that the two morphisms we are trying
to compose are off by a path! This forces us to transport one of them,
which makes reasoning about the composition extremely annoying.

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

The internal category laws follow from the category laws, though there
are a bunch of transports we need to wade through.

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

Naturality is (luckily) quite simple.

```agda
  icat .has-internal-cat .idi-nat _ = refl
  icat .has-internal-cat .∘i-nat f g σ = funext λ γ →
    refl ,ₚ refl ,ₚ ap₂ _∘_ refl (recast-cod _ _)
```
