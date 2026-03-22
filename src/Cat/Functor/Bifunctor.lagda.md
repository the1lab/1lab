<!--
```agda
open import Cat.Instances.Product
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Functor.Bifunctor where
```

# Bifunctors

<!--
```agda
module Bifunctor
  {o₁ h₁ o₂ h₂ o₃ h₃ : _}
  {C : Precategory o₁ h₁}
  {D : Precategory o₂ h₂}
  {E : Precategory o₃ h₃}
  (F : Bifunctor C D E)
  where
  private
    module C = Precategory C
    module D = Precategory D
    module E = Cat E
    variable
      a b c d : ⌞ C ⌟
      w x y z : ⌞ D ⌟

  open Functor F renaming (F₀ to Right) using () public
  module _ X where open Functor (F .Functor.F₀ X) renaming (F₁ to infix 35 _▶_) using (F₀) public
  module _ {a b} (g : C.Hom a b) where open _=>_ (F .Functor.F₁ g) renaming (η to infix 35 _◀_) using () public
```
-->

```agda
  lmap : ∀ {a b x} → C.Hom a b → E.Hom (F₀ a x) (F₀ b x)
  lmap f = f ◀ _

  rmap : ∀ {x y a} → D.Hom x y → E.Hom (F₀ a x) (F₀ a y)
  rmap f = _ ▶ f
```

These operations behave functorially by themselves, and you can "push
second past first".

```agda
  rmap-id : ∀ {x a} → rmap {x} {a = a} D.id ≡ E.id
  rmap-id = F .Functor.F₀ _ .Functor.F-id

  rmap-∘
    : ∀ {x y z a} (f : D.Hom y z) (g : D.Hom x y)
    → rmap {a = a} (f D.∘ g) ≡ rmap f E.∘ rmap g
  rmap-∘ = F .Functor.F₀ _ .Functor.F-∘

  lmap-id : ∀ {a x} → lmap {a} {x = x} C.id ≡ E.id
  lmap-id = F .Functor.F-id ·ₚ _

  lmap-∘
    : ∀ {a b c x} (f : C.Hom b c) (g : C.Hom a b)
    → lmap {x = x} (f C.∘ g) ≡ lmap f E.∘ lmap g
  lmap-∘ f g = F .Functor.F-∘ f g ·ₚ _

  lrmap
    : ∀ {a b x y} (f : C.Hom a b) (g : D.Hom x y)
    → lmap f E.∘ rmap g ≡ rmap g E.∘ lmap f
  lrmap f g = F .Functor.F₁ f ._=>_.is-natural _ _ g

  rlmap
    : ∀ {a b x y} (g : D.Hom x y) (f : C.Hom a b)
    → rmap g E.∘ lmap f ≡ lmap f E.∘ rmap g
  rlmap f g = sym (lrmap g f)
```

```agda
  _◆_ : ∀ {a b x y} → C.Hom a b → D.Hom x y → E.Hom (F · a · x) (F · b · y)
  _◆_ β α = lmap β E.∘ rmap α

  ◆-id : ∀ {a x} → C.id {a} ◆ D.id {x} ≡ E.id
  ◆-id = E.eliml lmap-id ∙ rmap-id

  ◆-∘
    : ∀ {a b c x y z} {f : C.Hom b c} {g : C.Hom a b} {f' : D.Hom y z} {g' : D.Hom x y}
    → (f C.∘ g) ◆ (f' D.∘ g') ≡ (f ◆ f') E.∘ (g ◆ g')
  ◆-∘ = ap₂ E._∘_ (lmap-∘ _ _) (rmap-∘ _ _) ∙ E.extendr (E.extendl (lrmap _ _))

  lmap-◆ : ∀ {a b x} (f : C.Hom a b) → f ◀ x ≡ f ◆ D.id
  lmap-◆ f = E.intror rmap-id

  rmap-◆ : ∀ {x y a} (f : D.Hom x y) → a ▶ f ≡ C.id ◆ f
  rmap-◆ f = E.introl lmap-id
```

Fixing an object in either of the categories gives us a functor which
varies in the other category.

```agda
  Left : D.Ob → Functor C E
  Left X .Functor.F₀ A = F₀ A X
  Left X .Functor.F₁ f = f ◀ X
  Left X .Functor.F-id = lmap-id
  Left X .Functor.F-∘  = lmap-∘

  Flip : Bifunctor D C E
  Flip = make-bifunctor record
    { F₀      = flip F₀
    ; lmap    = rmap
    ; rmap    = lmap
    ; lmap-id = rmap-id
    ; rmap-id = lmap-id
    ; lmap-∘  = rmap-∘
    ; rmap-∘  = lmap-∘
    ; lrmap   = λ f g → sym (lrmap g f)
    }

  Uncurry : Functor (C ×ᶜ D) E
  Uncurry .Functor.F₀      = uncurry F₀
  Uncurry .Functor.F₁      = uncurry _◆_
  Uncurry .Functor.F-id    = ◆-id
  Uncurry .Functor.F-∘ _ _ = ◆-∘
```

<!--
```agda
open Bifunctor using (Flip ; Uncurry) public

module
  _ {o₁ h₁ o₂ h₂ o₃ h₃ : _}
  {C : Precategory o₁ h₁}
  {D : Precategory o₂ h₂}
  {E : Precategory o₃ h₃}
  {F G : Bifunctor C D E}
  where

  private
    module C = Precategory C
    module D = Precategory D
    module E = Cat E
    variable
      a b c d : ⌞ C ⌟
      w x y z : ⌞ D ⌟
    module F = Bifunctor F using (_◀_ ; _▶_ ; _◆_)
    module G = Bifunctor G using (_◀_ ; _▶_ ; _◆_)

    open _=>_

    {-
    This is a pretty evil hack to support using natural-◀ and friends
    with postfix syntax.

    Elaboration for postfix dot remembers (and depends on) whether a
    copy is of a proper projection, so by shoving them into an arbitrary
    record (which doesn't even have to be exported) before putting them
    in the helper module, we can pretend that they're fields.
    -}

    record bifunctor-nat (eta : F => G) : Type (o₁ ⊔ o₂ ⊔ h₁ ⊔ h₂ ⊔ h₃) where
      field
        natural-◀ : ∀ {f : C.Hom a b} {x} → eta · _ · _ E.∘ (f F.◀ x) ≡ (f G.◀ x) E.∘ eta · _ · _
        natural-▶ : ∀ {a} {f : D.Hom x y} → eta · _ · _ E.∘ (a F.▶ f) ≡ (a G.▶ f) E.∘ eta · _ · _
        natural-◆
          : ∀ {f : C.Hom a b} {g : D.Hom x y}
          → eta · _ · _ E.∘ (f F.◆ g) ≡ (f G.◆ g) E.∘ eta · _ · _

    bifunctor-nat-impl : ∀ x → bifunctor-nat x
    bifunctor-nat-impl eta = record
      { natural-◀ = eta .is-natural _ _ _ ηₚ _
      ; natural-▶ = eta .η _ .is-natural _ _ _
      ; natural-◆ = E.pulll (eta .is-natural _ _ _ ηₚ _) ∙ E.extendr (eta .η _ .is-natural _ _ _)
      }

  module Binatural (eta : F => G) where
    open bifunctor-nat (bifunctor-nat-impl eta) public
    private
      module eta₀ = _=>_ eta
      open module eta₁ a = _=>_ (eta .η a) public

  open Binatural using (natural-◀ ; natural-▶ ; natural-◆) public
```
-->
