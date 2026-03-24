<!--
```agda
open import Cat.Functor.Naturality
open import Cat.Instances.Product
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as Fr
import Cat.Reasoning as Cat

open _=>_
```
-->

```agda
module Cat.Functor.Bifunctor where
```

# Bifunctors {defines="bifunctor"}

<!--
```agda
private
  variable
    o h o₁ h₁ o₂ h₂ o₃ h₃ : Level
    C D E : Precategory o₁ h₁
  module Cat[,] {o h o₁ h₁} {C : Precategory o h} {D : Precategory o₁ h₁} = Cat Cat[ C , D ]
```
-->

A **bifunctor** $F$ from $\cC$ and $\cD$ to $\cE$ is a functor of two
arguments. Traditionally, a bifunctor is defined as having its
**domain** be a [[product category]], so that $F$ would have type
$F : \cC \times \cD \to \cE$. In those terms, a bifunctor acts on both
of its arguments simultaneously, having a *single* action `_◆_`{.Agda}
on morphisms.

For technical reasons, we instead prefer to define bifunctors with a
[[functor category]] in their **codomain**, so that $F : \cC \to [\cD,
\cE]$. In these terms, we can evaluate $F$ at an object $a : \cC$ to get
a functor $F(a) : \cC \to \cE$, and evaluating *this* at $b : \cD$ gives
the action of $F$ on a pair of objects. The action of $F(a)$ on a
morphism $x \to y : \cD$ behaves as a "whiskering" operator, being a map
$F(a)(f) : F\ a\ x \to F\ a\ y$ which varies the second parameter, leaving $a$
fixed. The action of $F$ on a morphism $a \to b : \cD$ is a [[natural
transformation]] whose components, having type $F(f)(x) : F\ a\ x \to F\
b\ x$, generate the complementary whiskering operation.

```agda
Bifunctor : Precategory o h → Precategory o₁ h₁ → Precategory o₂ h₂ → Type _
Bifunctor C D E = Functor C Cat[ D , E ]
```

<!--
```agda
{-# DISPLAY Functor {o} {ℓ} {_} {_} C (Cat[_,_] {o₁} {ℓ₁} {o₂} {ℓ₂} D E) = Bifunctor {o} {ℓ} {o₁} {ℓ₁} {o₂} {ℓ₂} C D E #-}

module Bifunctor (F : Bifunctor C D E) where
  private
    module C = Precategory C
    module D = Precategory D
    module E = Cat E
    variable
      a b c d : ⌞ C ⌟
      w x y z : ⌞ D ⌟
```
-->

<details>
<summary>
More on the technical reasons.
</summary>

The mechanism Agda uses for reifying normal forms for display to the
user favours definitions that can be written entirely in terms of the
module system. If we defined bifunctors with a product argument, the
joint action on morphisms would be disqualified from being written
infix, since the module system provides no facility for currying a
function.

```agda
  private
    open module r₀ X = Functor (F .Functor.F₀ X) public
      renaming (F₁ to infix 35 _▶_) using (F₀)

    open module r₁ {a b} (f : C.Hom a b) = _=>_ (F .Functor.F₁ f) public
      renaming (η to infix 35 _◀_) using ()
```

Publicly opening private module aliases ensures that only the symbols
`F₀`{.Agda}, `_◀_`{.Agda}, and `_▶_`{.Agda} are in scope, but not the
intermediate modules `r₀`{.Agda} and `r₁`{.Agda}, ensuring that a term
like `f ◀ A` will not be recovered as `f r₁.◀ A`.

</details>

The rest of this module contains helpers for working with the two
functorial actions. First, we write two little helper functions that
allow eliding the "unchanging" argument of the whiskerings. The names
`lmap`{.Agda} and `rmap`{.Agda} are named **l**eft and **r**ight after
the direction of the triangles `_◀_`{.Agda} and `_▶_`{.Agda}.

```agda
  lmap : C.Hom a b → E.Hom (F₀ a x) (F₀ b x)
  lmap f = f ◀ _

  rmap : D.Hom x y → E.Hom (F₀ a x) (F₀ a y)
  rmap f = _ ▶ f
```

These operations are both functorial by themselves. For `rmap`{.Agda},
we show this by projecting from the functor $F(A)$. For `lmap`{.Agda},
functoriality of $F$ gives us a path of natural transformations, so we
must project the identity between the underlying maps as an additional
step.

```agda
  rmap-id : a ▶ D.id {x} ≡ E.id
  rmap-∘  : (f : D.Hom y z) (g : D.Hom x y) → a ▶ (f D.∘ g) ≡ (a ▶ f) E.∘ (a ▶ g)

  rmap-id = F .Functor.F₀ _ .Functor.F-id
  rmap-∘  = F .Functor.F₀ _ .Functor.F-∘

  lmap-id : C.id {a} ◀ x ≡ E.id
  lmap-∘  : (f : C.Hom b c) (g : C.Hom a b) → (f C.∘ g) ◀ x ≡ (f ◀ x) E.∘ (g ◀ x)

  lmap-id    = F .Functor.F-id     ·ₚ _
  lmap-∘ f g = F .Functor.F-∘  f g ·ₚ _
```

Finally, the naturality squares for each $F(f)$, pictured below, show
that `lmap`{.Agda} and `rmap`{.Agda} commute past eachother.

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  {F\ a\ x} \&\& {F\ a\ y} \\
  \\
  {F\ b\ x} \&\& {F\ b\ y}
  \arrow["{a \mathop{\triangleright} g}", from=1-1, to=1-3]
  \arrow["{f \mathop{\triangleleft} x}"', from=1-1, to=3-1]
  \arrow["{f \mathop{\triangleleft} y}", from=1-3, to=3-3]
  \arrow["{b \mathop{\triangleright} g}"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

```agda
  lrmap : ∀ f g → (f ◀ y) E.∘ (a ▶ g) ≡ (b ▶ g) E.∘ (f ◀ x)
  lrmap f g = F .Functor.F₁ f .is-natural _ _ g

  rlmap : ∀ g f → (b ▶ g) E.∘ (f ◀ x) ≡ (f ◀ y) E.∘ (a ▶ g)
  rlmap f g = sym (lrmap g f)
```

## Horizontal composition

A bifunctor provides two identical, but not definitionally equal, ways
of acting on both coordinates. For definiteness, we define the
**horizontal composition** operation to be the left-hand-side of
`lrmap`{.Agda}.

```agda
  _◆_ : ∀ {a b x y} → C.Hom a b → D.Hom x y → E.Hom (F · a · x) (F · b · y)
  _◆_ β α = (β ◀ _) E.∘ (_ ▶ α)
```

A pair of short calculations shows that this operation is "functorial in
both variables".

```agda
  ◆-id : ∀ {a x} → C.id {a} ◆ D.id {x} ≡ E.id
  ◆-id =
    C.id ◆ D.id               ≡⟨⟩
    (C.id ◀ _) E.∘ (_ ▶ D.id) ≡⟨ E.eliml lmap-id ⟩
    _ ▶ D.id                  ≡⟨ rmap-id ⟩
    E.id                      ∎

  ◆-∘
    : ∀ {a b c x y z}
    → {f : C.Hom b c} {g : C.Hom a b} {f' : D.Hom y z} {g' : D.Hom x y}
    → (f C.∘ g) ◆ (f' D.∘ g') ≡ (f ◆ f') E.∘ (g ◆ g')
  ◆-∘ {f = f} {g} {f'} {g'} =
    (f C.∘ g) ◆ (f' D.∘ g')                         ≡⟨⟩
    (f C.∘ g ◀ _) E.∘ (_ ▶ f' D.∘ g')               ≡⟨ ap₂ E._∘_ (lmap-∘ _ _) (rmap-∘ _ _) ⟩
    ((f ◀ _) E.∘ (g ◀ _)) E.∘ (_ ▶ f') E.∘ (_ ▶ g') ≡⟨ E.extendr (E.extendl (lrmap _ _)) ⟩
    ((f ◀ _) E.∘ (_ ▶ f')) E.∘ (g ◀ _) E.∘ (_ ▶ g') ≡⟨⟩
    (f ◆ f') E.∘ (g ◆ g')                           ∎
```

As special cases of functoriality, we recover the whiskerings as a
special case of horizontal composition.

```agda
  lmap-◆ : ∀ {a b x} (f : C.Hom a b) → f ◀ x ≡ f ◆ D.id
  lmap-◆ f = E.intror rmap-id

  rmap-◆ : ∀ {x y a} (f : D.Hom x y) → a ▶ f ≡ C.id ◆ f
  rmap-◆ f = E.introl lmap-id
```

## Associated functors

Evaluating $F$ at an object $a : \cC$ gives a functor $\cD \to \cE$, by
definition. Since this functor acts by `rmap`{.Agda}, we call this the
functor associated to $F$ on the `Right`{.Agda}.

```agda
  Right : C.Ob → Functor D E
  Right A = F .Functor.F₀ A
```

In the other direction, we must write out the functor $\cC \to \cE$
associated to $F$ on the `Left`{.Agda}, given an object $x : \cD$, in
components.

```agda
  Left : D.Ob → Functor C E
  Left X .Functor.F₀ A = F₀ A X
  Left X .Functor.F₁ f = f ◀ X
  Left X .Functor.F-id = lmap-id
  Left X .Functor.F-∘  = lmap-∘
```

<!--
```agda
  module ▶ {A} = Fr (Right A) hiding (F₀ ; F₁)
  module ◀ {A} = Fr (Left A)  hiding (F₀ ; F₁)
```
-->

By swapping the positions of `lmap`{.Agda} and `rmap`{.Agda}, we can
turn a bifunctor of $\cC$ and $\cD$ to $\cE$ into a bifunctor of $\cD$
and $\cC$ to $\cE$.

<!--
```agda
module _ {C : Precategory o h} {D : Precategory o₁ h₁} {E : Precategory o₂ h₂} where
  private
    module C = Precategory C
    module D = Precategory D
    module E = Precategory E

  record Make-bifunctor : Type (o ⊔ o₁ ⊔ o₂ ⊔ h ⊔ h₁ ⊔ h₂) where
    field
      F₀   : ⌞ C ⌟ → ⌞ D ⌟ → ⌞ E ⌟
      lmap : ∀ {a b x} → C.Hom a b → E.Hom (F₀ a x) (F₀ b x)
      rmap : ∀ {x y a} → D.Hom x y → E.Hom (F₀ a x) (F₀ a y)

      lmap-id : ∀ {a x} → lmap {a} {x = x} C.id ≡ E.id
      rmap-id : ∀ {x a} → rmap {x} {a = a} D.id ≡ E.id

      lmap-∘
        : ∀ {a b c x} (f : C.Hom b c) (g : C.Hom a b)
        → lmap {x = x} (f C.∘ g) ≡ lmap f E.∘ lmap g

      rmap-∘
        : ∀ {x y z a} (f : D.Hom y z) (g : D.Hom x y)
        → rmap {a = a} (f D.∘ g) ≡ rmap f E.∘ rmap g

      lrmap
        : ∀ {a b x y} (f : C.Hom a b) (g : D.Hom x y)
        → lmap f E.∘ rmap g ≡ rmap g E.∘ lmap f

  make-bifunctor : Make-bifunctor → Bifunctor C D E
  {-# INLINE make-bifunctor #-}
  make-bifunctor mm =
    record
      { F₀   = λ x → record
        { F₀   = mm.F₀ x
        ; F₁   = mm.rmap
        ; F-id = mm.rmap-id
        ; F-∘  = mm.rmap-∘
        }
      ; F₁   = λ x → record
        { η          = λ _     → mm.lmap x
        ; is-natural = λ x y z → mm.lrmap _ _
        }
      ; F-id = ext λ _ → mm.lmap-id
      ; F-∘  = λ f g → ext λ _ → mm.lmap-∘ _ _
      }
    where module mm = Make-bifunctor mm

module _ (F : Bifunctor C D E) where
  private open module F = Bifunctor F
  open Functor

  -- Defining Flip in components instead of using make-bifunctor avoids
  -- introducing a new "Flip.Right" which is distinct from Left.
  --
  -- This is basically the only avoidable case of generativity.
```
-->

```agda
  Flip : Bifunctor D C E
  Flip .F₀ = Left

  Flip .F₁ f .η A              = A ▶ f
  Flip .F₁ f .is-natural x y g = rlmap _ _

  Flip .F-id    = ext λ _ → rmap-id
  Flip .F-∘ f g = ext λ _ → rmap-∘ _ _
```

Finally, we can `Uncurry`{.Agda} $F$ into a functor $\cC \times \cD \to
\cE$, using the horizontal composition defined above.

```agda
  Uncurry : Functor (C ×ᶜ D) E
  Uncurry .F₀      = uncurry F.F₀
  Uncurry .F₁      = uncurry _◆_
  Uncurry .F-id    = ◆-id
  Uncurry .F-∘ _ _ = ◆-∘
```

<!--
```agda
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
    module F = Bifunctor F
    module G = Bifunctor G

    open _=>_

  module Binatural (eta : F => G) where
    abstract
      natural-◀ : ∀ {f : C.Hom a b} {x} → eta · _ · _ E.∘ (f F.◀ x) ≡ (f G.◀ x) E.∘ eta · _ · _
      natural-◀ = eta .is-natural _ _ _ ηₚ _

      natural-▶ : ∀ {a} {f : D.Hom x y} → eta · _ · _ E.∘ (a F.▶ f) ≡ (a G.▶ f) E.∘ eta · _ · _
      natural-▶ = eta .η _ .is-natural _ _ _

      natural-◆
        : ∀ {f : C.Hom a b} {g : D.Hom x y}
        → eta · _ · _ E.∘ (f F.◆ g) ≡ (f G.◆ g) E.∘ eta · _ · _
      natural-◆ = E.pulll natural-◀ ∙ E.extendr natural-▶

    private
      open module eta₁ a = _=>_ (eta .η a) public

    right : ∀ {x} → F.Right x => G.Right x
    right = eta .η _

    left : ∀ {x} → F.Left x => G.Left x
    left .η              x = eta .η _ .η _
    left .is-natural x y f = natural-◀

  open Binatural using (natural-◀ ; natural-▶ ; natural-◆) public

  biiso→isoⁿ
    : (i : ∀ x y → F · x · y E.≅ G · x · y)
    → (∀ {x y z} (f : C.Hom x y) → (f G.◀ z) E.∘ i x z .E.to ≡ i y z .E.to E.∘ (f F.◀ z))
    → (∀ {x y z} (f : D.Hom x y) → (z G.▶ f) E.∘ i z x .E.to ≡ i z y .E.to E.∘ (z F.▶ f))
    → F Cat[,].≅ G
  {-# INLINE biiso→isoⁿ #-}
  biiso→isoⁿ i n1 n2 = iso→isoⁿ
    (λ x → iso→isoⁿ (i x) λ {x y} f → n2 f)
    λ {x y} f → ext (λ z → n1 f)

  record Make-binatural : Type (o₁ ⊔ o₂ ⊔ h₁ ⊔ h₂ ⊔ h₃) where
    field
      η : (c : C.Ob) → (d : D.Ob) → E.Hom (F.F₀ c d) (G.F₀ c d)
      is-natural-◀
        : ∀ {c1 c2 : C.Ob} (f : C.Hom c1 c2) (d : D.Ob)
        → η c2 d E.∘ (f F.◀ d) ≡ (f G.◀ d) E.∘ η c1 d
      is-natural-▶
        : ∀ (c : C.Ob) {d1 d2 : D.Ob} (f : D.Hom d1 d2)
        → η c d2 E.∘ (c F.▶ f) ≡ (c G.▶ f) E.∘ η c d1

  make-binatural : Make-binatural → F => G
  {-# INLINE make-binatural #-}
  make-binatural mk =
    record
    { η = λ x → record
      { η = λ y → mk.η x y
      ; is-natural = λ y z f → mk.is-natural-▶ x f
      }
    ; is-natural = λ x y f → ext λ z → mk.is-natural-◀ f z
    }
    where module mk = Make-binatural mk
```
-->
