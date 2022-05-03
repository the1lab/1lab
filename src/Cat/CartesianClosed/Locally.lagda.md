```agda
open import Cat.Functor.Adjoint.Compose
open import Cat.CartesianClosed.Base
open import Cat.Diagram.Limit.Finite
open import Cat.Functor.Bifunctor
open import Cat.Instances.Functor
open import Cat.Diagram.Pullback
open import Cat.Functor.Pullback
open import Cat.Diagram.Product
open import Cat.Functor.Adjoint
open import Cat.Instances.Slice
open import Cat.Prelude

import Cat.Reasoning

module Cat.CartesianClosed.Locally where
```

<!--
```agda
open /-Obj
open /-Hom
```
-->

# Locally Cartesian Closed Categories

A [finitely complete] category $\ca{C}$ is said to be **locally
Cartesian closed** when each of its [slice categories] is [Cartesian
closed]. In practice, though, it is easier to express this property in
terms of a certain family of functors existing.

[finitely complete]: Cat.Diagram.Limit.Finite.html
[slice categories]: Cat.Instances.Slice.html
[Cartesian closed]: Cat.CartesianClosed.Base.html

A [finitely complete] category $\ca{C}$ is **locally cartesian closed**
when each of its [base change] functors $f^* : \ca{C}/x \to \ca{C}/y$
admit a [right adjoint] $\prod_f : \ca{C}/y \to \ca{C}/x$, called the
**dependent sum**, thus extending the existing dependent sum-base change
adjunction to an adjoint triple

$$
\textstyle\sum_f \dashv f* \textstyle\prod_f
$$

[right adjoint]: Cat.Functor.Adjoint.html
[base change]: Cat.Functor.Pullback.html

```agda
record is-lcc {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ ℓ) where
  open Cat.Reasoning C

  field
    finitely-complete : Finitely-complete C

  open Finitely-complete finitely-complete public

  base-change : ∀ {a b} → Hom a b → Functor (Slice C b) (Slice C a)
  base-change = Base-change pullbacks

  field
    Πf    : ∀ {a b} → Hom a b → Functor (Slice C a) (Slice C b)
    f*⊣Πf : ∀ {a b} (f : Hom a b) → base-change f ⊣ Πf f
```

Note that the slices of a finitely complete category $\ca{C}$ are
automatically Cartesian categories, since products in $\ca{C}/a$ are
computed as pullbacks in $\ca{C}$.

```agda
  module /-Prods (a : Ob) = Cartesian (Slice C a)
    (λ A B → Pullback→Fibre-product (pullbacks (A .map) (B .map)))
```

## Internal homs

We now calculate that each slice of $\ca{C}$ is a [cartesian closed
category], by exhibiting a right adjoint each of their product functors.

[cartesian closed category]: Cat.CartesianClosed.Base.html

```agda
module _ {o ℓ} {C : Precategory o ℓ} (lcc : is-lcc C) where
  open Cat.Reasoning C
  open is-lcc lcc

  open Functor
  open is-cc

  private
    hom : ∀ {a} (f : Slice C a .Precategory.Ob) → Functor _ _
    hom f = Πf (f .map) F∘ base-change (f .map)

  is-lcc→slice-is-cc
    : ∀ {a : Ob}
    → is-cc (Slice C a)
        (λ A B → Pullback→Fibre-product (pullbacks (A .map) (B .map)))
  is-lcc→slice-is-cc .terminal = record
    { top  = cut (C .Precategory.id) ; has⊤ = Slice-terminal-object }
```

For a map $f : x \to a$, the internal hom functor $[f,-]$ in $\ca{C}/a$
is given by the composite

$$
\ca{C}/a \xto{f^*} \ca{C}/x \xto {\prod_f} \ca{C}/a
$$

```agda
  is-lcc→slice-is-cc .[_,-] f = hom f
```

To prove that this is a right adjoint, we use that [adjunctions compose]
and re-express the Cartesian product functor in $\ca{C}/a$ as the
composite

$$
\ca{C}/a \xto{f^*} \ca{C}/x \xto {\sum_f} \ca{C}/a
$$

We then have, since $\sum_f \dashv f^*$ and $f^* \dashv \prod_f$, the
adjunction $(\sum_f f^*) \dashv (\prod_f f^*)$.

[adjunctions compose]: Cat.Functor.Adjoint.Compose.html

```agda
  is-lcc→slice-is-cc {a = a} .tensor⊣hom f = adj where
    module f = /-Obj f

    -- The "good" cartesian product functor. The one we can piece
    -- together.
    tensor = Σf f.map F∘ base-change f.map
    tensor⊣hom′ : tensor ⊣ hom f
    tensor⊣hom′ = LF⊣GR (f*⊣Πf _) (Σf⊣f* pullbacks f.map)

    -- The product functor we have to give an adjoint to...
    product = Cartesian.×-functor (Slice C a) (λ A B → Pullback→Fibre-product (pullbacks (A .map) (B .map)))
    a×- = Left product f

    -- ... is the same that we already proved is left adjoint to hom!
    tensor-is-product : tensor ≡ a×-
    tensor-is-product = Functor-path p1 p2 where
      p1 : ∀ x → F₀ tensor x ≡ F₀ a×- x
      p1 x = /-Obj-path refl (sym (pullbacks (x .map) f.map .Pullback.square))

      p2 : ∀ {x y} (g : Slice C a .Precategory.Hom x y)
         → PathP (λ i → /-Hom (p1 x i) (p1 y i)) (F₁ tensor g) (F₁ a×- g)
      p2 {x} {y} g =
        /-Hom-pathp _ _ (Pullback.unique₂ (pullbacks (y .map) (f .map)) {p = path}
          (Pullback.p₁∘limiting (pullbacks _ _)) (Pullback.p₂∘limiting (pullbacks _ _))
          (Pullback.p₁∘limiting (pullbacks _ _)) (Pullback.p₂∘limiting (pullbacks _ _) ∙ idl _))
        where
          path =
            y .map ∘ g .map ∘ Pullback.p₁ (pullbacks _ _) ≡⟨ pulll (g .commutes) ⟩
            x .map ∘ Pullback.p₁ (pullbacks _ _)          ≡⟨ Pullback.square (pullbacks _ _) ⟩
            f .map ∘ Pullback.p₂ (pullbacks _ _)          ∎

    adj : a×- ⊣ hom f
    adj = subst (_⊣ hom f) tensor-is-product tensor⊣hom′
```
