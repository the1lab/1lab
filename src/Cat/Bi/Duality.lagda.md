<!--
```agda
open import Cat.Functor.Bifunctor.Duality
open import Cat.Functor.Naturality
open import Cat.Functor.Bifunctor
open import Cat.Bi.Functor.Base
open import Cat.Bi.Base
open import Cat.Prelude renaming (_^op to _^opᶜ)

import Cat.Bi.Reasoning as Br
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Bi.Duality where
```

# Duality in bicategories

A common theme in category theory is duality, and each category has a
[[formal opposite|opposite category]] given by reversing the direction
of all the morphisms.  The same holds in a [[bicategory]], but here we
have a bit more nuance: we could consider reversing either the 1-cells
or the 2-cells (or both).  Both of these yield valid constructions,
resulting in different flavours of duality.

<!--
```agda
private
  module Pb = Prebicategory
  variable
    o o' h h' ℓ ℓ' : Level

open Cr.is-invertible hiding (op)
open Pseudofunctor
open Cr.Inverses
open Lax-functor
open Functor renaming (op to opᶠ)
open Cr._≅_
open _=>_ renaming (op to opⁿ)

module _ (C : Prebicategory o h ℓ) where
  open make-natural-iso
  open Prebicategory C
  private
    module C  = Br C
    module CH = C.Hom
```
-->

## Opposite bicategories {defines="opposite-bicategory"}

Inverting the 1-cells of a bicategory $\bicat{C}$ gives an effect
similar to taking the opposite of a category, and can be used to express
contravariance in lax functors, for example.  We will refer to this as
the **opposite bicategory** $\bicat{C}\op$.

```agda
  infixl 60 _^op
  _^op : Prebicategory o h ℓ
  _^op .Pb.Ob      = Ob
  _^op .Pb.Hom x y = Hom y x
```

The identity in $\bicat{C}\op$ is inherited from $\bicat{C}$, while the
composition bifunctor is obtained by flipping the arguments to
$\bicat{C}$'s compositor.

```agda
  _^op .Pb.id      = id
  _^op .Pb.compose = Flip compose
```

The left unitor of $\bicat{C}\op$ is given by the right unitor of
$\bicat{C}$, and vice versa.

```agda
  _^op .Pb.unitor-l = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .eta           = ρ→
    ni .inv           = ρ←
    ni .eta∘inv _     = C.ρ≅ .invl
    ni .inv∘eta _     = C.ρ≅ .invr
    ni .natural _ _ _ = sym $ ρ→nat _
  _^op .Pb.unitor-r = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .eta           = λ→
    ni .inv           = λ←
    ni .eta∘inv _     = C.λ≅ .invl
    ni .inv∘eta _     = C.λ≅ .invr
    ni .natural _ _ _ = sym $ λ→nat _
```

Finally, the associator in $\bicat{C}\op$ is given by the inverse of the
associator of $\bicat{C}$.

```agda
  _^op .Pb.associator = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .eta _     = α← _
    ni .inv _     = α→ _
    ni .eta∘inv _ = C.α≅ .invr
    ni .inv∘eta _ = C.α≅ .invl
```

<details>
<summary>
To verify the naturality, we must shuffle some whiskerings around to
make their order match what the naturality square of of the associator
expects.
</summary>

```agda
    ni .natural _ _ _ =
         CH.car (CH.cdr (ap (C._◀ _) (compose.rlmap _ _)) ∙ compose.rlmap _ _)
      ∙∙ sym (α←nat _ _ _)
      ∙∙ CH.cdr (CH.cdr (ap (_ C.▶_) (compose.lrmap _ _)) ∙ compose.lrmap _ _)
```

</details>

The triangle and pentagon identities are obtained from those in
$\bicat{C}$ by inverting the associator.

```agda
  _^op .Pb.triangle f g     = C.triangle-α→
  _^op .Pb.pentagon f g h i = C.pentagon-α→
```

## Conjugate bicategories {defines="conjugate-bicategory"}

If we instead invert the 2-cells of a bicategory $\bicat{C}$, we get a
construction which we refer to as the **conjugate bicategory**, denoted
$\bicat{C}\co$. This notion serves to invert the directionality of
2-cells in constructions like lax functors and lax transformations: a
lax functor between conjugate categories has compositor and unitor
2-cells going in the opposite direction.

To achieve this 2-cell inversion, we let the $\hom$-category of
$\bicat{C}\co$ between objects $x$ and $y$ be given by the opposite
$\hom$-category $\hom(x,y)\op$.  Note that $x$ and $y$ retain their
original order, while the morphisms in the $\hom$-category (the 2-cells)
are reversed.

```agda
  infixl 60 _^co
  _^co : Prebicategory o h ℓ
  _^co .Pb.Ob      = Ob
  _^co .Pb.Hom x y = Hom x y ^opᶜ
```

The identity is again inherited from $\bicat{C}$, while the composition,
which must now act on the opposite $\hom$-categories, is given by the
[[opposite|opposite bifunctor]] of the composition in $\bicat{C}$.

```agda
  _^co .Pb.id      = id
  _^co .Pb.compose = bop compose
```

In the conjugate bicategory, the unitors and associator must go in the
opposite direction, which we achieve by taking their inverses.

```agda
  _^co .Pb.unitor-l = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .eta           = λ←
    ni .inv           = λ→
    ni .eta∘inv _     = C.λ≅ .invl
    ni .inv∘eta _     = C.λ≅ .invr
    ni .natural _ _ _ = λ←nat _
  _^co .Pb.unitor-r = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .eta           = ρ←
    ni .inv           = ρ→
    ni .eta∘inv _     = C.ρ≅ .invl
    ni .inv∘eta _     = C.ρ≅ .invr
    ni .natural _ _ _ = ρ←nat _
  _^co .Pb.associator = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .eta           = α←
    ni .inv           = α→
    ni .eta∘inv _     = C.α≅ .invl
    ni .inv∘eta _     = C.α≅ .invr
```

<details>
<summary>
To verify the naturality of the associator, we must again shuffle some
whiskerings.
</summary>

```agda
    ni .natural _ _ _ =
         CH.cdr (CH.car (ap (_ C.▶_) (compose.rlmap _ _)) ∙ compose.rlmap _ _)
      ∙∙ α←nat _ _ _
      ∙∙ CH.car (CH.car (ap (C._◀ _) (compose.lrmap _ _)) ∙ compose.lrmap _ _)
```

</details>

The triangle and pentagon identities are given by inverting both sides
in the corresponding equations for $\bicat{C}$.

```agda
  _^co .Pb.triangle f g     = C.Hom.lswizzle (sym C.triangle-inv) (C.α≅ .invl)
  _^co .Pb.pentagon _ _ _ _ = sym (Hom.assoc _ _ _) ∙ C.pentagon-α→
```

## Duality in lax functors and pseudofunctors {defines="opposite-lax-functor conjugate-pseudofunctor"}

<!--
```agda
module _ {B : Prebicategory o h ℓ} {C : Prebicategory o' h' ℓ'} where
  private
    module B = Br B
    module C = Br C

    open C.Hom

  module _ (F : Lax-functor B C) where
    private module F = Lf-reasoning F
```
-->

As with functors, lax functors have duals going between the opposite
categories.  The compositor of the opposite functor is given by flipping
the original compositor, and the hexagon diagram can be reordered
accordingly.

```agda
    opˡ : Lax-functor (B ^op) (C ^op)
    opˡ .P₀ = F.P₀
    opˡ .P₁ = F.P₁
    opˡ .compositor .η (f , g)        = F.γ→ (g , f)
    opˡ .compositor .is-natural _ _ f =
      cdr (C.⊗.rlmap _ _) ∙∙ F.γ→nat _ _ ∙∙ car F.P₁.⟨ B.⊗.lrmap _ _ ⟩
    opˡ .unitor = F.unitor
    opˡ .hexagon f g h = swizzle (sym (F.hexagon h g f ∙ assoc _ _ _))
        C.α≅.invl (F.P₁.F-map-iso B.α≅ .invr)
      ∙ sym (assoc _ _ _)
    opˡ .right-unit = F.left-unit
    opˡ .left-unit  = F.right-unit
```

On the other hand, there is no good notion of a "conjugate dual" from
$\bicat{B}\co$ to $\bicat{C}\co$ for a lax functor: we would need to
invert the directions of the compositor and unitor, but for a lax
functor, this is not possible.  On the other hand, for pseudofunctors we
get both flavors of duals.

<!--
```agda
  module _ (F : Pseudofunctor B C) where
    private module F = Pf-reasoning F
```
-->

```agda
    opᵖ : Pseudofunctor (B ^op) (C ^op)
    opᵖ .lax                    = opˡ (F .lax)
    opᵖ .unitor-inv             = F.unitor-inv
    opᵖ .compositor-inv (f , g) = F.compositor-inv (g , f)
```

The conjugate dual of a pseudofunctor $F$ acts the same as $F$ on
objects, but its action on $\hom$-categories is given by the opposite of
$F$'s action.

```agda
    co : Pseudofunctor (B ^co) (C ^co)
    co .lax .P₀ = F.P₀
    co .lax .P₁ = F.P₁.op
```

Since $F$ is a pseudofunctor, we can use the inverse compositor and
unitor in the conjugate construction.

```agda
    co .lax .compositor .η                = F.γ←
    co .lax .compositor .is-natural _ _ _ =
      car (C.⊗.rlmap _ _) ∙∙ sym (F.γ←nat _ _) ∙∙ cdr F.P₁.⟨ B.⊗.lrmap _ _ ⟩
    co .lax .unitor = F.υ←
```

<details>
<summary>
For the hexagon and unit identities, we invert the equations of $F$.
The details are hidden in the block below.
</summary>

```agda
    co .lax .hexagon f g h = inverse-unique refl refl
      (F.P₁.F-map-iso B.α≅ ∘Iso F.γ≅ ∘Iso C.◀.F-map-iso F.γ≅)
      (F.γ≅ ∘Iso C.▶.F-map-iso F.γ≅ ∘Iso C.α≅)
      (F.hexagon f g h)
    co .lax .right-unit f = inverse-unique refl refl
      (F.P₁.F-map-iso B.ρ≅ Iso⁻¹ ∘Iso F.γ≅ ∘Iso C.▶.F-map-iso F.υ≅)
      (C.ρ≅ Iso⁻¹) (F.right-unit f)
    co .lax .left-unit f  = inverse-unique refl refl
      (F.P₁.F-map-iso B.λ≅ Iso⁻¹ ∘Iso F.γ≅ ∘Iso C.◀.F-map-iso F.υ≅)
      (C.λ≅ Iso⁻¹) (F.left-unit f)
    co .unitor-inv .inv                   = F.υ→
    co .unitor-inv .inverses .invl        = F.unitor-inv .inverses .invl
    co .unitor-inv .inverses .invr        = F.unitor-inv .inverses .invr
    co .compositor-inv fg .inv            = F.γ→ fg
    co .compositor-inv fg .inverses .invl = F.compositor-inv fg .inverses .invl
    co .compositor-inv fg .inverses .invr = F.compositor-inv fg .inverses .invr
```

</details>

## Oplax functors and transformations {defines="oplax-functor oplax-transformation"}

While a lax functor has no inherent conjugate dual, we can still
consider lax functors between the conjugate categories.  As mentioned,
these are lax functors whose compositor and unitor 2-cells run in the
opposite direction.  We refer to these as **oplax functors**.

```agda
Oplax-functor : Prebicategory o h ℓ → Prebicategory o' h' ℓ' → Type _
Oplax-functor B C = Lax-functor (B ^co) (C ^co)
```

We can also consider lax transformations whose 2-cells run in the
opposite direction, as follows.  We refer to these as **oplax
transformations**.

```agda
module _ {B : Prebicategory o h ℓ} {C : Prebicategory o' h' ℓ'} where
  _=>ₒ_ : Lax-functor (B ^op) (C ^op) → Lax-functor (B ^op) (C ^op) → Type _
  F =>ₒ G = G =>ₗ F
```

In words, we define an oplax transformation from $F$ to $G$ to be a lax
transformation from $G$ to $F$ (reversing the direction of both 1-cells
and 2-cells), but in the opposite bicategories (which restores the
direction of the 1-cells).

Note that because oplax functors have conjugated domains and codomains,
lax transformations between them are "natively" inverted at the level of
2-cells.  In other words, a lax transformation of oplax functors runs in
the same direction as an oplax transformation of lax functors, while an
oplax transformation of oplax functors runs in the same direction as a
lax transformation of lax functors.
