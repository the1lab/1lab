<!--
```agda
open import Cat.Bi.Lax-functor.Lax-transfor
open import Cat.Bi.Lax-functor.Modification
open import Cat.Bi.Instances.Lax-functor
open import Cat.Bi.Instances.Terminal
open import Cat.Bi.Lax-functor.Base
open import Cat.Functor.Bifunctor
open import Cat.Instances.Product
open import Cat.Functor.Constant
open import Cat.Bi.Duality
open import Cat.Bi.Solver
open import Cat.Bi.Base
open import Cat.Prelude hiding (_^op)

import Cat.Bi.Reasoning as Br
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Bi.Lax-functor.Constant where
```

# Constant pseudofunctors {defines="constant-pseudofunctor"}

A **constant pseudofunctor** from $\bf{B}$ to $\bf{C}$ sends every
object of $\bf{B}$ to a single object $c : \bf{C}$, every 1-cell of
$\bf{C}$ to the identity morphism on $c$, and every 2-cell of $\bf{C}$
to the identity morphism on that identity morphism.

<!--
```agda
private
  variable
    o o' h h' ℓ ℓ' : Level
    B C : Prebicategory o h ℓ

  module Pf = Pseudofunctor
  module Lf = Lax-functor

open Cr.is-invertible
open Lax-transfor
open Modification
open Cr.Inverses
open Functor
open _=>_
```
-->

As with [[constant functors]], we can characterise the constant
pseudofunctors as factorizations through the [[terminal bicategory]].

```agda
ConstP : (X : Prebicategory.Ob C) → Pseudofunctor B C
ConstP X = !ConstP X P∘ !P
```

Furthermore, given two bicategories $\bf{B}$ and $\bf{C}$, the
assignment sending an object $X$ to the constant functor at $X$ is
pseudofunctorial.

```agda
Const-pseudoₒ : Pseudofunctor C (Pseudoₒ B C)
Const-pseudoₒ {C = C} {B = B} = pf module Const-pseudoₒ where
```

In defining this pseudofunctor, there are multiple options for what the
codomain should be, depending on whether we want to consider lax, oplax,
or pseudonatural transformations.  All three are valid, but here we
demonstrate the oplax version.

<!--
TODO: Define this as a pseudofunctor into Pseudoₚ B C (after defining
the latter), and derive the lax and oplax versions using the inclusions
of Pseudoₚ B C into the lax/oplax pseudofunctor categories.

```agda
  open Prebicategory C
  private module CH {A} {B} = Cr (Hom A B)
```
-->

The 1-cell action of this pseudofunctor is also constant, sending a
morphism $f : X \to Y$ to the constant transformation between the
constant pseudofunctors at $X$ and $Y$ which is $f$ everywhere.

```agda
  Const₁ : ∀ {X Y} → Functor (Hom X Y) Pseudoₒ[ ConstP X , ConstP Y ]
  Const₁ .F₀ f .σ A                         = f
  Const₁ .F₀ f .naturator .η _              = λ→ _ ∘ ρ← _
  Const₁ .F₀ f .naturator .is-natural _ _ _ = bicat! C
  Const₁ .F₀ f .ν-compositor g h            = bicat! C
  Const₁ .F₀ f .ν-unitor                    = bicat! C
  Const₁ .F₁ α .Γ a                         = α
  Const₁ .F₁ α .is-natural                  = bicat! C
  Const₁ .F-id                              = ext λ _ → refl
  Const₁ .F-∘ f g                           = ext λ _ → refl
```

<details>
<summary>
Because everything in this construction is constant, the compositor and
unitors are just componentwise identities, but we need to pass through
some slight bureaucracy to show that this is valid.
</summary>

```agda
  compositor
    : ∀ {X Y Z}
    → Uncurry (Flip (Lax.compose (B ^op) (C ^op))) F∘ (Const₁ {Y} {Z} F× Const₁ {X} {Y})
    => Const₁ F∘ Uncurry compose
  compositor .η _ .Γ _               = CH.id
  compositor .η _ .is-natural        = bicat! C
  compositor .is-natural _ _ (f , g) = ext λ _ → CH.idl _
    ∙∙ ap₂ _∘_  (CH.eliml compose.▶.F-id) (CH.elimr compose.◀.F-id)
    ∙∙ sym (CH.idr _)

  compositor-inv
    : ∀ {X Y Z} fg
    → Cr.is-invertible Pseudoₒ[ ConstP X , ConstP Z ] (compositor {X} {Y} {Z} .η fg)
  compositor-inv (f , g) .inv .Γ _        = Hom.id
  compositor-inv (f , g) .inv .is-natural = bicat! C
  compositor-inv (f , g) .inverses .invl  = ext λ _ → Hom.idl _
  compositor-inv (f , g) .inverses .invr  = ext λ _ → Hom.idr _

  unitor : ∀ {X} → Modification idlx (Const₁ .F₀ (id {X}))
  unitor .Γ _        = Hom.id
  unitor .is-natural = bicat! C

  unitor-inv : ∀ {X} → Cr.is-invertible Pseudoₒ[ ConstP X , ConstP X ] (unitor {X})
  unitor-inv .inv .Γ _        = Hom.id
  unitor-inv .inv .is-natural = bicat! C
  unitor-inv .inverses .invl  = ext λ _ → Hom.idl _
  unitor-inv .inverses .invr  = ext λ _ → Hom.idr _
```
</details>

```agda
  lf : Lax-functor C (Pseudoₒ B C)
  lf .Lf.P₀ X          = ConstP X
  lf .Lf.P₁            = Const₁
  lf .Lf.compositor    = compositor
  lf .Lf.unitor        = unitor
  lf .Lf.hexagon f g h = ext λ _ →
      CH.elimr   (CH.idl _ ∙∙ CH.eliml compose.▶.F-id ∙∙ compose.◀.F-id)
    ∙ CH.insertl (CH.idl _ ∙∙ CH.eliml compose.▶.F-id ∙∙ compose.◀.F-id)
  lf .Lf.right-unit f = ext λ _ →
    CH.elimr (Hom.idl _ ∙∙ CH.eliml compose.▶.F-id ∙∙ compose.◀.F-id)
  lf .Lf.left-unit f = ext λ _ →
    CH.elimr (Hom.idl _ ∙∙ CH.eliml compose.▶.F-id ∙∙ compose.◀.F-id)

  pf : Pseudofunctor _ _
  pf .Pf.lax            = lf
  pf .Pf.unitor-inv     = unitor-inv
  pf .Pf.compositor-inv = compositor-inv
```
