<!--
```agda
open import Cat.Bi.Lax-functor.Lax-transfor
open import Cat.Bi.Lax-functor.Modification
open import Cat.Functor.Naturality
open import Cat.Functor.Bifunctor
open import Cat.Instances.Product
open import Cat.Bi.Duality
open import Cat.Bi.Solver
open import Cat.Bi.Base
open import Cat.Prelude hiding (_^op)

import Cat.Bi.Reasoning as Br
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Bi.Instances.Lax-functor where
```

# Lax functor bicategories

We have seen that [[lax (and pseudonatural) transformations|lax
transformation]] give a meaningful notion of morphism between [[lax
functors]], and that [[modifications]] give a notion of morphisms
between lax transformations.  We've also done the work to show that [lax
transformations compose], and [similarly for modifications].

[lax transformations compose]: Cat.Bi.Lax-functor.Lax-transfor.html
[similarly for modifications]: Cat.Bi.Lax-functor.Modification.html

Now we can assemble these observations to state that the lax functors
between bicategories $\bf{C}$ and $\bf{D}$ themselves form a bicategory
$[\bf{C},\bf{D}]$, where objects are lax functors, 1-cells are lax
transformations, and 2-cells are modifications.  In fact, we get
multiple variations of this construction, since we can consider lax
functors, pseudofunctors, or [[oplax functors]] as objects, and lax
transformations, pseudonatural transformations, or [[oplax
transformations]] as 1-cells.  Here, we consider lax functors together
with lax and oplax transformations, and pseudofunctors with lax and
oplax transformations, respectively.

<!--
TODO: Define versions with pseudonatural transformations as full
subcategories of the lax ones.
-->

<!--
```agda
open Pseudofunctor
open Cr.Inverses
open Functor
open Cr._≅_
open _=>_

private
  module Pc = Precategory
  module Pb = Prebicategory
  variable
    o o' h h' ℓ ℓ' : Level
    B C : Prebicategory o h ℓ
```
-->

## Categories of lax transformations

For a pair of lax functors, the lax transformations between them and
modifications between those, form a category.  We have already done most
of the work required to define this category.

```agda
Laxₗ[_,_] : Lax-functor B C → Lax-functor B C → Precategory _ _
Laxₗ[_,_] F G .Pc.Ob                  = F =>ₗ G
Laxₗ[_,_] F G .Pc.Hom                 = Modification
Laxₗ[_,_] F G .Pc.Hom-set _ _         = Mod-is-set
Laxₗ[_,_] F G .Pc.id                  = idmd
Laxₗ[_,_] F G .Pc._∘_                 = _∘md_
Laxₗ[_,_] {C = C} F G .Pc.idr _       = ext λ _ → Pb.Hom.idr C _
Laxₗ[_,_] {C = C} F G .Pc.idl _       = ext λ _ → Pb.Hom.idl C _
Laxₗ[_,_] {C = C} F G .Pc.assoc _ _ _ = ext λ _ → Pb.Hom.assoc C _ _ _
```

We also get a category of lax functors and oplax transformations, using
the observation that an oplax transformation is the same as a lax
transformation in the opposite direction in the [[opposite
bicategories]].

```agda
Laxₒ[_,_]
  : Lax-functor (B ^op) (C ^op) → Lax-functor (B ^op) (C ^op) → Precategory _ _
Laxₒ[ F , G ] = Laxₗ[ G , F ]
```

For two pseudofunctors, we get categories of (op-)lax transformations
between them by the same construction as above.

```agda
Pseudoₗ[_,_] : Pseudofunctor B C → Pseudofunctor B C → Precategory _ _
Pseudoₗ[ F , G ] = Laxₗ[ F .lax , G .lax ]

Pseudoₒ[_,_]
  : Pseudofunctor (B ^op) (C ^op) → Pseudofunctor (B ^op) (C ^op) → Precategory _ _
Pseudoₒ[ F , G ] = Laxₒ[ F .lax , G .lax ]
```

## Bicategories of lax functors

Finally, we can bring the pieces together to form the bicategory of lax
functors and lax transformations.

```agda
Laxₗ : Prebicategory o h ℓ → Prebicategory o' h' ℓ' → Prebicategory _ _ _
Laxₗ B C = pb module Lax where
```

<!--
```agda
  private
    module C  = Br C
    module CH = C.Hom
  open Make-bifunctor
  open Lax-transfor
  open Modification
```
-->

The composition functor maps two lax transformation to their composite,
and acts on modifications by horizontal composition (or whiskering).

```agda
  compose
    : {F G H : Lax-functor B C}
    → Bifunctor Laxₗ[ G , H ] Laxₗ[ F , G ] Laxₗ[ F , H ]
  compose = make-bifunctor mk where
    mk : Make-bifunctor
    mk .F₀ α β     = α ∘lx β
    mk .lmap f     = f ◆md idmd
    mk .rmap g     = idmd ◆md g
```

<details>
<summary>
We elide the routine verification that this construction is functorial.
</summary>

```agda
    mk .lmap-id    = ext λ _ → C.⊗.◆-id
    mk .rmap-id    = ext λ _ → C.⊗.◆-id
    mk .lmap-∘ f g = ext λ _ → CH.pushl C.◀-distribl ∙ CH.car (CH.intror C.▶.F-id)
    mk .rmap-∘ f g = ext λ _ → CH.pushr C.▶-distribr ∙ CH.cdr (CH.introl C.◀.F-id)
    mk .lrmap f g  = ext λ _ →
         ap₂ C._∘_ (sym (C.⊗.lmap-◆ _)) (sym (C.⊗.rmap-◆ _))
      ∙∙ C.⊗.lrmap _ _
      ∙∙ ap₂ C._∘_ (C.⊗.rmap-◆ _) (C.⊗.lmap-◆ _)
```
</details>

The left unitor in our bicategory should be a natural family of
invertible modifications $\id \To \alpha \id$.  Since $\alpha \id$ is
given componentwise by $\alpha_a \id$ at each $a \in \bf{C}$, we can
build a modification by taking the unitor $\lambda_{\alpha_a}$ of
$\bf{C}$ at each component.

```agda
  unitor-l : ∀ {F G} → Id ≅ⁿ Bifunctor.Right (compose {F = F} {G}) idlx
  unitor-l = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta α .Γ a        = C.λ→ (σ α a)
    ni .make-natural-iso.eta α .is-natural = bicat! C
    ni .make-natural-iso.inv α .Γ a        = C.λ← (σ α a)
    ni .make-natural-iso.inv α .is-natural = bicat! C
    ni .make-natural-iso.eta∘inv α         = ext λ _ → C.λ≅ .invl
    ni .make-natural-iso.inv∘eta α         = ext λ _ → C.λ≅ .invr
    ni .make-natural-iso.natural _ _ _     = ext λ _ →
      CH.car (sym (C.⊗.rmap-◆ _)) ∙ sym (C.λ→nat _)
```

<details>
<summary>
The right unitor and associator are analogous, and we fold them into
this `<details>`{.html}-block.
</summary>
```agda
  unitor-r : ∀ {F G} → Id ≅ⁿ Bifunctor.Left (compose {G = F} {G}) idlx
  unitor-r = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta α .Γ a        = C.ρ→ (σ α a)
    ni .make-natural-iso.eta α .is-natural = bicat! C
    ni .make-natural-iso.inv α .Γ a        = C.ρ← (σ α a)
    ni .make-natural-iso.inv α .is-natural = bicat! C
    ni .make-natural-iso.eta∘inv α         = ext λ _ → C.ρ≅ .invl
    ni .make-natural-iso.inv∘eta α         = ext λ _ → C.ρ≅ .invr
    ni .make-natural-iso.natural _ _ _     = ext λ _ →
      CH.car (sym (C.⊗.lmap-◆ _)) ∙ sym (C.ρ→nat _)

  associator : Associator-for Laxₗ[_,_] compose
  associator = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .make-natural-iso.eta α .Γ a        = C.α→ _
    ni .make-natural-iso.eta α .is-natural = bicat! C
    ni .make-natural-iso.inv α .Γ a        = C.α← _
    ni .make-natural-iso.inv α .is-natural = bicat! C
    ni .make-natural-iso.eta∘inv α         = ext λ _ → C.α≅ .invl
    ni .make-natural-iso.inv∘eta α         = ext λ _ → C.α≅ .invr
    ni .make-natural-iso.natural _ _ _     = ext λ _ → bicat! C
```
</details>

Slotting these constructions into our bicategory, all that remains is
showing the triangle and pentagon equations.  However, these follow
directly from the corresponding equations of $\bf{C}$, since our unitors
and associator are constructed componentwise from those in $\bf{C}$.

```agda
  pb : Prebicategory _ _ _
  pb .Pb.Ob           = Lax-functor B C
  pb .Pb.Hom          = Laxₗ[_,_]
  pb .Pb.id           = idlx
  pb .Pb.compose      = compose
  pb .Pb.unitor-l     = unitor-l
  pb .Pb.unitor-r     = unitor-r
  pb .Pb.associator   = associator
  pb .Pb.triangle f g = ext λ _ → CH.car (sym (C.⊗.lmap-◆ _))
    ∙∙ C.triangle (σ f _) (σ g _)
    ∙∙ C.⊗.rmap-◆ _
  pb .Pb.pentagon f g h i = ext λ _ → CH.car (sym (C.⊗.lmap-◆ _))
    ∙∙ CH.cddr (sym (C.⊗.rmap-◆ _))
    ∙∙ C.pentagon (σ f _) (σ g _) (σ h _) (σ i _)
```

Applying duality yields a bicategory of lax functors with oplax
transformations...

```agda
Laxₒ : Prebicategory o h ℓ → Prebicategory o' h' ℓ' → Prebicategory _ _ _
Laxₒ B C = Laxₗ (B ^op) (C ^op) ^op
```

And the same constructions work to give us bicategories of
pseudofunctors with lax and oplax transformations, respectively.

```agda
Pseudoₗ : Prebicategory o h ℓ → Prebicategory o' h' ℓ' → Prebicategory _ _ _
Pseudoₗ B C .Pb.Ob         = Pseudofunctor B C
Pseudoₗ B C .Pb.Hom F G    = Pseudoₗ[ F , G ]
Pseudoₗ B C .Pb.id         = idlx
Pseudoₗ B C .Pb.compose    = Lax.compose B C
Pseudoₗ B C .Pb.unitor-l   = Lax.unitor-l B C
Pseudoₗ B C .Pb.unitor-r   = Lax.unitor-r B C
Pseudoₗ B C .Pb.associator = to-natural-iso ni where
  ni : make-natural-iso _ _
  ni .make-natural-iso.eta           = Lax.associator B C .to .η
  ni .make-natural-iso.inv           = Lax.associator B C .from .η
  ni .make-natural-iso.eta∘inv _     = ext λ _ → Br.α≅ C .invl
  ni .make-natural-iso.inv∘eta _     = ext λ _ → Br.α≅ C .invr
  ni .make-natural-iso.natural _ _ _ = ext λ _ → bicat! C
Pseudoₗ B C .Pb.triangle f g     = Lax.pb B C .Pb.triangle f g
Pseudoₗ B C .Pb.pentagon f g h i = Lax.pb B C .Pb.pentagon f g h i

Pseudoₒ : Prebicategory o h ℓ → Prebicategory o' h' ℓ' → Prebicategory _ _ _
Pseudoₒ B C = Pseudoₗ (B ^op) (C ^op) ^op
```

<!--
TODO: Define Pseudoₗ as a full subbicategory of Laxₗ, and Pseudoₚ (with
pseudonatural transformations) as a locally full subbicategory of Laxₗ.
-->
