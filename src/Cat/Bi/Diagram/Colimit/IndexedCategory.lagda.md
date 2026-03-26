<!--
```agda
open import Cat.Bi.Functor.IndexedCategory
open import Cat.Bi.Instances.Discrete
open import Cat.Bi.Instances.Functor
open import Cat.Bi.Functor.Constant
open import Cat.Functor.Equivalence
open import Cat.Bi.Diagram.Colimit
open import Cat.Functor.Naturality
open import Cat.Functor.Coherence
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import Cat.Bi.Equivalence hiding (is-equivalence)
open import Cat.Functor.Base
open import Cat.Bi.Duality hiding (_^op)
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning as Dr
import Cat.Functor.Reasoning as Fr
import Cat.Bi.Reasoning as Br
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Bi.Diagram.Colimit.IndexedCategory
  {o h o' h'} {I : Precategory o h}
  (F : Pseudofunctor (Locally-discrete (I ^op)) (Cat (o ⊔ o') (h ⊔ h')))
  where
```

# Lax colimits of indexed categories

An especially important case of lax colimits are those of [[indexed
categories]], i.e., contravariant pseudofunctors from a [[locally
discrete bicategory]] into $\Cat$.  For an indexed category $F :
\ca{I}\op \to \Cat$, the lax colimit of $F$ coincides with the
[[Grothendieck construction]] $\int F$, which is what we show in this
module.

<!--
```agda
  open Pseudofunctor
  open Modification
  open Cr.Inverses
  open Functor
  open Cr._≅_
  open _=>ₗ_
  open _=>_

  private
    module I      = Precategory I
    module F      = IndexedCategory F
    module F₀ {x} = Cr (F.₀ x)
    module G      = Cr (∫ F.displayed)
    module Cat    = Br (Cat (o ⊔ o') (h ⊔ h'))

    open Dr F.displayed
```
-->

```agda
  univ-cocone : opᵖ F .lax =>ₒ ConstP F.∫ .lax
```

To construct the universal cocone, we use the canonical inclusion
functors from the fibre categories of $F$ into $\int F$.

```agda
  univ-cocone .σ a = F.ιᶠ a
```

The naturality 2-cells are straightforward to define, and we did so
already off-screen.

```agda
  univ-cocone .naturator .η f = nat-unidl-to (F.ιᶠ-base-change f)
```

<details>
<summary>
Verifying that this data satisfies the required naturality and
compatibility requirements is tedious but straightforward in principle,
so we elide the details.
</summary>

```agda
  univ-cocone .naturator .is-natural f g reflᵢ =
    nat-unidl-to (F.ιᶠ-base-change f) ∘nt (_ ▸ F.₂ reflᵢ) ≡⟨ Cat.Hom.elimr (Fr.elim (postaction (Cat _ _) _) F.P₁.F-id) ⟩
    nat-unidl-to (F.ιᶠ-base-change f)                     ≡⟨ Cat.Hom.introl Cat.◀.F-id ⟩
    (idnt ◂ _) ∘nt nat-unidl-to (F.ιᶠ-base-change f)      ∎
  univ-cocone .ν-compositor f g = ext λ _ → sym $
    let
      p : id' ∘' id' ≡ (id' F₀.∘ F.γ← _ .η _) ∘' id' F₀.∘ F.γ→ _ .η _
      p = cast[] (idr' _ ∙[] F₀.insertr (F.γ≅' .invr) ∙[] symP F.cancel-id')
    in
       G.eliml (G.idl _) ∙ G.idl _
    ∙∙ G.cdr (G.idl _ ∙ G.cdr (sym (G.idr _) ∙ Fr.weave (ιᶠ _ _) (F₀.cdr p)))
    ∙∙ sym (G.pushl3 (F.ιᶠ-base-change-comp f g ηₚ _))
  univ-cocone .ν-unitor = ext λ _ →
    Fr.weave (ιᶠ _ _)
      (F₀.cdr (cast[] (F.cancel-id' ∙[] F₀.idl _ ∙[] symP (idr' _))))
    ∙ G.introl (G.idl _)
```

</details>

To show that this cocone is universal, we must show that for any other
lax cocone with apex $X$, we can construct a functor $\int F \to X$
which factors the other cocone through the universal one.

```agda
  module _ (X : Precategory (o ⊔ o') (h ⊔ h')) where
```

<!--
```agda
    open Cr X hiding (invl ; invr)
    private
      module Ox = IndexedOplax {F = opᵖ F} {ConstP X}
      ν-unitor'
        : ∀ (α : ⌞ Pseudoₒ[ opᵖ F , ConstP X ] ⌟ ) {i} y
        → α .ν→ I.id .η y ∘ α .σ i .F₁ (F.υ→ .η _) ≡ id
      ν-unitor' α y = Ox.ν-unitor α y ∙ idr _
```
-->

```agda
    cocone→mediator₀ : opᵖ F .lax =>ₒ ConstP X .lax → Functor F.∫ X
    cocone→mediator₀ α = funct where
```

Assume that we are given a lax cocone $\alpha : F \To \Delta_X$.  This
is an oplax transformation with functor components $F(i) \to X$ for each
$i \in \ca{I}$.  Since an object of $\int F$ bundles an $i \in \ca{I}$
with some $a \in F(i)$, we can use $\alpha_i$ to map $a$ into $X$,
giving us the object mapping we need.

```agda
      module α = _=>ₗ_ α
      funct : Functor F.∫ X
      funct .F₀ (x , Fx) = α.σ x .F₀ Fx
```

For the morphism mapping, we are given $f : i \to j$ in $\ca{I}$,
together with some $\phi : a \to F(f)(b)$ with $a \in F(i)$ and $b \in
F(j)$, and we must produce a morphism $\alpha_i(a) \to \alpha_j(b)$.
Taking $\alpha_i(\phi) : \alpha_i(a) \to \alpha_i(F(f)(b))$ gets us
almost all of the way.  To complete the definition, we need a morphism
$\alpha_i(F(f)(b)) \to \alpha_j(b)$ in $X$, but note that since $\alpha$
is a transformation from $F$ to $\Delta_X$, and $\Delta_X$ sends all
morphisms to the identity functor on $X$, this is exactly a component of
$\alpha$'s naturator.

```agda
      funct .F₁ {x , Fx} {y , Fy} (∫hom f Ff) = α.ν→ f .η Fy ∘ α.σ x .F₁ Ff
```

We can check that this gives a functorial assignment using the coherence
identities of $\alpha$.

```agda
      funct .F-id {x , Fx}                                          = ν-unitor' α Fx
      funct .F-∘ {x , Fx} {y , Fy} {z , Fz} (∫hom f Ff) (∫hom g Fg) =
        α.ν→ (f I.∘ g) .η Fz ∘ α.σ x .F₁ (Ff ∘' Fg)                          ≡⟨ cdr (sym $ Fr.collapse3 (α.σ x) refl) ⟩
        α.ν→ (f I.∘ g) .η Fz ∘ α.σ x .F₁ (F.γ→ (g , f) .η Fz) ∘ _            ≡⟨ extendl (Ox.ν-compositor α f g Fz ∙ eliml (idl _)) ⟩
        α.ν→ f .η Fz ∘ α.ν→ g .η _ ∘ α.σ x .F₁ (F.₁ g .F₁ Ff) ∘ α.σ x .F₁ Fg ≡⟨ cdr (extendl (α.ν→ g .is-natural _ _ _)) ∙ assoc _ _ _ ⟩
        (α.ν→ f .η Fz ∘ α.σ y .F₁ Ff) ∘ α.ν→ g .η Fy ∘ α.σ x .F₁ Fg          ∎
```

Furthermore, assignment of cocones to functors itself extends to a
functor from the category of oplax transformations from $F$ to
$\Delta_X$ to the functor category $[\int F, X]$.

```agda
    cocone→mediator : Functor Pseudoₒ[ opᵖ F , ConstP X ] Cat[ F.∫ , X ]
    cocone→mediator .F₀ = cocone→mediator₀
```

The morphism mapping of this functor acts on modifications $\gamma :
\alpha \to \beta$ between cones, and produces a natural transformation
of induced functors.  This means that at each object $(i, a) \in \int
F$, we must give a component morphism $\alpha_i(a) \to \beta_i(a)$ in
$X$.  But unwrapping the definitions, we see that these are just the
components of $\gamma$.

```agda
    cocone→mediator .F₁ γ .η (x , Fx) = γ .Γ x .η Fx
```

Naturality follows from the naturality of $\gamma$, and functoriality
turns out to be trivial.

```agda
    cocone→mediator .F₁ {α} {β} γ .is-natural (x , Fx) (y , Fy) (∫hom f Ff) =
      γ .Γ y .η Fy ∘ α .ν→ f .η Fy ∘ α .σ x .F₁ Ff             ≡˘⟨ extendl (γ .is-natural ηₚ Fy) ⟩
      β .ν→ f .η Fy ∘ γ .Γ x .η (F.₁ f .F₀ Fy) ∘ α .σ x .F₁ Ff ≡⟨ pushr (γ .Γ x .is-natural _ _ _) ⟩
      (β .ν→ f .η Fy ∘ β .σ x .F₁ Ff) ∘ γ .Γ x .η Fx           ∎
    cocone→mediator .F-id    = ext λ _ → refl
    cocone→mediator .F-∘ γ δ = ext λ _ → refl
```

The final step is to show that the functor produced by
`cocone→mediator`{.Agda} factors essentially uniquely through the
universal cocone.  Formally, we must prove that it forms an
[[equivalence of categories]] together with the functor which maps a
functor $\int F \to X$ to the lax cocone defined by pullback through the
universal cocone.

```agda
    private
      hom→cocone' = hom→cocone₀ {h' = lzero} {o' ⊔ h'} F F.∫ univ-cocone X
```

<details>
<summary>
This equivalence holds essentially by definition, but we must pass
through some fairly tedious bureaucracy to establish it.  These proofs
mostly consist of eliminating identity morphisms, but the terms involved
get very big, and we have to construct layered natural transformations
and modifications.
</summary>

```agda
    cocone→mediator-unit : Id ≅ⁿ hom→cocone' F∘ cocone→mediator
    cocone→mediator-unit = to-natural-iso ni where
      abstract
        cocone-factors
          : ∀ (α : ⌞ Pseudoₒ[ opᵖ F , ConstP X ] ⌟ ) {a b} {f : I.Hom b a} i
          → α .ν→ f .η i ≡ (hom→cocone' F∘ cocone→mediator) .F₀ α .ν→ f .η i
        cocone-factors α i =
          sym $ idl _ ∙∙ eliml (idl _) ∙∙ idl _ ∙∙ idr _ ∙∙ elimr (α .σ _ .F-id)

      ni : make-natural-iso _ _
      ni .make-natural-iso.eta α .Γ a .η _              = id
      ni .make-natural-iso.eta α .Γ a .is-natural _ _ _ =
        pushl (sym (ν-unitor' α _)) ∙∙ sym (cdr (α .σ a .F-∘ _ _)) ∙∙ sym (idr _)
      ni .make-natural-iso.eta α .is-natural = ext λ i →
        idr _ ∙∙ sym (cocone-factors α i) ∙∙ sym (idl _)
      ni .make-natural-iso.inv α .Γ a .η _              = id
      ni .make-natural-iso.inv α .Γ a .is-natural _ _ _ =
        idl _ ∙ cdr (α .σ a .F-∘ _ _) ∙∙ cancell (ν-unitor' α _) ∙∙ sym (idr _)
      ni .make-natural-iso.inv α .is-natural {b = b} = ext λ i →
        idr _ ∙∙ cocone-factors α i ∙∙ sym (idl _)
      ni .make-natural-iso.eta∘inv _     = ext λ _ _ → idl _
      ni .make-natural-iso.inv∘eta _     = ext λ _ _ → idl _
      ni .make-natural-iso.natural _ α f = ext λ _ _ → idr _ ∙ car (ν-unitor' α _)

    cocone→mediator-counit : cocone→mediator F∘ hom→cocone' ≅ⁿ Id
    cocone→mediator-counit = to-natural-iso ni where
      mediator-stable
        : ∀ (G : Functor F.∫ X) {a b} (f : G.Hom a b)
        → (cocone→mediator F∘ hom→cocone') .F₀ G .F₁ f ≡ G .F₁ f
      mediator-stable G (∫hom f Ff) =
          car (idl _ ∙ eliml (idl _) ∙∙ idl _ ∙∙ idr _)
        ∙ Fr.collapse G (∫Hom-path _ (I.idr _) $ cast[] $ F.cancel-id' ∙[] F₀.idl _)

      ni : make-natural-iso _ _
      ni .make-natural-iso.eta G .η _              = id
      ni .make-natural-iso.eta G .is-natural _ _ f =
        idl _ ∙∙ mediator-stable G f ∙∙ sym (idr _)
      ni .make-natural-iso.inv G .η _              = id
      ni .make-natural-iso.inv G .is-natural _ _ f =
        idl _ ∙∙ sym (mediator-stable G f) ∙∙ sym (idr _)
      ni .make-natural-iso.eta∘inv _ = ext λ _ → idl _
      ni .make-natural-iso.inv∘eta _ = ext λ _ → idl _
      ni .make-natural-iso.natural G H α = ext λ _ →
        idr _ ∙ introl (H .F-id) ∙ sym (idl _)

    cocone→mediator⊣ : cocone→mediator ⊣ hom→cocone'
    cocone→mediator⊣ ._⊣_.unit    = cocone→mediator-unit .to
    cocone→mediator⊣ ._⊣_.counit  = cocone→mediator-counit .to
    cocone→mediator⊣ ._⊣_.zig     = ext λ _   → idl _
    cocone→mediator⊣ ._⊣_.zag {G} = ext λ _ _ → idr _ ∙ eliml (G .F-id)
```

</details>

Finally, we can state the promised result: the lax colimit of $F$ is
given by $\int F$.

```agda
    cocone→mediator-equiv : is-equivalence cocone→mediator
    cocone→mediator-equiv .is-equivalence.F⁻¹                = hom→cocone'
    cocone→mediator-equiv .is-equivalence.F⊣F⁻¹              = cocone→mediator⊣
    cocone→mediator-equiv .is-equivalence.has-is-equivalence = record where
      unit-iso α   = Cr.iso→invertible Laxₒ[ _ , _ ] (isoⁿ→iso cocone→mediator-unit α)
      counit-iso G =
        Cr.iso→invertible Cat[ _ , _ ] (isoⁿ→iso cocone→mediator-counit G)

  ∫-colim : is-lax-colimit {h' = lzero} {o' ⊔ h'} F F.∫ univ-cocone
  ∫-colim X = is-equivalenceᶜ→is-equivalence
    $ is-equivalence.inverse-equivalence (cocone→mediator-equiv X)
```
