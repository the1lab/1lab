<!--
```agda
open import Cat.Functor.Equivalence
open import Cat.Functor.Naturality
open import Cat.Functor.Univalence
open import Cat.Functor.Adjoint
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as Fr
import Cat.Reasoning as Cr
```
-->

```agda
module
  Cat.Functor.Adjoint.Unique
  {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
  where
```

<!--
```agda
private
  module C = Cr C
  module D = Cr D
```
-->

# Uniqueness of adjoints

Let $F : \cC \to \cD$ be a functor participating in two [[adjunctions]]
$F \dashv G$ and $F \dashv G'$. Using the data from both adjunctions, we
can exhibit a natural isomorphism $G \cong G'$, which additionally
preserves the unit and counit: Letting $\gamma$, $\delta$ be the
components of the natural isomorphism, we have $\gamma\eta = \eta'$,
idem for $\eps$.

<!--
```agda
module _ {F : Functor C D} {G G' : Functor D C} (a : F ⊣ G) (a' : F ⊣ G') where
  private
    module F = Fr F
    module G = Fr G
    module G' = Fr G'
    module a = _⊣_ a
    module a' = _⊣_ a'
  open a.unit using (η)
  open a.counit using (ε)
  open a'.unit hiding (is-natural) renaming (η to η')
  open a'.counit hiding (is-natural) renaming (ε to ε')
  open make-natural-iso
```
-->

The isomorphism is defined (in components) to be $G'\eps\eta'G$, with
inverse $G\eps'\eta{}G$. Here, we show the construction of both
directions, cancellation in one directly, and naturality (naturality for
the inverse is taken care of by `make-natural-iso`{.Agda}). Cancellation
in the other direction is exactly analogous, and so was omitted.

```agda
  private
    make-G≅G' : make-natural-iso G G'
    make-G≅G' .eta x = G'.₁ (ε x) C.∘ η' _
    make-G≅G' .inv x = G.₁ (ε' x) C.∘ η _
    make-G≅G' .inv∘eta x =
      (G.₁ (ε' x) C.∘ η _) C.∘ G'.₁ (ε _) C.∘ η' _    ≡⟨ C.extendl (C.pullr (a.unit.is-natural _ _ _) ∙ G.pulll (a'.counit.is-natural _ _ _)) ⟩
      G.₁ (ε x D.∘ ε' _) C.∘ η _ C.∘ η' _             ≡⟨ C.refl⟩∘⟨ a.unit.is-natural _ _ _ ⟩
      G.₁ (ε x D.∘ ε' _) C.∘ G.₁ (F.₁ (η' _)) C.∘ η _ ≡⟨ G.pulll (D.cancelr a'.zig) ⟩
      G.₁ (ε x) C.∘ η _                               ≡⟨ a.zag ⟩
      C.id                                            ∎
    make-G≅G' .natural x y f =
      G'.₁ f C.∘ G'.₁ (ε x) C.∘ η' _               ≡⟨ C.pulll (G'.weave (sym (a.counit.is-natural _ _ _))) ⟩
      (G'.₁ (ε y) C.∘ G'.₁ (F.₁ (G.₁ f))) C.∘ η' _ ≡⟨ C.extendr (sym (a'.unit.is-natural _ _ _)) ⟩
      (G'.₁ (ε y) C.∘ η' _) C.∘ G.₁ f              ∎
```

<!--
```agda
    make-G≅G' .eta∘inv x =
          C.extendl (C.pullr (a'.unit.is-natural _ _ _))
        ∙∙ ap₂ C._∘_ refl (C.pushl (sym (a'.unit.is-natural _ _ _)))
        ∙∙ C.extend-inner (a'.unit.is-natural _ _ _)
        ∙∙ G'.extendl (a.counit.is-natural _ _ _)
        ∙∙ ap₂ C._∘_ refl ( ap₂ C._∘_ refl (a'.unit.is-natural _ _ _)
                          ∙ G'.cancell a.zig)
        ∙ a'.zag
```
-->

The data above is exactly what we need to define a natural isomorphism
$G \cong G'$. Showing that this isomorphism commutes with the adjunction
natural transformations is a matter of calculating:

```agda
  right-adjoint-unique : Cr.Isomorphism Cat[ D , C ] G G'
  right-adjoint-unique = to-natural-iso make-G≅G'

  abstract
    unique-preserves-unit
      : ∀ {x} → make-G≅G' .eta _ C.∘ η x ≡ η' x
    unique-preserves-unit =
      make-G≅G' .eta _ C.∘ η _                 ≡⟨ C.pullr (a'.unit.is-natural _ _ _) ⟩
      G'.₁ (ε _) C.∘ G'.₁ (F.₁ (η _)) C.∘ η' _ ≡⟨ G'.cancell a.zig ⟩
      η' _                                     ∎

    unique-preserves-counit
      : ∀ {x} → ε _ D.∘ F.₁ (make-G≅G' .inv _) ≡ ε' x
    unique-preserves-counit =
      ε _ D.∘ F.₁ (make-G≅G' .inv _)         ≡⟨ D.refl⟩∘⟨ F.F-∘ _ _ ⟩
      ε _ D.∘ F.₁ (G.₁ (ε' _)) D.∘ F.₁ (η _) ≡⟨ D.extendl (a.counit.is-natural _ _ _) ⟩
      ε' _ D.∘ ε _ D.∘ F.₁ (η _)             ≡⟨ D.elimr a.zig ⟩
      ε' _                                   ∎
```

If the codomain category $\cC$ is furthermore univalent, so that natural
isomorphisms are an [[identity system]] on the functor category $[D,
C]$, we can upgrade the isomorphism $G \cong G'$ to an identity $G
\equiv G$, and preservation of the adjunction data means this identity
can be improved to an identification between _pairs of_ the functors and
their respective adjunctions.

```agda
is-left-adjoint-is-prop
 : is-category C
 → (F : Functor C D)
 → is-prop $ Σ[ G ∈ Functor D C ] (F ⊣ G)
is-left-adjoint-is-prop cc F (G , a) (G' , a') i = G≡G' cd i , a≡a' cd i
```

<!--
```agda
  where
  G≅G' = right-adjoint-unique a a'
  cd = Functor-is-category cc
  open _⊣_
  open _=>_
  open Functor
  module F = Fr F

  module _ (d : is-category Cat[ D , C ]) where
    G≡G' = d .to-path G≅G'

    abstract
      same-eta : PathP (λ i → Id => G≡G' i F∘ F) (a .unit) (a' .unit)
      same-eta = Nat-pathp refl (λ i → G≡G' i F∘ F)
        λ x → Hom-pathp-reflr C $
          ap₂ C._∘_ (whisker-path-left {G = G} {G'} {F = F} d G≅G') refl
        ∙ unique-preserves-unit a a'

      same-eps : PathP (λ i → F F∘ G≡G' i => Id) (a .counit) (a' .counit)
      same-eps = Nat-pathp (λ i → F F∘ G≡G' i) refl
        λ x → Hom-pathp-refll D $
          ap₂ D._∘_ refl (whisker-path-right {G = F} {F = G} {G'} d G≅G')
        ∙ unique-preserves-counit a a'

    a≡a' : PathP (λ i → F ⊣ G≡G' i) a a'
    a≡a' i .unit = same-eta i
    a≡a' i .counit = same-eps i
    a≡a' i .zig {A} =
      is-set→squarep (λ i j → D.Hom-set (F.₀ A) (F.₀ A))
        (λ i → same-eps i .η (F.₀ A) D.∘ F.₁ (same-eta i .η A))
        (a .zig) (a' .zig) refl i
    a≡a' i .zag {A} =
      is-set→squarep (λ i j → C.Hom-set (G≡G' i .F₀ A) (G≡G' i .F₀ A))
        (λ i → G≡G' i .F₁ (same-eps i .η A) C.∘ same-eta i .η (G≡G' i .F₀ A))
        (a .zag) (a' .zag) (λ _ → C.id) i
```
-->

As a corollary, we conclude that, for a functor $F : \cC \to \cD$ from a
[[univalent category]] $\cC$, "being an equivalence of categories" is a
proposition.

```agda
open adjunction-is-equivalence
open is-equivalence

is-equivalence-is-prop
  : is-category C
  → (F : Functor C D)
  → is-prop (is-equivalence F)
is-equivalence-is-prop ccat F x y = go where
  invs = ap fst $
    is-left-adjoint-is-prop ccat F (x .F⁻¹ , x .F⊣F⁻¹) (y .F⁻¹ , y .F⊣F⁻¹)

  adjs = ap snd $
    is-left-adjoint-is-prop ccat F (x .F⁻¹ , x .F⊣F⁻¹) (y .F⁻¹ , y .F⊣F⁻¹)

  go : x ≡ y
  go i .F⁻¹ = invs i
  go i .F⊣F⁻¹ = adjs i
  go i .has-is-equivalence .unit-iso a =
    is-prop→pathp (λ i → C.is-invertible-is-prop {f = _⊣_.η (adjs i) a})
      (x .unit-iso a)
      (y .unit-iso a) i
  go i .has-is-equivalence .counit-iso a =
    is-prop→pathp (λ i → D.is-invertible-is-prop {f = _⊣_.ε (adjs i) a})
      (x .counit-iso a)
      (y .counit-iso a) i
```
