<!--
```agda
open import Algebra.Group.Ab
open import Algebra.Group

open import Cat.Displayed.Univalence.Thin
open import Cat.Instances.Product
open import Cat.Displayed.Total
open import Cat.Prelude
```
-->

```agda
module Algebra.Group.Ab.Hom where
```

# Maps between abelian groups

<!--
```agda
open is-group-hom
open Total-hom
```
-->

As [groups] are an algebraic theory, if $G$ is a group, we can equip the
set of functions $X \to G$ with the pointwise group structure. When
considering a pair of groups $G, H$, however, we're less interested in
the _functions_ $G \to H$, and more interested in the homomorphisms $G
\to H$. Can these be equipped with a group structure?

[groups]: Algebra.Group.html

It turns out that the answer is no: if you try to make $\hom$ into a
functor on [$\Grp$], equipping $A \to B$ the pointwise group structure,
you find out that the sum of group homomorphisms can not be shown to be
a homomorphism. But when considering [[abelian groups]], i.e. the category
[$\Ab$], this _does_ work:

[$\Grp$]: Algebra.Group.Cat.Base.html
[$\Ab$]: Algebra.Group.Ab.html

<!--
```agda
Abelian-group-on-hom
  : ∀ {ℓ} (A B : Abelian-group ℓ)
  → Abelian-group-on (Ab.Hom A B)
Abelian-group-on-hom A B = to-abelian-group-on make-ab-on-hom module Hom-ab where
  open make-abelian-group
  private
    module B = Abelian-group-on (B .snd)
    module A = Abelian-group-on (A .snd)

  make-ab-on-hom : make-abelian-group (Ab.Hom A B)
  make-ab-on-hom .ab-is-set = Ab.Hom-set _ _
```
-->

```agda
  make-ab-on-hom .mul f g .hom x = f .hom x B.* g .hom x
  make-ab-on-hom .mul f g .preserves .pres-⋆ x y =
    f .hom (x A.* y) B.* g .hom (x A.* y)                ≡⟨ ap₂ B._*_ (f .preserves .pres-⋆ x y) (g .preserves .pres-⋆ x y) ⟩
    (f .hom x B.* f .hom y) B.* (g .hom x B.* g .hom y)  ≡⟨ B.pullr (B.pulll refl)  ⟩
    f .hom x B.* (f .hom y B.* g .hom x) B.* g .hom y    ≡⟨ (λ i → f .hom x B.* B.commutes {x = f .hom y} {y = g .hom x} i B.* (g .hom y)) ⟩
    f .hom x B.* (g .hom x B.* f .hom y) B.* g .hom y    ≡⟨ B.pushr (B.pushl refl) ⟩
    (f .hom x B.* g .hom x) B.* (f .hom y B.* g .hom y)  ∎

  make-ab-on-hom .inv f .hom x = B._⁻¹ (f .hom x)
  make-ab-on-hom .inv f .preserves .pres-⋆ x y =
    f .hom (x A.* y) B.⁻¹               ≡⟨ ap B._⁻¹ (f .preserves .pres-⋆ x y) ⟩
    (f .hom x B.* f .hom y) B.⁻¹        ≡⟨ B.inv-comm ⟩
    (f .hom y B.⁻¹) B.* (f .hom x B.⁻¹) ≡⟨ B.commutes ⟩
    (f .hom x B.⁻¹) B.* (f .hom y B.⁻¹) ∎

  make-ab-on-hom .1g .hom x = B.1g
  make-ab-on-hom .1g .preserves .pres-⋆ x y = B.introl refl
```

<!--
```agda
  make-ab-on-hom .idl x       = Homomorphism-path λ x → B.idl
  make-ab-on-hom .assoc x y z = Homomorphism-path λ _ → B.associative
  make-ab-on-hom .invl x      = Homomorphism-path λ x → B.inversel
  make-ab-on-hom .comm x y    = Homomorphism-path λ x → B.commutes

open Functor

Ab[_,_] : ∀ {ℓ} → Abelian-group ℓ → Ab.Ob → Ab.Ob
∣ Ab[ A , B ] .fst ∣ = _
Ab[ A , B ] .fst .is-tr = Ab.Hom-set A B
Ab[ A , B ] .snd = Abelian-group-on-hom A B
```
-->

It's only a little more work to show that this extends to a functor
$\Ab\op \times \Ab \to \Ab$.

```agda
Ab-hom-functor : ∀ {ℓ} → Functor (Ab ℓ ^op ×ᶜ Ab ℓ) (Ab ℓ)
Ab-hom-functor .F₀ (A , B) = Ab[ A , B ]
Ab-hom-functor .F₁ (f , g) .hom h = g Ab.∘ h Ab.∘ f
Ab-hom-functor .F₁ (f , g) .preserves .pres-⋆ x y = Homomorphism-path λ z →
  g .preserves .pres-⋆ _ _
Ab-hom-functor .F-id    = Homomorphism-path λ _ → Homomorphism-path λ x → refl
Ab-hom-functor .F-∘ f g = Homomorphism-path λ _ → Homomorphism-path λ x → refl
```
