<!--
```agda
{-# OPTIONS -vtc.def:10 #-}
open import Algebra.Monoid.Category
open import Algebra.Semigroup
open import Algebra.Monoid renaming (idr to mon-idr; idl to mon-idl)
open import Algebra.Magma

open import Cat.Monoidal.Instances.Cartesian
open import Cat.Displayed.Univalence.Thin
open import Cat.Functor.Hom.Representable
open import Cat.Functor.FullSubcategory
open import Cat.Diagram.Product.Solver
open import Cat.Functor.Equivalence
open import Cat.Instances.Functor
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Displayed.Total
open import Cat.Instances.Sets
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Monoidal.Diagram.Monoid.Representable where
```

<!--
```agda
-- Under the module header to prevent sorting from ruining the import list
open import Cat.Monoidal.Diagram.Monoid
  renaming (Monoid-on to Monoid-ob;
            is-monoid-hom to internal-monoid-hom)

module _
  {o ℓ} {C : Precategory o ℓ}
  (prod : has-products C)
  (term : Terminal C)
  where

  open Cat.Reasoning C
  open Binary-products C prod
  open Terminal term
  open Monoid-ob
  open internal-monoid-hom
  open Monoid-hom
  open Functor
  open _=>_
  open Total-hom
  open Representation
```
-->

# Monoid Objects as Representable Presheaves

Let $\cC$ be a cartesian category, and let $(M,\eta,\mu)$ be an
[internal monoid] in $\cC$. Our first observation is that the
diagrammatic definition implies that every **generalised element** $X
\to M$ is a $\Sets$-monoid, with the identity element given by

$$
X \xto{!} 1 \xto{\eta} M\text{,}
$$

and the multiplication given by

$$
(X \times X) \xto{\langle f, g \rangle} (M \times M) \xto{\mu} M\text{.}
$$

[internal monoid]: Cat.Monoidal.Diagram.Monoid.html

<!--
```agda
  private
    C-monoid : Ob → Type ℓ
    C-monoid m = Monoid-ob (Cartesian-monoidal prod term) m

    C-monoid-hom : ∀ {m n} → Hom m n → C-monoid m → C-monoid n → Type ℓ
    C-monoid-hom f m-mon n-mon =
      internal-monoid-hom (Cartesian-monoidal prod term) f m-mon n-mon
```
-->

```agda
  Mon→Hom-mon : ∀ {m} (x : Ob) → C-monoid m → Monoid-on (Hom x m)
  Mon→Hom-mon {m} x mon = hom-mon where

    has-semigroup : is-semigroup λ f g → mon .μ ∘ ⟨ f , g ⟩
    has-semigroup .has-is-magma .has-is-set = Hom-set _ _
    has-semigroup .associative {f} {g} {h} =
      mon .μ ∘ ⟨ f , mon .μ ∘ ⟨ g , h ⟩ ⟩                                            ≡⟨ products! C prod ⟩
      mon .μ ∘ (id ⊗₁ mon .μ) ∘ ⟨ f , ⟨ g , h ⟩ ⟩                                    ≡⟨ extendl (mon .μ-assoc) ⟩
      mon .μ ∘ ((mon .μ ⊗₁ id) ∘ ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩) ∘ ⟨ f , ⟨ g , h ⟩ ⟩ ≡⟨ products! C prod ⟩
      mon .μ ∘ ⟨ mon .μ ∘ ⟨ f , g ⟩ , h ⟩                                            ∎

    hom-mon : Monoid-on (Hom x m)
    hom-mon .Monoid-on.identity = mon .η ∘ !
    hom-mon .Monoid-on._⋆_ f g = mon .μ ∘ ⟨ f , g ⟩
    hom-mon .Monoid-on.has-is-monoid .has-is-semigroup = has-semigroup
    hom-mon .Monoid-on.has-is-monoid .mon-idl {f} =
      mon .μ ∘ ⟨ mon .η ∘ ! , f ⟩         ≡⟨ products! C prod ⟩
      mon .μ ∘ (mon .η ⊗₁ id) ∘ ⟨ ! , f ⟩ ≡⟨ pulll (mon .μ-unitl) ⟩
      π₂ ∘ ⟨ ! , f ⟩                      ≡⟨ π₂∘⟨⟩ ⟩
      f                                   ∎
    hom-mon .Monoid-on.has-is-monoid .mon-idr {f} =
      mon .μ ∘ ⟨ f , mon .η ∘ ! ⟩         ≡⟨ products! C prod ⟩
      mon .μ ∘ (id ⊗₁ mon .η) ∘ ⟨ f , ! ⟩ ≡⟨ pulll (mon .μ-unitr) ⟩
      π₁ ∘ ⟨ f , ! ⟩                      ≡⟨ π₁∘⟨⟩ ⟩
      f                                   ∎
```

Note that precomposition by $f : x \to y$ also yields a
monoid homomorphism between the monoids of generalized elements.

```agda
  precompose-hom-mon-hom
    : ∀ {x y m} {mon : C-monoid m}
    → (f : Hom x y)
    → Monoid-hom (Mon→Hom-mon y mon) (Mon→Hom-mon x mon) (_∘ f)
  precompose-hom-mon-hom {mon = mon} f .pres-id =
    (mon .η ∘ !) ∘ f ≡⟨ pullr (sym (!-unique (! ∘ f))) ⟩
    mon .η ∘ ! ∎
  precompose-hom-mon-hom {mon = mon} f .pres-⋆ g h =
    (mon .μ ∘ ⟨ g , h ⟩) ∘ f   ≡⟨ pullr (⟨⟩∘ f) ⟩
    mon .μ ∘ ⟨ g ∘ f , h ∘ f ⟩ ∎
```

Furthermore, internal monoid homomorphisms $m \to n$ yield monoid
homomorphisms between monoids of generalized elements.

```agda
  internal-mon-hom→hom-mon-hom
    : ∀ {x m n} {f : Hom m n} {m-mon : C-monoid m} {n-mon : C-monoid n}
    → C-monoid-hom f m-mon n-mon
    → Monoid-hom (Mon→Hom-mon x m-mon) (Mon→Hom-mon x n-mon) (f ∘_)
  internal-mon-hom→hom-mon-hom {f = f} {m-mon} {n-mon} hom .pres-id =
    f ∘ m-mon .η ∘ ! ≡⟨ pulll (hom .pres-η) ⟩
    n-mon .η ∘ !     ∎
  internal-mon-hom→hom-mon-hom {f = f} {m-mon} {n-mon} hom .pres-⋆ g h =
    f ∘ m-mon .μ ∘ ⟨ g , h ⟩       ≡⟨ extendl (hom .pres-μ) ⟩
    n-mon .μ ∘ f ⊗₁ f ∘ ⟨ g , h ⟩  ≡⟨ products! C prod ⟩
    n-mon .μ ∘ ⟨ f ∘ g , f ∘ h ⟩   ∎
```

The latter fact means that we can extend this construction to a
presheaf of monoids.

```agda
  Mon→PshMon
    : ∀ {m} → C-monoid m
    → Functor (C ^op) (Monoids ℓ)
  Mon→PshMon {m} mon .F₀ x .fst = el! (Hom x m)
  Mon→PshMon {m} mon .F₀ x .snd = Mon→Hom-mon x mon
  Mon→PshMon {m} mon .F₁ f .hom = _∘ f
  Mon→PshMon {m} mon .F₁ f .preserves = precompose-hom-mon-hom {mon = mon} f
  Mon→PshMon {m} mon .F-id = Homomorphism-path idr
  Mon→PshMon {m} mon .F-∘ f g = Homomorphism-path λ h → assoc h g f
```

By definition, the constructed presheaf is representable.

```agda
  Mon→PshMon-rep
    : ∀ {m} → (mon : C-monoid m)
    → Representation {C = C} (Forget F∘ Mon→PshMon mon)
  Mon→PshMon-rep {m = m} mon .rep = m
  Mon→PshMon-rep {m = m} mon .represents = to-natural-iso ni where
    open make-natural-iso

    ni : make-natural-iso (Forget F∘ Mon→PshMon mon) (Hom-into C m)
    ni .eta _ f = f
    ni .inv _ f = f
    ni .eta∘inv _ = refl
    ni .inv∘eta _ = refl
    ni .natural _ _ _ = refl
```

We can extend this correspondence to a functor from the category of
monoid objects in $\cC$ to the category of representable presheaves
of monoids on $\cC$.

```agda
  private
    Mon[C] : Precategory (o ⊔ ℓ) (ℓ ⊔ ℓ)
    Mon[C] = ∫ Mon[ Cartesian-monoidal prod term ]

  PShMon : ∀ κ → Precategory (o ⊔ ℓ ⊔ lsuc κ) (o ⊔ ℓ ⊔ κ)
  PShMon κ = Cat[ C ^op , Monoids κ ]

  RepPShMon : Precategory (o ⊔ lsuc ℓ) (o ⊔ ℓ)
  RepPShMon = Restrict {C = PShMon ℓ} (λ P → Representation {C = C} (Forget F∘ P))

  Mon→RepPShMon : Functor Mon[C] RepPShMon
  Mon→RepPShMon .F₀ (m , mon) .object = Mon→PshMon mon
  Mon→RepPShMon .F₀ (m , mon) .witness = Mon→PshMon-rep mon
  Mon→RepPShMon .F₁ f .η x .hom = f .hom ∘_
  Mon→RepPShMon .F₁ f .η x .preserves =
    internal-mon-hom→hom-mon-hom (f .preserves)
  Mon→RepPShMon .F₁ f .is-natural x y g =
    Homomorphism-path λ h → assoc (f .hom) h g
  Mon→RepPShMon .F-id = Nat-path λ x → Homomorphism-path λ f → idl f
  Mon→RepPShMon .F-∘ f g = Nat-path λ x → Homomorphism-path λ h →
    sym (assoc (f .hom) (g .hom) h)
```

We can prove that this functor is fully faithful by using a Yoneda-style
argument.

```agda
  Nat→internal-mon-hom
    : ∀ {m n} {m-mon : C-monoid m} {n-mon : C-monoid n}
    → (α : Mon→PshMon m-mon => Mon→PshMon n-mon)
    → C-monoid-hom (α .η m .hom id) m-mon n-mon
  Nat→internal-mon-hom {m} {n} {m-mon} {n-mon} α .pres-η =
    (α .η m .hom id) ∘ (m-mon .η) ≡˘⟨ ap hom (α .is-natural _ _ _) $ₚ _ ⟩
    α .η top .hom (id ∘ m-mon .η) ≡⟨ ap (α .η _ .hom) (id-comm-sym ∙ ap (m-mon .η ∘_) (sym (!-unique _))) ⟩
    α .η top .hom (m-mon .η ∘ !)  ≡⟨ α .η _ .preserves .pres-id ⟩
    n-mon .η ∘ !                  ≡⟨ elimr (!-unique _) ⟩
    n-mon .η                      ∎
  Nat→internal-mon-hom {m} {n} {m-mon} {n-mon} α .pres-μ =
    α .η m .hom id ∘ (m-mon .μ)                                  ≡˘⟨ ap hom (α .is-natural _ _ _) $ₚ _ ⟩
    α .η (m ⊗₀ m) .hom (id ∘ m-mon .μ)                           ≡⟨ ap (α .η _ .hom) (id-comm-sym ∙ ap (m-mon .μ ∘_) (sym ⟨⟩-η)) ⟩
    α .η (m ⊗₀ m) .hom (m-mon .μ ∘ ⟨ π₁ , π₂ ⟩)                  ≡⟨ α .η _ .preserves .pres-⋆ _ _ ⟩
    n-mon .μ ∘ ⟨ α .η _ .hom π₁ , α .η _ .hom π₂ ⟩               ≡˘⟨ ap (n-mon .μ ∘_) (ap₂ ⟨_,_⟩ (ap (α .η _ .hom) (idl _)) (ap (α .η _ .hom) (idl _))) ⟩
    n-mon .μ ∘ ⟨ α .η _ .hom (id ∘ π₁) , α .η _ .hom (id ∘ π₂) ⟩ ≡⟨ ap (n-mon .μ ∘_) (ap₂ ⟨_,_⟩ (ap hom (α .is-natural _ _ _) $ₚ _) (ap hom (α .is-natural _ _ _) $ₚ _)) ⟩
    n-mon .μ ∘ (α .η m .hom id ⊗₁ α .η m .hom id)                ∎

  Mon→RepPShMon-is-ff : is-fully-faithful Mon→RepPShMon
  Mon→RepPShMon-is-ff =
    is-iso→is-equiv $ iso
      (λ α → total-hom (α .η _ .hom id) (Nat→internal-mon-hom α))
      (λ α → Nat-path λ _ → total-hom-path _
        (funext λ f →
          sym (ap hom (α .is-natural _ _ _) $ₚ _)
          ∙ ap (α .η _ .hom) (idl _))
        (is-prop→pathp (λ _ → hlevel 1) _ _))
      (λ α → total-hom-path _
        (idr _)
        (is-prop→pathp (λ _ → is-monoid-hom-is-prop _) _ _))
```


## Monoid Objects from Representable Presheaves

Intuitively, what we have just shown is that monoids internal to $\cC$
yield monoids in the internal language of $\cC$; in fact, we have a
monoid in every single possible context $X$! However, the converse of
this is also true: if $M$ is a monoid in every single context $X$ in the
internal language of $\cC$, then $M$ is a monoid object, provided that
$M$ is *naturally* a monoid in every context $X$. From a type theoretic
point of view, this is akin to asking that the monoid structure be
invariant under substitution.

```agda
  module _ {m : Ob} (mon : ∀ x → Monoid-on (Hom x m)) where
    private module mon {x} = Monoid-on (mon x)
    open mon using (identity; _⋆_)

    Hom-mon→Mon
      : (∀ {x y} → (f : Hom x y) → identity ∘ f ≡ identity)
      → (∀ {x y} → (f g : Hom y m) → (h : Hom x y) → (f ⋆ g) ∘ h ≡ f ∘ h ⋆ g ∘ h)
      → C-monoid m
```

The monoid operations are defined in the smallest context possible. For
identity this is the empty context (IE: the terminal object), for
multiplication, this is the context $M \times M$.

```agda
    Hom-mon→Mon id-nat ⋆-nat .η = identity {top}
    Hom-mon→Mon id-nat ⋆-nat .μ = π₁ ⋆ π₂
```

The laws follow directly from the fact that $\cC(X, M)$ is naturally a
monoid.

```agda
    Hom-mon→Mon id-nat ⋆-nat .μ-unitl =
      (π₁ ⋆ π₂) ∘ (identity ⊗₁ id)                    ≡⟨ ⋆-nat _ _ _ ⟩
      (π₁ ∘ identity ⊗₁ id) ⋆ (π₂ ∘ identity ⊗₁ id)   ≡⟨ ap₂ _⋆_ π₁∘⟨⟩ π₂∘⟨⟩ ⟩
      (identity ∘ π₁) ⋆ (id ∘ π₂)                     ≡⟨ ap₂ _⋆_ (id-nat _) (idl _) ⟩
      identity ⋆ π₂                                   ≡⟨ mon.idl ⟩
      π₂                                              ∎
    Hom-mon→Mon id-nat ⋆-nat .μ-unitr =
      (π₁ ⋆ π₂) ∘ (id ⊗₁ identity)                  ≡⟨ ⋆-nat _ _ _ ⟩
      (π₁ ∘ id ⊗₁ identity) ⋆ (π₂ ∘ id ⊗₁ identity) ≡⟨ ap₂ _⋆_ π₁∘⟨⟩ π₂∘⟨⟩ ⟩
      (id ∘ π₁) ⋆ (identity ∘ π₂)                   ≡⟨ ap₂ _⋆_ (idl _) (id-nat _) ⟩
      π₁ ⋆ identity                                 ≡⟨ mon.idr ⟩
      π₁                                            ∎
    Hom-mon→Mon id-nat ⋆-nat .μ-assoc =
      (π₁ ⋆ π₂) ∘ (id ⊗₁ (π₁ ⋆ π₂))                                  ≡⟨ ⋆-nat _ _ _ ⟩
      (π₁ ∘ id ⊗₁ (π₁ ⋆ π₂)) ⋆ (π₂ ∘ id ⊗₁ (π₁ ⋆ π₂))                ≡⟨ ap₂ _⋆_ π₁∘⟨⟩ π₂∘⟨⟩ ⟩
      (id ∘ π₁) ⋆ ((π₁ ⋆ π₂) ∘ π₂)                                   ≡⟨ ap₂ _⋆_ (idl _) (⋆-nat _ _ _) ⟩
      π₁ ⋆ ((π₁ ∘ π₂) ⋆ (π₂ ∘ π₂))                                   ≡⟨ mon.associative ⟩
      (π₁ ⋆ (π₁ ∘ π₂)) ⋆ (π₂ ∘ π₂)                                   ≡˘⟨ ap₂ _⋆_ (⋆-nat _ _ _ ∙ ap₂ _⋆_ π₁∘⟨⟩ π₂∘⟨⟩) (idl _) ⟩
      ((π₁ ⋆ π₂) ∘ ⟨ π₁ , π₁ ∘ π₂ ⟩) ⋆ (id ∘ π₂ ∘ π₂)                ≡⟨ ap₂ _⋆_ (ap ((π₁ ⋆ π₂) ∘_) (sym π₁∘⟨⟩)) (ap (id ∘_) (sym π₂∘⟨⟩)) ⟩
      ((π₁ ⋆ π₂) ∘ π₁ ∘ _) ⋆ (id ∘ π₂ ∘ _)                           ≡⟨ ap₂ _⋆_ (extendl (sym π₁∘⟨⟩)) (extendl (sym π₂∘⟨⟩)) ⟩
      (π₁ ∘ _) ⋆ (π₂ ∘ _)                                            ≡˘⟨ ⋆-nat _ _ _ ⟩
      (π₁ ⋆ π₂) ∘ ((π₁ ⋆ π₂) ⊗₁ id) ∘ ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩ ∎
```

We can use the previous fact to show that every representable presheaf
of monoids yields an internal monoid in $\cC$ on the representing object
of the presheaf.


```agda
  RepPshMon→Mon
    : ∀ (P : Functor (C ^op) (Monoids ℓ))
    → (P-rep : Representation {C = C} (Forget F∘ P))
    → C-monoid (P-rep .rep)
  RepPshMon→Mon P P-rep = Hom-mon→Mon hom-mon η*-nat μ*-nat
    module RepPshMon→Mon where
```

Before proceeding with the construction, we shall investigate the
representability condition further. Note that the natural isomorphism
is an isomorphism between generalized elements of the representing object
of $P$ and sections of $P$.

```agda
    m : Ob
    m = P-rep .rep

    PMon : Ob → Type ℓ
    PMon x = ∣ P .F₀ x .fst ∣

    module PMon {x} = Monoid-on (P .F₀ x .snd)
    module repr = natural-iso (P-rep .represents)

    open PMon hiding (idl; idr; associative)

    gen : ∀ {x} → PMon x → Hom x m
    gen {x} px = repr.to .η x px

    elt : ∀ {x} → Hom x m → PMon x
    elt {x} f = repr.from .η x f
```

This isomorphism allows us to transfer the monoid structure on each
$P(x)$ to monoid structure on generalized elements of the representing
object.

```agda
    η* : ∀ x → Hom x m
    η* x = gen identity

    μ* : ∀ {x} → Hom x m → Hom x m → Hom x m
    μ* {x = x} f g = gen $ (elt f) ⋆ (elt g)

    η*-idl : ∀ {x} → (f : Hom x m) → μ* (η* x) f ≡ f
    η*-idl {x} f =
      gen (⌜ elt (gen identity) ⌝ ⋆ elt f) ≡⟨ ap! (repr.invr ηₚ _ $ₚ _) ⟩
      gen (identity ⋆ elt f)               ≡⟨ ap gen PMon.idl ⟩
      gen (elt f)                          ≡⟨ repr.invl ηₚ _ $ₚ _ ⟩
      f                                    ∎

    η*-idr : ∀ {x} → (f : Hom x m) → μ* f (η* x) ≡ f
    η*-idr {x} f =
      gen (elt f ⋆ ⌜ elt (gen identity) ⌝) ≡⟨ ap! (repr.invr ηₚ _ $ₚ _) ⟩
      gen (elt f ⋆ identity)               ≡⟨ ap gen PMon.idr ⟩
      gen (elt f)                          ≡⟨ repr.invl ηₚ _ $ₚ _ ⟩
      f                                    ∎

    μ*-assoc : ∀ {x} → (f g h : Hom x m) → μ* f (μ* g h) ≡ μ* (μ* f g) h
    μ*-assoc {x} f g h =
      gen (elt f ⋆ ⌜ elt (gen (elt g ⋆ elt h)) ⌝) ≡⟨ ap! (repr.invr ηₚ _ $ₚ _) ⟩
      gen (elt f ⋆ (elt g ⋆ elt h))               ≡⟨ ap gen PMon.associative ⟩
      gen (⌜ elt f ⋆ elt g ⌝ ⋆ elt h)             ≡⟨ ap! (sym $ repr.invr ηₚ _ $ₚ _) ⟩
      gen (elt (gen (elt f ⋆ elt g)) ⋆ elt h)     ∎
```

<!--
```agda
    hom-mon : ∀ x → Monoid-on (Hom x m)
    hom-mon x .Monoid-on.identity = η* x
    hom-mon x .Monoid-on._⋆_ = μ*
    hom-mon x .Monoid-on.has-is-monoid .has-is-semigroup .has-is-magma .has-is-set =
      Hom-set x m
    hom-mon x .Monoid-on.has-is-monoid .has-is-semigroup .associative = μ*-assoc _ _ _
    hom-mon x .Monoid-on.has-is-monoid .mon-idl = η*-idl _
    hom-mon x .Monoid-on.has-is-monoid .mon-idr = η*-idr _
```
-->

Naturality follows from naturality, as one would hope!

```agda
    η*-nat
      : ∀ {w x} (f : Hom w x)
      → η* x ∘ f ≡ η* w
    η*-nat {w} {x} f =
      (η* x) ∘ f                  ≡˘⟨ repr.to .is-natural _ _ _ $ₚ _ ⟩
      gen (P .F₁ f .hom identity) ≡⟨ ap gen (P .F₁ f .preserves .pres-id) ⟩
      η* w ∎

    μ*-nat
      : ∀ {w x} (f g : Hom x m) (h : Hom w x)
      → μ* f g ∘ h ≡ μ* (f ∘ h) (g ∘ h)
    μ*-nat f g h =
      μ* f g ∘ h                                            ≡˘⟨ repr.to .is-natural _ _ _ $ₚ _ ⟩
      gen (P .F₁ h .hom ((elt f) ⋆ (elt g)))                ≡⟨ ap gen (P .F₁ h .preserves .pres-⋆ _ _) ⟩
      gen ((P .F₁ h .hom (elt f)) ⋆ (P .F₁ h .hom (elt g))) ≡˘⟨ ap gen (ap₂ _⋆_ (repr.from .is-natural _ _ _ $ₚ _) (repr.from .is-natural _ _ _ $ₚ _)) ⟩
      μ* (f ∘ h) (g ∘ h) ∎
```

This implies that the functor from internal monoids to representable
presheaves of monoids is [split eso], and thus an equivalence.

[split esp]: Cat.Functor.Base.html#essential-fibres

```agda
  Mon→RepPShMon-is-split-eso : is-split-eso Mon→RepPShMon
  Mon→RepPShMon-is-split-eso P .fst =
    P .witness .rep , RepPshMon→Mon (P .object) (P .witness)
  Mon→RepPShMon-is-split-eso P .snd =
    super-iso→sub-iso _ (to-natural-iso ni)
    where
      open make-natural-iso
      open RepPshMon→Mon (P .object) (P .witness)
      open PMon using (identity; _⋆_)
      module P = Functor (P .object)

      ni : make-natural-iso (Mon→PshMon (RepPshMon→Mon (P .object) (P .witness))) (P .object)
      ni .eta x .hom = repr.from .η x
      ni .eta x .preserves .pres-id =
        elt (η* top ∘ !)           ≡⟨ ap elt (η*-nat !) ⟩
        elt (η* x)                 ≡⟨ repr.invr ηₚ _ $ₚ _ ⟩
        identity                   ∎
      ni .eta x .preserves .pres-⋆ f g =
        elt (μ* π₁ π₂ ∘ ⟨ f , g ⟩)                 ≡⟨ ap elt (μ*-nat _ _ _) ⟩
        elt (μ* (π₁ ∘ ⟨ f , g ⟩) (π₂ ∘ ⟨ f , g ⟩)) ≡⟨ ap elt (ap₂ μ* π₁∘⟨⟩ π₂∘⟨⟩) ⟩
        elt (μ* f g)                               ≡⟨ repr.invr ηₚ _ $ₚ _ ⟩
        (elt f ⋆ elt g) ∎
      ni .inv x .hom = repr.to .η x
      ni .inv x .preserves .pres-id = sym (η*-nat _)
      ni .inv x .preserves .pres-⋆ f g =
        gen (f ⋆ g)                                          ≡˘⟨ ap gen (ap₂ _⋆_ (repr.invr ηₚ _ $ₚ _) (repr.invr ηₚ _ $ₚ _)) ⟩
        μ* (gen f) (gen g)                                   ≡˘⟨ ap₂ μ* π₁∘⟨⟩ π₂∘⟨⟩ ⟩
        μ* (π₁ ∘ ⟨ gen f , gen g ⟩) (π₂ ∘ ⟨ gen f , gen g ⟩) ≡˘⟨ μ*-nat _ _ _ ⟩
        μ* π₁ π₂ ∘ ⟨ gen f , gen g ⟩                         ∎
      ni .eta∘inv x = Homomorphism-path (repr.invr ηₚ x $ₚ_)
      ni .inv∘eta x = Homomorphism-path (repr.invl ηₚ x $ₚ_)
      ni .natural x y f = Homomorphism-path (sym (repr.from .is-natural _ _ _) $ₚ_)

  Mon→RepPShMon-is-equiv : is-equivalence Mon→RepPShMon
  Mon→RepPShMon-is-equiv =
    ff+split-eso→is-equivalence
      Mon→RepPShMon-is-ff
      Mon→RepPShMon-is-split-eso
```

## The big picture

It's easy to lose the forest for the trees here, so let's take a step
back and examine what we have done. This equivalence of categories shows
that monoids in the internal language of $\cC$ are really monoids in
$\cC$. Furthermore, nothing we have done relies on the structure of
monoids; we could repeat the same argument with internal groups and
everything would go through smoothly.

The lesson is that category theorists prefer to define internal structure
in the smallest context possible, and then rely on weakening to obtain
a well-behaved object in the internal language. This *works*, but is
somewhat unnatural, and can summon pullback nasal demons that will ruin
your day. For instance, defining internal categories in this manner
requires taking pullbacks to ensure that the composition operation is
well formed, which spirals out of control when quantifying over multiple
morphisms due to coherence issues. If we take this generalized
object perspective instead, such coherence issues can be avoided!
