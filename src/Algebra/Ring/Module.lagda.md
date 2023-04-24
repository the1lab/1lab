<!--
```agda
open import Algebra.Group.Notation
open import Algebra.Group.Ab
open import Algebra.Group
open import Algebra.Ring

open import Cat.Displayed.Univalence.Thin
open import Cat.Prelude hiding (_+_)

import Cat.Reasoning
```
-->

```agda
module Algebra.Ring.Module where
```

<!--
```agda
module _ {ℓ} (R : Ring ℓ) where
  private module R = Ring-on (R .snd)
  open Displayed
  open Total-hom
  open Functor
```
-->

# Modules

A **module** over a \r{ring} $R$ is an \r{abelian group} $G$ equipped
with an action by $R$. Modules generalise the idea of vector spaces,
which may be familiar from linear algebra, by replacing the field of
scalars by a _ring_ of scalars. More pertinently, though, modules
_specialise_ [functors]: specifically, functors into the category $\Ab$.

[functors]: Cat.Abelian.Instances.Functor.html

For silly formalisation reasons, when defining modules, we do not take
"an $\Ab$-functor into $\Ab$" as the definition: this correspondence is
a theorem we prove later. Instead, we set up $R$-modules as typical
algebraic structures, as data (and property) attached to a type.

The structure of an $R$-module on a type $T$ consists of an _addition_
$+ : T \times T \to T$ and a _scalar multiplication_ $\cdot : R \times T
\to T$ — which we generally omit, writing $rx$ for $r \cdot x$. These
must satisfy the following properties:

- $+$ makes $T$ into an [abelian group] — which is easy to state, since
we already have "is an abelian group" as a modular structure;
- $·$ is an endomorphism of $R$ onto $(T, +)$'s endomorphism ring. In
other words, we have:
  * $1x = x$;
  * $(rs) \cdot x = r \cdot (s \cdot x)$;
  * $(r + s)x = rx + sx$; and
  $ $r(x + y) = rx + ry$.

[abelian group]: Algebra.Group.Ab.html

```agda
  record is-module {ℓ′} {T : Type ℓ′} (_+_ : T → T → T) (_⋆_ : ⌞ R ⌟ → T → T) : Type (ℓ ⊔ ℓ′) where
    no-eta-equality
    field
      has-is-ab  : is-abelian-group _+_
      ⋆-distribl : ∀ r x y → r ⋆ (x + y)   ≡ (r ⋆ x) + (r ⋆ y)
      ⋆-distribr : ∀ r s x → (r R.+ s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x)
      ⋆-assoc    : ∀ r s x → (r R.* s) ⋆ x ≡ r ⋆ (s ⋆ x)
      ⋆-id       : ∀ x     → R.1r ⋆ x      ≡ x

    private
      ug : Group-on _
      ug = record { has-is-group = is-abelian-group.has-is-group has-is-ab }

    module ab = Additive-notation ug
    private module ab' = is-abelian-group has-is-ab renaming (commutes to +-comm)

    open ab using (-_ ; 0g ; +-invr ; +-invl ; +-assoc ; +-idl ; +-idr ; neg-0 ; neg-comm ; neg-neg ; has-is-set) public
    open ab' using (+-comm) public

    abstract
      ⋆-is-group-hom : ∀ {r} → is-group-hom ug ug (r ⋆_)
      ⋆-is-group-hom .is-group-hom.pres-⋆ x y = ⋆-distribl _ x y

    private module ⋆gh {r} = is-group-hom (⋆-is-group-hom {r}) renaming (pres-id to ⋆-idr ; pres-inv to ⋆-negr)
    open ⋆gh public using (⋆-idr ; ⋆-negr)

  private unquoteDecl eqv = declare-record-iso eqv (quote is-module)

  record Module-on {ℓ′} (T : Type ℓ′) : Type (ℓ ⊔ ℓ′) where
    no-eta-equality
    field
      _+_        : T → T → T
      _⋆_        : ⌞ R ⌟ → T → T
      has-is-mod : is-module _+_ _⋆_

    infixl 25 _+_
    infixr 27 _⋆_

    open is-module has-is-mod public

  Module-on→Group-on
    : ∀ {ℓm} {T : Type ℓm}
    → Module-on T
    → Group-on T
  Module-on→Group-on M = record { has-is-group = is-abelian-group.has-is-group (Module-on.has-is-ab M) }

  Module-on→Abelian-group-on
    : ∀ {ℓm} {T : Type ℓm}
    → Module-on T
    → Abelian-group-on T
  Module-on→Abelian-group-on M = record { has-is-ab = Module-on.has-is-ab M }

  abstract instance
    H-Level-is-module
      : ∀ {ℓ′} {T : Type ℓ′} {_+_ : T → T → T} {_⋆_ : ⌞ R ⌟ → T → T} {n}
      → H-Level (is-module _+_ _⋆_) (suc n)
    H-Level-is-module {T = T} = prop-instance $ λ x →
      let
        instance
          _ : H-Level T 2
          _ = basic-instance 2 (is-module.has-is-set x)
      in Iso→is-hlevel 1 eqv (hlevel 1) x

  open Module-on ⦃ ... ⦄ hiding (has-is-set)

  Module : ∀ ℓm → Type (lsuc ℓm ⊔ ℓ)
  Module ℓm = Σ (Set ℓm) λ X → Module-on ∣ X ∣

  record is-linear-map {ℓm ℓn} {S : Type ℓm} {T : Type ℓn} (f : S → T) (M : Module-on S) (N : Module-on T) : Type (ℓ ⊔ ℓm ⊔ ℓn) where
    no-eta-equality
    private instance
      _ = M
      _ = N

    field
      linear : ∀ r s t → f (r ⋆ s + t) ≡ r ⋆ f s + f t

    abstract
      has-is-gh : is-group-hom (Module-on→Group-on M) (Module-on→Group-on N) f
      has-is-gh .is-group-hom.pres-⋆ x y = ap f (ap₂ _+_ (sym (⋆-id _)) refl) ∙ linear _ _ _ ∙ ap₂ _+_ (⋆-id _) refl

    open is-group-hom has-is-gh
      renaming ( pres-⋆ to pres-+ ; pres-id to pres-0 ; pres-inv to pres-neg)
      public

    abstract
      pres-⋆ : ∀ r s → f (r ⋆ s) ≡ r ⋆ f s
      pres-⋆ r s = ap f (sym +-idr) ∙ linear _ _ _ ∙ ap (r ⋆ f s +_) pres-0 ∙ +-idr

  private unquoteDecl eqv′ = declare-record-iso eqv′ (quote is-linear-map)
  open is-linear-map using (linear) public

  -- There are too many possible instances in scope for instance search
  -- to solve this one, but fortunately it's pretty short:

  abstract instance
    H-Level-is-linear-map
      : ∀ {ℓ′ ℓ′′} {T : Type ℓ′} {S : Type ℓ′′} {M : Module-on T} {N : Module-on S} {f : T → S} {n}
      → H-Level (is-linear-map f M N) (suc n)
    H-Level-is-linear-map {S = S} {N = N} = prop-instance $
      Iso→is-hlevel 1 eqv′ $
      Π-is-hlevel³ 1 λ _ _ _ →
      Module-on.ab.has-is-set N _ _

  record Linear-map {ℓm ℓn} (M : Module ℓm) (N : Module ℓn) : Type (ℓ ⊔ ℓm ⊔ ℓn) where
    field
      map           : ⌞ M ⌟ → ⌞ N ⌟
      has-is-linear : is-linear-map map (M .snd) (N .snd)
    open is-linear-map has-is-linear public

  open Linear-map public

  Linear-map-path
    : ∀ {ℓm ℓn} {M : Module ℓm} {N : Module ℓn}
      {f g : Linear-map M N}
    → f .map ≡ g .map
    → f ≡ g
  Linear-map-path p i .map = p i
  Linear-map-path {M = M} {N} {f} {g} p i .has-is-linear =
    is-prop→pathp (λ i → hlevel {T = is-linear-map (p i) (M .snd) (N .snd)} 1)
      (f .has-is-linear) (g .has-is-linear) i

  R-Mod-structure : ∀ {ℓ} → Thin-structure _ Module-on
  ∣ R-Mod-structure {ℓ} .is-hom f M N ∣    = is-linear-map {ℓ} {ℓ} f M N
  R-Mod-structure {ℓ} .is-hom f M N .is-tr = Iso→is-hlevel 1 eqv′ $ Π-is-hlevel³ 1 λ _ _ _ → Module-on.ab.has-is-set N _ _
  R-Mod-structure {ℓ} .id-is-hom .linear r s t = refl
  R-Mod-structure {ℓ} .∘-is-hom f g α β .linear r s t = ap f (β .linear r s t) ∙ α .linear _ _ _
  R-Mod-structure {ℓ} .id-hom-unique {s = s} {t = t} α _ = r where
    module s = Module-on s
    module t = Module-on t

    r : s ≡ t
    r i .Module-on._+_ x y = is-linear-map.pres-+ α x y i
    r i .Module-on._⋆_ x y = is-linear-map.pres-⋆ α x y i
    r i .Module-on.has-is-mod =
      is-prop→pathp (λ i → hlevel {T = is-module (λ x y → is-linear-map.pres-+ α x y i) (λ x y → is-linear-map.pres-⋆ α x y i)} 1)
        (Module-on.has-is-mod s) (Module-on.has-is-mod t) i

  R-Mod : ∀ ℓm → Precategory (lsuc ℓm ⊔ ℓ) (ℓm ⊔ ℓ)
  R-Mod ℓm = Structured-objects (R-Mod-structure {ℓm})

  Forget-module : ∀ ℓm → Functor (R-Mod ℓm) (Sets ℓm)
  Forget-module _ = Forget-structure R-Mod-structure

  private
    _ : ∀ {ℓm} → Module ℓm ≡ Precategory.Ob (R-Mod ℓm)
    _ = refl

  record make-module {ℓm} (M : Type ℓm) : Type (ℓm ⊔ ℓ) where
    field
      has-is-set : is-set M
      _+_ : M → M → M
      inv : M → M
      0g  : M

      +-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
      +-invl  : ∀ x → inv x + x ≡ 0g
      +-idl   : ∀ x → 0g + x ≡ x
      +-comm  : ∀ x y → x + y ≡ y + x

      _⋆_ : ⌞ R ⌟ → M → M

      ⋆-distribl : ∀ r x y → r ⋆ (x + y)   ≡ (r ⋆ x) + (r ⋆ y)
      ⋆-distribr : ∀ r s x → (r R.+ s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x)
      ⋆-assoc    : ∀ r s x → (r R.* s) ⋆ x ≡ r ⋆ (s ⋆ x)
      ⋆-id       : ∀ x     → R.1r ⋆ x      ≡ x

  to-module-on : ∀ {ℓm} {M : Type ℓm} → make-module M → Module-on M
  to-module-on m .Module-on._+_ = make-module._+_ m
  to-module-on m .Module-on._⋆_ = make-module._⋆_ m
  to-module-on m .Module-on.has-is-mod = mod where
    gr : Group-on _
    gr = to-group-on λ where
      .make-group.group-is-set → make-module.has-is-set m
      .make-group.unit → make-module.0g m
      .make-group.mul → make-module._+_ m
      .make-group.inv → make-module.inv m
      .make-group.assoc → make-module.+-assoc m
      .make-group.invl → make-module.+-invl m
      .make-group.idl → make-module.+-idl m

    mod : is-module _ _
    mod .is-module.has-is-ab .is-abelian-group.has-is-group = gr .Group-on.has-is-group
    mod .is-module.has-is-ab .is-abelian-group.commutes = make-module.+-comm m _ _
    mod .is-module.⋆-distribl = make-module.⋆-distribl m
    mod .is-module.⋆-distribr = make-module.⋆-distribr m
    mod .is-module.⋆-assoc = make-module.⋆-assoc m
    mod .is-module.⋆-id = make-module.⋆-id m

  from-module-on : ∀ {ℓ} {T : Type ℓ} → Module-on T → Module ℓ
  ∣ from-module-on M .fst ∣    = _
  from-module-on M .fst .is-tr = Module-on.has-is-set M
  from-module-on M .snd = M

  to-module : ∀ {ℓm} {M : Type ℓm} → make-module M → Module ℓm
  ∣ to-module m .fst ∣ = _
  to-module m .fst .is-tr = make-module.has-is-set m
  to-module m .snd = to-module-on m

  module _ {ℓm} (G : Abelian-group ℓm) where
    private module G = Abelian-group-on (G .snd)

    action→module-on
      : (_⋆_ : ⌞ R ⌟ → ⌞ G ⌟ → ⌞ G ⌟)
      → (⋆-distribl : ∀ r x y → r ⋆ (x G.* y) ≡ (r ⋆ x) G.* (r ⋆ y))
      → (⋆-distribr : ∀ r s x → (r R.+ s) ⋆ x ≡ (r ⋆ x) G.* (s ⋆ x))
      → (⋆-assoc    : ∀ r s x → (r R.* s) ⋆ x ≡ r ⋆ (s ⋆ x))
      → (⋆-idl      : ∀ x     → R.1r ⋆ x      ≡ x)
      → Module-on ⌞ G ⌟
    action→module-on s dl dr a i .Module-on._+_ = G._*_
    action→module-on s dl dr a i .Module-on._⋆_ = s
    action→module-on s dl dr a i .Module-on.has-is-mod .is-module.has-is-ab = G.has-is-ab
    action→module-on s dl dr a i .Module-on.has-is-mod .is-module.⋆-distribl = dl
    action→module-on s dl dr a i .Module-on.has-is-mod .is-module.⋆-distribr = dr
    action→module-on s dl dr a i .Module-on.has-is-mod .is-module.⋆-assoc = a
    action→module-on s dl dr a i .Module-on.has-is-mod .is-module.⋆-id = i

    action→module
      : (_⋆_ : ⌞ R ⌟ → ⌞ G ⌟ → ⌞ G ⌟)
      → (⋆-distribl : ∀ r x y → r ⋆ (x G.* y) ≡ (r ⋆ x) G.* (r ⋆ y))
      → (⋆-distribr : ∀ r s x → (r R.+ s) ⋆ x ≡ (r ⋆ x) G.* (s ⋆ x))
      → (⋆-assoc    : ∀ r s x → (r R.* s) ⋆ x ≡ r ⋆ (s ⋆ x))
      → (⋆-idl      : ∀ x     → R.1r ⋆ x      ≡ x)
      → Module ℓm
    action→module s dl dr a i .fst = G .fst
    action→module s dl dr a i .snd = action→module-on s dl dr a i

  representable-module : Module ℓ
  representable-module .fst = R .fst
  representable-module .snd = to-module-on record
    { has-is-set = R.has-is-set
    ; _+_ = R._+_
    ; inv = R.-_
    ; 0g = R.0r
    ; +-assoc = λ x y z → sym R.+-associative
    ; +-invl = λ x → R.+-invl
    ; +-idl = λ x → R.+-idl
    ; +-comm = λ x y → R.+-commutes
    ; _⋆_ = R._*_
    ; ⋆-distribl = λ x y z → R.*-distribl
    ; ⋆-distribr = λ x y z → R.*-distribr
    ; ⋆-assoc    = λ x y z → sym R.*-associative
    ; ⋆-id       = λ x → R.*-idl
    }

module R-Mod {ℓ ℓm} {R : Ring ℓ} = Cat.Reasoning (R-Mod R ℓm)

hom→linear-map
  : ∀ {ℓ ℓm} {R : Ring ℓ} {M N : Module R ℓm}
  → R-Mod.Hom M N
  → Linear-map R M N
hom→linear-map h .map           = h .hom
hom→linear-map h .has-is-linear = h .preserves

linear-map→hom
  : ∀ {ℓ ℓm} {R : Ring ℓ} {M N : Module R ℓm}
  → Linear-map R M N
  → R-Mod.Hom M N
linear-map→hom h .hom       = h .map
linear-map→hom h .preserves = h .has-is-linear
