<!--
```agda
{-# OPTIONS --lossy-unification #-}
open import Algebra.Ring.Module.Notation
open import Algebra.Ring.Commutative
open import Algebra.Group.Notation
open import Algebra.Ring.Module hiding (map)
open import Algebra.Prelude
open import Algebra.Group
open import Algebra.Ring

open import Cat.Prelude hiding (_+_)

open import Data.Fin.Product
open import Data.Fin.Base
```
-->

```agda
module Algebra.Ring.Module.Multilinear
  {ℓ} (R : Ring ℓ) (cr : is-commutative-ring R)
  where
```

# Multilinear maps

<!--
```agda
private module R = Ring-on (R .snd)
open Additive-notation ⦃ ... ⦄
open Module-notation ⦃ ... ⦄

-- XXX: Level subsumption checking _hates_ what I'm doing here with
-- ℓ-maxᶠ, since it doesn't satisfy any definitional equalities like
-- (ℓ-maxᶠ (λ x → f x ⊔ y)) = ℓ-maxᶠ f ⊔ y. The level we pick has to
-- satisfy:
--
--   ℓ-maxᶠ (λ z → ℓ ⊔ ℓₘ z ⊔ ℓₙ ⊔ ℓ-maxᶠ ℓₘ) ≤ _
--
-- floating out the constants, this is
--   ℓ ⊔ ℓₙ ⊔ ℓ-maxᶠ (λ z → ℓₘ n ⊔ ℓ-maxᶠ ℓₘ)
-- and the last term simplifies to ℓ-maxᶠ ℓₘ by reasoning in a
-- lattice.
--
{-# NO_UNIVERSE_CHECK #-}
```
-->

We define the [module] of _multilinear maps_ over a base [commutative]
[ring] $R$, generically over all finite arities. A multilinear map in
$n$ variables is a function $f : M_0 \to M_1 \to \dots M_n \to N$, which
is separately linear in each variable. We formalise this construction
very literally, using [finitary dependent products] and curried
functions.

[module]: Algebra.Ring.Module.html
[ring]: Algebra.Ring.html
[commutative]: Algebra.Ring.Commutative.html
[finitary dependent products]: Data.Fin.Product.html

<!--
```agda
record Multilinear-map (n : Nat) {ℓₘ : Fin n → Level} {ℓₙ}
        (Ms : (i : Fin n) → Module R (ℓₘ i))
        (N : Module R ℓₙ) : Type (ℓ ⊔ ℓₙ ⊔ ℓ-maxᶠ ℓₘ)
  where
  no-eta-equality

  private instance
    _ = module-notation N
    _ : ∀ {i : Fin n} → Module-notation R ⌞ Ms i ⌟
    _ = module-notation (Ms _)
```
-->

```agda
  field
    map      : Arrᶠ (λ i → ⌞ Ms i ⌟) ⌞ N ⌟
```

We use the combinators for reasoning about finitary curried functions to
express the $n$-fold linearity requirement as follows. For simplicity,
assume we are given a tuple $\alpha : \Pi^f M$, and an index $i : [n]$.
The $i$th value of $\alpha$ does not matter, but having an irredundant
representation would be much harder.

If we are given $r : R$, $x, y : M_i$, we can consider the updated
tuples[^updatep] $\alpha[i:=x]$, $\alpha[i:=y]$, and $\alpha[i:=rx+y]$
--- which take the same values as $\alpha$ on all but the $i$th index,
where they have the specified value. This corresponds to holding all but
the $i$th index constant, and allowing only it to vary. Linearity on the
$i$th value saying that $f(\alpha[i:=rx+y]) = rf(\alpha[i:=x]) +
f(\alpha[i:=y])$.

[^updatep]: Apologies for the notation here --- I could not find a way
to denote `updateₚ α i x` that fits well in the mathematical prose.

```agda
    linearₚ
      : Πᶠ λ i → (α : Πᶠ λ j → ⌞ Ms j ⌟) (r : ⌞ R ⌟) (x y : ⌞ Ms i ⌟)
      → applyᶠ map (updateₚ α i (r ⋆ x + y))
      ≡ r ⋆ applyᶠ map (updateₚ α i x) + applyᶠ map (updateₚ α i y)
```

<!--
```agda
  linear-at
    : ∀ i (xs : Πᶠ λ j → ⌞ Ms j ⌟) (r : ⌞ R ⌟) (x y : ⌞ Ms i ⌟)
    → applyᶠ map (updateₚ xs i (r ⋆ x + y))
    ≡ r ⋆ applyᶠ map (updateₚ xs i x) + applyᶠ map (updateₚ xs i y)
  linear-at = indexₚ linearₚ

  pres-+-at
    : ∀ i (xs : Πᶠ λ j → ⌞ Ms j ⌟) (x y : ⌞ Ms i ⌟)
    → applyᶠ map (updateₚ xs i (x + y))
    ≡ applyᶠ map (updateₚ xs i x) + applyᶠ map (updateₚ xs i y)
  pres-+-at i xs x y =
      ap (λ e → applyᶠ map (updateₚ xs i (e + y))) (sym (⋆-id _))
    ·· linear-at i xs R.1r x y
    ·· ap₂ _+_ (⋆-id _) refl

  is-group-hom-at
    : ∀ i (xs : Πᶠ λ j → ⌞ Ms j ⌟)
    → is-group-hom (Module-on→Group-on (Ms i .snd))
                   (Module-on→Group-on (N .snd))
                   λ m → applyᶠ map (updateₚ xs i m)
  is-group-hom-at i xs .is-group-hom.pres-⋆ x y = pres-+-at i xs x y

  pres-⋆-at
    : ∀ i (xs : Πᶠ λ j → ⌞ Ms j ⌟) (r : ⌞ R ⌟) (x : ⌞ Ms i ⌟)
    → applyᶠ map (updateₚ xs i (r ⋆ x))
    ≡ r ⋆ applyᶠ map (updateₚ xs i x)
  pres-⋆-at i xs r x =
      ap (λ e → applyᶠ map (updateₚ xs i e)) (sym +-idr)
    ·· linear-at i xs r x 0g
    ·· (ap₂ _+_ refl (is-group-hom.pres-id (is-group-hom-at i xs)) ∙ +-idr)

-- XXX: Since we're already squishing down a type whose universe level
-- Agda dislikes, one might wonder if we have to use the finitary
-- products in the type of `pres-+ₚ`. The answer is yes, since
-- otherwise `linearᶠ` lives in Setω, which the declare-record-iso
-- tactic is very unhappy about.

open Multilinear-map
open Multilinear-map using (map) public
open Linear-map using (map)

private unquoteDecl eqv = declare-record-iso eqv (quote Multilinear-map)

private variable
  ℓm ℓn : Level
  M N : Module R ℓm
  n : Nat
  ℓₘ : Fin n → Level
  Ms : ∀ i → Module R (ℓₘ i)

Multilinear-map-path
  : ∀ {n} {ℓₘ : Fin n → Level} {N : Module R ℓn} {Ms : (i : Fin n) → Module R (ℓₘ i)}
    {f g : Multilinear-map n Ms N}
  → f .map ≡ g .map
  → f ≡ g
Multilinear-map-path {N = N} {f = f} {g = g} p = go where
  module N = Module-on (N .snd)
  go : f ≡ g
  go i .map = p i
  go i .linearₚ = is-prop→pathp
    (λ i → Πᶠ-is-hlevel 1 λ j → Π-is-hlevel³ 1 λ _ _ _ → Π-is-hlevel 1 λ _ →
      N .fst .is-tr (applyᶠ (p i) _) (_ N.⋆ applyᶠ (p i) _ N.+ applyᶠ (p i) _))
    (f .linearₚ) (g .linearₚ)
    i

Multilinear-maps
  : ∀ {n} {ℓₘ : Fin n → Level}
      {Ms : (i : Fin n) → Module R (ℓₘ i)}
      {N : Module R ℓn}
  → Module-on R (Multilinear-map n Ms N)
Multilinear-maps {n = n} {Ms = Ms} {N = N} = to-module-on mk where
  private
    module Ms i = Module-on (Ms i .snd)
    module N    = Module-on (N .snd)
    instance
      _ = module-notation N
      _ : ∀ {i : Fin n} → Module-notation R ⌞ Ms i ⌟
      _ = module-notation (Ms _)

    -- Normally there would be no way in hell these helpers would ever
    -- be useful... except this module needs lossy-unification for
    -- performance reasonsl so we might as well abuse it for style!
    _⟨_⟩
      : Multilinear-map n Ms N
      → {_ : Πᶠ (λ i → ⌞ Ms i ⌟)} {i : Fin n} → ⌞ Ms i ⌟ → ⌞ N ⌟
    _⟨_⟩ f {xs} {i} x = applyᶠ (f .map) (updateₚ xs i x)

    _⟨_⟩ᵤ
      : ∀ {n ℓ'} {ℓ : Fin n → Level} {P : (i : Fin n) → Type (ℓ i)} {X : Type ℓ'}
      → Arrᶠ P X → {_ : Πᶠ P} {i : Fin n} → P i → X
    _⟨_⟩ᵤ f {xs} {i} x = applyᶠ f (updateₚ xs i x)

    infix 300 _⟨_⟩
    infix 300 _⟨_⟩ᵤ
```
-->

Note that, since some of the computations involving curried functions of
generic length can get pretty gnarly, we separate preservation of
addition and of scaling when defining multilinear maps. This makes no
semantic difference, but it does simplify the proofs slightly.

We now turn to defining an $R$-module structure on the set of
multilinear maps $M_i \to N$. This is nothing but the pointwise module
structure, exactly as in the construction of [internal homs in $R$-Mod];
However, to keep the interface of `Multilinear-map`{.Agda} simple to
use, we must submit to the conservation of frustration, and power
through some nighmarish computations by hand.

[internal homs in $R$-Mod]: Algebra.Ring.Module.Category.html

```agda
  add : Multilinear-map n Ms N → Multilinear-map n Ms N → Multilinear-map n Ms N
  add f g .Multilinear-map.map = zipᶠ _+_ (f .map) (g .map)
  add f g .Multilinear-map.linearₚ = tabulateₚ λ i xs r x y →
    zipᶠ _+_ (f .map) (g .map) ⟨ r ⋆ x + y ⟩ᵤ         ≡⟨ apply-zipᶠ _ _ _ _ ⟩
    f ⟨ r ⋆ x + y ⟩ + g ⟨ r ⋆ x + y ⟩                 ≡⟨ ap₂ _+_ (linear-at f i xs r x y) (linear-at g i xs r x y) ⟩
    (r ⋆ f ⟨ x ⟩ + f ⟨ y ⟩) + (r ⋆ g ⟨ x ⟩ + g ⟨ y ⟩) ≡⟨ N.ab.extendr (N.ab.extendl N.+-comm) ⟩
    (r ⋆ f ⟨ x ⟩ + r ⋆ g ⟨ x ⟩) + (f ⟨ y ⟩ + g ⟨ y ⟩) ≡⟨ ap₂ _+_ (sym (⋆-distribl r _ _)) refl ⟩
    r ⋆ (f ⟨ x ⟩ + g ⟨ x ⟩) + (f ⟨ y ⟩ + g ⟨ y ⟩)     ≡⟨ ap₂ N._+_ (ap (r N.⋆_) (sym (apply-zipᶠ _ _ _ _))) (sym (apply-zipᶠ _ _ _ _)) ⟩
    r ⋆ (zipᶠ _+_ (f .map) (g .map) ⟨ x ⟩ᵤ)
      + zipᶠ _+_ (f .map) (g .map) ⟨ y ⟩ᵤ             ∎
```

The example of addition, above, is representative: The flow of these
proofs is explicit appeals to the computation rule(s) of curried
functions, since the length is generic, surrounding a bit of actual
algebra when the underlying operations are exposed enough. The rest of
the construction is entirely analogous.

<details>
<summary>Since it's so repetitive, it does not need time in the
spotlight.</summary>

```agda
  invm : Multilinear-map n Ms N → Multilinear-map n Ms N
  invm f .map     = mapᶠ N.-_ (f .map)
  invm f .linearₚ = tabulateₚ λ i xs r x y →
    apply-mapᶠ _ _ _ ·· ap N.-_ (linear-at f i xs r x y)
    ·· N.neg-comm
    ·· N.+-comm
    ·· sym (ap₂ N._+_ N.⋆-invr refl)
     ∙ sym (ap₂ N._+_ (ap (r N.⋆_) (apply-mapᶠ _ _ _)) (apply-mapᶠ _ _ _))

  scale : ⌞ R ⌟ → Multilinear-map n Ms N → Multilinear-map n Ms N
  scale r f .map = mapᶠ (r N.⋆_) (f .map)
  scale r f .linearₚ = tabulateₚ λ i xs s x y →
    apply-mapᶠ _ _ _
    ·· ap (r N.⋆_) (linear-at f i xs s x y)
    ·· ⋆-distribl _ _ _
     ∙ ap₂ N._+_ (N.⋆-assoc _ _ _ ·· ap₂ N._⋆_ cr refl ·· sym (N.⋆-assoc _ _ _) ∙ ap (s N.⋆_) (sym (apply-mapᶠ _ _ _)))
                 (sym (apply-mapᶠ _ _ _))

  open make-module hiding (_+_ ; _⋆_)

  mk : make-module R (Multilinear-map n Ms N)
  mk .has-is-set = Iso→is-hlevel 2 eqv $ Σ-is-hlevel 2 (Arrᶠ-is-hlevel 2 (N .fst .is-tr)) λ x →
    is-prop→is-set $ Πᶠ-is-hlevel 1 λ i →
      Π-is-hlevel³ 1 λ _ _ _ → Π-is-hlevel 1 λ _ → N .fst .is-tr _ _

  -- Structure
  mk .make-module._+_ = add
  mk .inv = invm
  mk .make-module._⋆_ = scale
  mk .0g .map = constᶠ N.0g
  mk .0g .linearₚ = tabulateₚ λ i xs r x y →
    apply-constᶠ _ (updateₚ xs i (r ⋆ x + y)) ∙ sym (N.ab.elimr (apply-constᶠ _ _)
    ∙ ap (r N.⋆_) (apply-constᶠ _ _) ∙ N.⋆-idr)

  -- Group laws
  mk .+-assoc x y z = Multilinear-map-path $ funextᶠ λ as →
        apply-zipᶠ _ _ _ as
    ·· ap₂ N._+_ refl (apply-zipᶠ _ _ _ _)
    ·· N.+-assoc ∙ ap₂ N._+_ (sym (apply-zipᶠ N._+_ _ _ _)) refl
     ∙ sym (apply-zipᶠ N._+_ _ _ _)
  mk .+-invl x = Multilinear-map-path $ funextᶠ λ as →
       apply-zipᶠ _ _ _ _
    ·· ap₂ N._+_ (apply-mapᶠ _ _ _) refl
    ·· N.+-invl
     ∙ sym (apply-constᶠ _ _)
  mk .+-idl x = Multilinear-map-path $ funextᶠ λ as →
    apply-zipᶠ _ _ _ _ ∙ N.ab.eliml (apply-constᶠ _ _)
  mk .+-comm x y = Multilinear-map-path $ funextᶠ λ as →
    apply-zipᶠ _ _ _ _ ∙ N.+-comm ∙ sym (apply-zipᶠ N._+_ _ _ _)

  -- Action laws
  mk .⋆-distribl r x y = Multilinear-map-path $ funextᶠ λ as →
        apply-mapᶠ _ _ _
    ·· ap (r N.⋆_) (apply-zipᶠ _ _ _ _)
    ·· N.⋆-distribl _ _ _
    ·· sym (ap₂ N._+_ (apply-mapᶠ _ _ _) (apply-mapᶠ _ _ _))
    ·· sym (apply-zipᶠ N._+_ _ _ _)
  mk .⋆-distribr r x y = Multilinear-map-path $ funextᶠ λ as →
        apply-mapᶠ _ _ _
    ·· N.⋆-distribr _ _ _
    ·· sym (ap₂ N._+_ (apply-mapᶠ (r N.⋆_) _ _) (apply-mapᶠ (x N.⋆_) _ _))
      ∙ sym (apply-zipᶠ N._+_ _ _ _)
  mk .⋆-assoc r s x = Multilinear-map-path $ funextᶠ λ as →
        apply-mapᶠ _ _ _
    ·· ap (r N.⋆_) (apply-mapᶠ _ _ _)
    ·· N.⋆-assoc _ _ _
      ∙ sym (apply-mapᶠ _ _ _)
  mk .⋆-id x = Multilinear-map-path $ funextᶠ λ as → apply-mapᶠ _ _ _ ∙ N.⋆-id _
```
</details>

```agda
Multilinear-Maps
  : ∀ {n} {ℓₘ : Fin n → Level} (Ms : (i : Fin n) → Module R (ℓₘ i)) (N : Module R ℓn)
  → Module R (ℓ-maxᶠ ℓₘ ⊔ ℓn ⊔ ℓ)
∣ Multilinear-Maps Ms N .fst ∣    = Multilinear-map _ Ms N
Multilinear-Maps Ms N .fst .is-tr = Multilinear-maps .Module-on.has-is-set
Multilinear-Maps Ms N .snd = Multilinear-maps
```

# Currying multilinear maps

If we consider the set of $n$-multilinear maps $M_i \to N$ as an
$R$-module, we are forced to consider the _linear_ maps maps $L \to (M_i
\to N)$. For any concrete $n$, these have definitionally equal
underlying types _and_ module structures, so it stands to reason that we
can construct an isomorphism in the generic case, too. Following the
standard convention, we refer to this isomorphism as _currying_, even
though, strictly speaking, none of its concrete instances perform any
currying.

<!--
```agda
module _
  {n} {ℓₘ : Fin (suc n) → Level}
  {Ms : (i : Fin (suc n)) → Module R (ℓₘ i)}
  {N : Module R ℓn}
  where

  private
    module N = Module-on (N .snd)
    module Ms i = Module-on (Ms i .snd)
```
-->

The construction here is fortunately straightforward, since having
successor length is concrete enough for the type of finitary curried
functions to compute away. The faff lies in shifting indices in the
proofs of linearity.

```agda
  curry-multilinear-map
    : Linear-map (Ms fzero) (Multilinear-Maps (λ i → Ms (fsuc i)) N)
    → Multilinear-map (suc n) Ms N
  curry-multilinear-map lin = ml where
    ml : Multilinear-map (suc n) _ _
    ml .map = λ x → lin .map x .map
    ml .linearₚ = tabulateₚ λ where
      fzero xs r x y    →
        ap (λ e → applyᶠ (e .map) (xs .snd)) (Linear-map.linear lin r x y)
        ·· apply-zipᶠ _ _ _ _
        ·· ap₂ N._+_ (apply-mapᶠ _ _ _) refl
      (fsuc i) xs r x y →
        linear-at (lin .map (xs .fst)) i (xs .snd) r x y

  uncurry-multilinear-map
    : Multilinear-map (suc n) Ms N
    → Linear-map (Ms fzero) (Multilinear-Maps (λ i → Ms (fsuc i)) N)
  uncurry-multilinear-map multi = uc where
    uc : Linear-map _ (Multilinear-Maps _ _)
    uc .map x .map     = multi .map x
    uc .map x .linearₚ = tabulateₚ λ i xs →
      Multilinear-map.linear-at multi (fsuc i) (x , xs)

    uc .lin .linear r s t =
      Multilinear-map-path $ funextᶠ λ as →
        linear-at multi fzero (Ms.0g fzero , as) _ _ _
        ∙ sym (apply-zipᶠ _ _ _ _ ∙ ap₂ N._+_ (apply-mapᶠ _ _ _) refl)
```

To stress how well these constructions compute, note that, on the
components relevant to equality, currying and uncurrying are
definitionally isomorphisms.

```agda
  uncurry-ml-is-iso : is-iso uncurry-multilinear-map
  uncurry-ml-is-iso = λ where
    .is-iso.inv    → curry-multilinear-map
    .is-iso.rinv x → Linear-map-path λ x → Multilinear-map-path refl
    .is-iso.linv x → Multilinear-map-path $ funextᶠ λ as → refl

  module
    Uncurry = Equiv (_ , is-iso→is-equiv uncurry-ml-is-iso)
```

<!--
```agda
1-linear-map
  : ∀ {ℓₘ : Fin 1 → Level} {M : (i : Fin 1) → Module R (ℓₘ i)}
  → Linear-map (M fzero) N → Multilinear-map 1 {ℓₘ = ℓₘ} M N
1-linear-map x .map = x .map
1-linear-map x .linearₚ = (λ _ → x .linear) , tt
```
-->
