<!--
```agda
open import Algebra.Ring.Module.Action
open import Algebra.Group.Subgroup
open import Algebra.Ring.Module
open import Algebra.Group.Ab
open import Algebra.Group
open import Algebra.Ring

open import Cat.Displayed.Univalence.Thin
open import Cat.Displayed.Total
open import Cat.Prelude

open import Data.Power

import Algebra.Ring.Reasoning as Ringr
```
-->

```agda
module Algebra.Ring.Ideal where
```

# Ideals in rings {defines="ideal"}

An **ideal** in a ring $R$ is the [[$\Ab$-enriched|Ab-enriched
category]] analogue of a [[sieve]], when $R$ is considered as an
$\Ab$-category with a single object, in that it picks out a
sub-[[$R$-module|module]] of $R$, considered as a [representable module], in
exactly the same way that a sieve on an object $x : \cC$ picks out a
subfunctor of $\yo(x)$. Since we know that $\baut R$'s composition is
given by $R$'s multiplication, and sieves are subsets closed under
precomposition, we instantly deduce that ideals are closed under
multiplication.

[representable module]: Algebra.Ring.Module.html#representable-modules

In the $\Ab$-enriched setting, however, there are some more operations
that leave us in the same $\hom$-group: addition! More generally, the
[[abelian group]] operations, i.e. addition, inverse, and the zero
morphism.  Putting these together we conclude that an ideal in $R$ is a
subset of $R$ containing the identity, which is closed under
multiplication and addition.

```agda
module _ {ℓ} (R : Ring ℓ) where
  private module R = Ringr R

  record is-ideal (𝔞 : ℙ ⌞ R ⌟) : Type (lsuc ℓ) where
    no-eta-equality
    field
      has-rep-subgroup : represents-subgroup R.additive-group 𝔞

      -- Note: these are named after the side the scalar acts on.
      has-*ₗ : ∀ x {y} → y ∈ 𝔞 → (x R.* y) ∈ 𝔞
      has-*ᵣ : ∀ x {y} → y ∈ 𝔞 → (y R.* x) ∈ 𝔞
```

::: popup
An **ideal** of a [[ring]] $R$ (generally [[commutative|ring]]) is a
subset $I \sube R$ which is a [[subgroup]] of $R$'s additive group, and
is furthermore closed under multiplication: if $y \in I$, then so are
$xy$ and $yx$.
:::

::: note
Since most of the rings over which we want to consider ideals
are _commutative_ rings, we will limit ourselves to the definition of
_two-sided_ ideals: Those for which we have, for $y \in \mathfrak{a}$
and any element $x : R$, $xy \in \mathfrak{a}$ and $yx \in
\mathfrak{a}$.
:::

<!--
```agda
    open represents-subgroup has-rep-subgroup
      renaming ( has-unit to has-0 ; has-⋆ to has-+ ; has-inv to has-neg )
      public

    ideal→normal : normal-subgroup R.additive-group 𝔞
    ideal→normal .normal-subgroup.has-rep = has-rep-subgroup
    ideal→normal .normal-subgroup.has-conjugate {y = y} x∈𝔞 =
      subst (_∈ 𝔞) (sym (ap (y R.+_) R.+-commutes ∙ R.cancell R.+-invr)) x∈𝔞

    open normal-subgroup ideal→normal hiding (has-rep) public
```
-->

Since an ideal is a [[subgroup]] of $R$'s additive group, its total space
inherits a group structure, and since multiplication in $R$ distributes
over addition in $R$, the group structure induced on $\mathfrak{a}$
carries a canonical $R$-module structure.

```agda
  ideal→module : (𝔞 : ℙ ⌞ R ⌟) → is-ideal 𝔞 → Module R ℓ
  ideal→module 𝔞 x = g .fst , mod where
    open Ring-action
    open is-ideal x
    gr : Group-on _
    gr = rep-subgroup→group-on 𝔞 has-rep-subgroup

    g = from-commutative-group (el! _ , gr) λ x y → Σ-prop-path! R.+-commutes

    mod : Module-on R ⌞ g ⌟
    mod = Action→Module-on R {G = g .snd} λ where
      ._⋆_ r (a , b) → _ , has-*ₗ r b
      .⋆-distribl r x y → Σ-prop-path! R.*-distribl
      .⋆-distribr r s x → Σ-prop-path! R.*-distribr
      .⋆-assoc r s x    → Σ-prop-path! R.*-associative
      .⋆-id x           → Σ-prop-path! R.*-idl
```

Since a map between modules is a [[monomorphism]] when its underlying
function is injective, and the first projection from a subset is always
injective, we can quickly conclude that the module structure on
$\mathfrak{a}$ is a sub-$R$-module of $R$:

```agda
  ideal→submodule
    : {𝔞 : ℙ ⌞ R ⌟} (idl : is-ideal 𝔞)
    → ideal→module 𝔞 idl R-Mod.↪ representable-module R
  ideal→submodule {𝔞 = 𝔞} idl = record
    { mor   = ∫hom fst (record { linear = λ _ _ _ → refl })
    ; monic = λ {c = c} g h x → Structured-hom-path (R-Mod-structure R) $
      embedding→monic (Subset-proj-embedding λ _ → 𝔞 _ .is-tr) (g .fst) (h .fst) (ap fst x)
    }
```

## Principal ideals

Every element $a : R$ generates an ideal: that of its multiples, which
we denote $(a)$. You'll note that we have to use the $\exists$
quantifier (rather than the $\sigma$ quantifier) to define $(a)$, since
in an arbitrary ring, multiplication by $a$ may fail to be injective,
so, given $a, b : R$ $b = ca = c'a$, we can't in general conclude that
$c = c'$.  Of course, in _any_ ring, multiplication _by zero_ is never
injective.

Note that, since our ideals are all two-sided (for simplicity) but our
rings may not be commutative (for expressiveness), if we want the ideal
generated by an element to be two-sided, this element must be *central*:
it must commute with every element of the ring.

```agda
  principal-ideal
    : (a : ⌞ R ⌟)
    → (central : ∀ x → a R.* x ≡ x R.* a)
    → is-ideal λ b → elΩ (Σ _ λ c → b ≡ c R.* a)
  principal-ideal a comm = record
    { has-rep-subgroup = record
      { has-unit = pure (_ , sym R.*-zerol)
      ; has-⋆    = λ x y → do
          (xi , p) ← x
          (yi , q) ← y
          pure (xi R.+ yi , ap₂ R._+_ p q ∙ sym R.*-distribr)
      ; has-inv  = λ x → do
          (xi , p) ← x
          pure (R.- xi , ap R.-_ p ∙ sym R.*-negatel)
      }
    ; has-*ₗ = λ x y → do
        (yi , q) ← y
        pure (x R.* yi , R.m.pushr q)
    ; has-*ᵣ = λ x y → do
        (yi , q) ← y
        pure ( yi R.* x
            , ap (R._* x) q ∙ R.m.extendr (comm x))
    }
```
