```agda
open import 1Lab.Prim.Monad

open import Algebra.Group.Subgroup
open import Algebra.Ring.Module
open import Algebra.Group.Ab
open import Algebra.Group
open import Algebra.Ring

open import Cat.Functor.FullSubcategory
open import Cat.Prelude

open import Data.Power

module Algebra.Ring.Ideal where
```

# Ideals in rings

An **ideal** in a ring $R$ is the [$\Ab$-enriched] analogue of a
[sieve], when $R$ is considered as an $\Ab$-category with a single
object, in that it picks out a sub-[$R$-module] of $R$, considered as a
[representable ring], in exactly the same way that a sieve on an object
$x : \ca{C}$ picks out a subfunctor of $\yo(x)$. Since we know that $\B
R$'s composition is given by $R$'s multiplication, and sieves are
subsets closed under precomposition, we instantly deduce that ideals are
closed under multiplication.

[$\Ab$-enriched]: Cat.Abelian.Base.html#ab-enriched-categories
[sieve]: Cat.Diagram.Sieve.html
[$R$-module]: Algebra.Ring.Module.html#modules
[representable ring]: Algebra.Ring.Module.html#representable-modules

In the $\Ab$-enriched setting, however, there are some more operations
that leaves us in the same $\hom$-group: addition! More generally, the
abelian group operations, i.e. addition, inverse, and the zero morphism.
Putting these together we conclude that an ideal in $R$ is a subset of
$R$ containing the identity, which is closed under multiplication and
addition.

```agda
module _ {ℓ} (R : Ring ℓ) where
  private module R = Ring-on (R .snd)
  open Module hiding (module R ; module G)

  record is-ideal (𝔞 : ℙ (R .fst)) : Type (lsuc ℓ) where
    no-eta-equality
    field
      has-rep-subgroup : represents-subgroup R.additive-group 𝔞
      has-* : ∀ x {y} → y ∈ 𝔞 → (x R.* y) ∈ 𝔞

    open represents-subgroup has-rep-subgroup
      renaming ( has-unit to has-0 ; has-⋆ to has-+ ; has-inv to has-neg )
      public
```

Since an ideal is a [subgroup] of $R$'s additive group, its total space
inherits a group structure, and since multiplication in $R$ distributes
over addition in $R$, the group structure induced on $\mathfrak{a}$
carries a canonical $R$-module structure.

[subgroup]: Algebra.Group.Subgroup.html

```agda
  ideal→module : (𝔞 : ℙ (R .fst)) → is-ideal 𝔞 → Module R
  ideal→module 𝔞 x = mod where
    open make-group
    open is-ideal x
    gr : Group-on _
    gr = rep-subgroup→group-on 𝔞 has-rep-subgroup

    mod : Module R
    mod .G = restrict (_ , gr) λ x y → Σ-prop-path (λ _ → 𝔞 _ .is-tr) R.+-commutes
    mod ._⋆_ x y = _ , has-* x (y .snd)
    mod .⋆-id x = Σ-prop-path (λ _ → 𝔞 _ .is-tr) R.*-idl
    mod .⋆-add-r r x y = Σ-prop-path (λ _ → 𝔞 _ .is-tr) R.*-distribl
    mod .⋆-add-l x r s = Σ-prop-path (λ _ → 𝔞 _ .is-tr) R.*-distribr
    mod .⋆-assoc r s x = Σ-prop-path (λ _ → 𝔞 _ .is-tr) R.*-associative
```

Since a map between modules is [a monomorphism] when its underlying
function is injective, and the first projection from a subset is always
injective, we can quickly conclude that the module structure on
$\mathfrak{a}$ is a sub-$R$-module of $R$:

[a monomorphism]: Cat.Morphism.html#monos

```agda
  ideal→submodule
    : {𝔞 : ℙ (R .fst)} (idl : is-ideal 𝔞)
    → ideal→module _ idl R-Mod.↪ representable-module R
  ideal→submodule {𝔞 = 𝔞} idl = record
    { mor   = fst , λ r m s n → refl
    ; monic = λ {c = c} g h x →
      Σ-prop-path (is-R-S-linear-is-prop c (ideal→module _ idl) Rings.id) $
        embedding→monic (Subset-proj-embedding λ _ → 𝔞 _ .is-tr) (g .fst) (h .fst)
          (sym (transport-refl _) ∙ ap fst x ∙ transport-refl _)
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

```agda
  principal-ideal
    : (a : R .fst) → is-ideal λ b → el (∃ (R .fst) λ c → b ≡ c R.* a) squash
  principal-ideal a = record
    { has-rep-subgroup = record
      { has-unit = pure (_ , sym R.*-zerol)
      ; has-⋆    = λ x y → do
          (xi , p) ← x
          (yi , q) ← y
          pure (xi R.+ yi , ap₂ R._+_ p q ∙ sym R.*-distribr)
      ; has-inv  = λ x → do
          (xi , p) ← x
          pure (R.- xi , ap R.-_ p ∙ R.neg-*-l)
      }
    ; has-* = λ x y → do
        (yi , q) ← y
        pure (x R.* yi , ap (x R.*_) q ∙ R.*-associative)
    }
```
