<!--
```agda
open import 1Lab.Reflection.Signature
open import 1Lab.Path.Reasoning
open import 1Lab.Reflection hiding (_!_ ; absurd)
open import 1Lab.Prelude

open import Data.Fin.Properties
open import Data.Wellfounded.W
open import Data.Set.Material
open import Data.Fin.Closure
open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Fin.Base
open import Data.Bool

open hlevel-projection
```
-->

```agda
module Data.Set.Material.Automation where
```

# Automation for material sets

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A A' B B' C : Type ℓ
```
-->

We can write automation for exhibiting a type as a [[material set]]
using a combination of instance arguments and reflection. A
**materialisation** of a type $A$ consists of a $V$-code $c$ and an
equivalence $A \simeq \El c$.

```agda
record Materialise {ℓ} (A : Type ℓ) : Type (lsuc ℓ) where
  field
    code  : V ℓ
    codes : A ≃ Elⱽ code

  open Equiv codes using (to ; from ; η ; ε ; injective) public
```

::: warning
Unlike other similar notions we have automated (like extensionality or
[[h-level]]), materialisations of a type do not inhabit a
[[proposition]], since any automorphism of $A$ can be composed with the
encoding equivalence to get a different materialisation.

The justification for providing this automation is the empirical
observation that constructions which use $V$ as a universe do not depend
on the precise tree structure of the code.
:::

<!--
```agda
-- Usage note: to maintain this property, 'Materialise' MUST NOT appear
-- in the types of anything that is not a 'Materialise' instance.
-- Instead, downstream functions which are parametrised by a V-code
-- SHOULD take an x : V explicitly.

{-# INLINE Materialise.constructor #-}
open Materialise hiding (to ; from ; η ; ε ; injective)
```
-->

The entry point for computing materialisations is the function
`materialise!`{.Agda}, which realigns the synthesised materialisation to
end up with a $V$-code that definitionally decodes to the type given.
This is necessary because "*definitionally* decodes to the stated type"
is not something we can mandate in the definition of the
`Materialise`{.Agda} record. Nevertheless, we can ask that Agda verify
this property, both as a demonstration and to avoid breakage in the
future.

```agda
materialise! : ∀ {ℓ} (A : Type ℓ) ⦃ m : Materialise A ⦄ → V (level-of A)
materialise! A ⦃ m ⦄ = realignⱽ (m .code) (Materialise.to m) (Materialise.injective m)

_ : ∀ {ℓ} {A : Type ℓ} ⦃ m : Materialise A ⦄ → Elⱽ (materialise! A) ≡ A
_ = refl
```

Of course, if a type is definitionally the decoding of a $V$-set, it has
an evident materialisation. If we can come up with an isomorphism
between $B$ and some materialised type $A$, we can also use that to
materialise $B$.

```agda
basic : (X : V ℓ) → Materialise (Elⱽ X)
basic X = record { code = X ; codes = id≃ }

Iso→materialisation
  : ∀ {ℓ} {A B : Type ℓ} ⦃ _ : Materialise A ⦄
  → Iso B A
  → Materialise B
Iso→materialisation ⦃ a ⦄ i = record where
  module i = Iso i
  code  = a .code
  codes = Iso→Equiv i ∙e a .codes
```

## Closure instances

We then have a battery of instances for both closed types like
`Bool`{.Agda} and type formers that we had previously written $V$-codes
for like `Πⱽ`{.Agda} and `Σⱽ`{.Agda}. Unlike (e.g.) `Πⱽ`{.Agda}, the
instance here supports materialising function types where the domain and
codomain live in different universes, by automatically inserting
`liftⱽ`{.Agda} where necessary. This management of lifts is
uninteresting and contributes the bulk of the code in this module.

```agda
instance
  Materialise-Bool : Materialise Bool
  Materialise-Bool = record where
    code  = twoⱽ (oneⱽ ∅ⱽ) ∅ⱽ one≠∅
    codes = Equiv.inverse Lift-≃

  Materialise-Nat : Materialise Nat
  Materialise-Nat = basic Natⱽ

  Materialise-⊤ : Materialise ⊤
  Materialise-⊤ = basic (realignⱽ (oneⱽ ∅ⱽ) lift λ p → refl)

  Materialise-⊥ : Materialise ⊥
  Materialise-⊥ = basic (realignⱽ ∅ⱽ lift λ p → hlevel!)

  Materialise-Σ
    : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
    → ⦃ _ : Materialise A ⦄ ⦃ _ : ∀ {x} → Materialise (B x) ⦄
    → Materialise (Σ A B)
  Materialise-Σ {ℓ = ℓ} {ℓ'} {A} {B} ⦃ a ⦄ ⦃ b ⦄ = record where
    module m = Materialise a
    module r = Equiv (liftⱽ.unraise ℓ' m.code)

    codes = Σ-ap (m.codes ∙e r.inverse) λ x →
      B x
        ≃⟨ b .codes ⟩
      Elⱽ (b {x} .code)
        ≃⟨ path→equiv (ap (λ e → Elⱽ (b {e} .code)) (sym (ap (Materialise.from a) (liftⱽ.unraise.ε ℓ' (a .code) _) ∙ Materialise.η a _))) ⟩
      Elⱽ (b {m.from (r.to (r.from (m.to x)))} .code)
        ≃⟨ liftⱽ.unraise.inverse ℓ (b .code) ⟩
      Elⱽ (liftⱽ ℓ (b {m.from (r.to (r.from (m.to x)))} .code))
        ≃∎

    code = Σⱽ
      (liftⱽ ℓ' (a .code))
      (λ i → liftⱽ ℓ (b {Materialise.from a (liftⱽ.unraise.to ℓ' (a .code) i)} .code))

  Materialise-Π
    : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
    → ⦃ _ : Materialise A ⦄ ⦃ _ : ∀ {x} → Materialise (B x) ⦄
    → Materialise ((x : A) → B x)
  Materialise-Π {ℓ} {ℓ'} {A} {B} ⦃ a ⦄ ⦃ b ⦄ = record where
    module m = Materialise a
    module r = Equiv (liftⱽ.unraise ℓ' m.code)

    codes =
      ((x : A) → B x)
        ≃⟨ Π-ap-dom (liftⱽ.unraise ℓ' m.code ∙e Equiv.inverse m.codes) ⟩
      ((x : Elⱽ (liftⱽ ℓ' m.code)) → B (m.from (r.to x)))
        ≃⟨ Π-ap-cod (λ x → b .codes) ⟩
      ((x : Elⱽ (liftⱽ ℓ' m.code)) → Elⱽ (b {m.from (r.to x)} .code))
        ≃⟨ Π-ap-cod (λ x → liftⱽ.unraise.inverse ℓ (b .code)) ⟩
      ((x : Elⱽ (liftⱽ ℓ' m.code)) → Elⱽ (liftⱽ ℓ (b {m.from (r.to x)} .code)))
        ≃∎

    code  = Πⱽ (liftⱽ ℓ' m.code) λ i → liftⱽ ℓ (b {m.from (r.to i)} .code)

  Materialise-Π'
    : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} ⦃ _ : Materialise A ⦄ ⦃ _ : ∀ {x} → Materialise (B x) ⦄
    → Materialise ({x : A} → B x)
  Materialise-Π' {A = A} {B = B} = Iso→materialisation {A = ∀ x → B x}
    ( (λ z x → z) , (iso (λ z {x} → z x) (λ f → refl) λ f → refl))

  Materialise-V : ∀ {ℓ} → Materialise (V ℓ)
  Materialise-V = record { code = Vⱽ ; codes = id≃ }

  Materialise-Ω : Materialise Ω
  Materialise-Ω = basic (realignⱽ (ℙⱽ (materialise! ⊤)) (λ w _ → w) (_·ₚ tt))

  Materialise-lift : ⦃ _ : Materialise A ⦄ → Materialise (Lift ℓ A)
  Materialise-lift {ℓ = ℓ} ⦃ m ⦄ = basic $ realignⱽ (liftⱽ ℓ (m .code))
    (λ x → liftⱽ.unraise.from ℓ (m .code) (m .codes .fst (x .lower)))
    (λ p → ap {B = λ _ → Lift _ _} lift
      (Equiv.injective (m .codes)
        (Equiv.injective (liftⱽ.unraise.inverse ℓ (m .code)) p)))
```

Note that we can materialise the identity types of an arbitrary [[set]],
not just of a materialisable set. More generally, we could materialise
any [[proposition]], but backtracking in Agda's instance search comes
with a significant performance penalty.

```agda
  Materialise-path : ∀ {ℓ} {A : Type ℓ} {x y : A} ⦃ _ : H-Level A 2 ⦄ → Materialise (x ≡ y)
  Materialise-path {x = x} {y = y} ⦃ m ⦄ = basic $ mkⱽ record where
    Elt   = (x ≡ y)
    idx p = ∅ⱽ
    inj _ = hlevel!
```

## A basic instance

Using a tactic argument, we can add an incoherent base instance which
materialises any type which is in the image of `El`{.Agda}. This can not
be an ordinary instance because `El`{.Agda} is not definitionally
injective (it does not determine the tree structure of the $V$-code), so
Agda will not invert it. However, when `El`{.Agda} is neutral, we can
*choose* to invert it in the obvious way ourselves, at a small
performance penalty.

```agda
private
  materialise-el : ∀ {ℓ} (A : Type ℓ) → Term → TC ⊤
  materialise-el A goal = quoteTC A >>= reduce >>= λ where
    (def (quote v-label.impl) (v-label-args x)) → unify goal (it basic ##ₙ x)
    a → typeError
      [ "Materialise: don't know how to come up with instance for\n  "
      , termErr a
      ]

instance
  Materialise-base : ∀ {ℓ} {A : Type ℓ} {@(tactic materialise-el A) it : Materialise A} → Materialise A
  {-# INCOHERENT Materialise-base #-}
  Materialise-base {it = it} = it
```

## Materialising record types

Using our existing helper `declare-record-iso`{.Agda} for exhibiting
record types as iterated $\Sigma$-types, we can write a metaprogram that
invents `Materialise`{.Agda} instances for records, given that all the
fields have materialisable types.

```agda
materialise-record : Name → Name → TC ⊤
materialise-record inst rec = do
  (rec-tele , _) ← pi-view <$> get-type rec

  eqv ← helper-function-name rec "iso"
  declare-record-iso eqv rec

  let
    args    = reverse $ map-up (λ n (_ , arg i _) → arg i (var₀ n)) 0 (reverse rec-tele)

    inst-ty = unpi-view (map (λ (nm , arg _ ty) → nm , argH ty) rec-tele) $
      it Materialise ##ₙ def rec args

  declare (argI inst) inst-ty
  define-function inst
    [ clause [] [] (it Iso→materialisation ##ₙ def₀ eqv) ]
```

As a demo, we can write a type of "$V$-categories", and define the
$V$-category of $V$-sets.

```agda
private
  record VCat ℓ ℓ' : Type (lsuc (ℓ ⊔ ℓ')) where
    field
      Ob  : V ℓ
      Hom : ⌞ Ob ⌟ → ⌞ Ob ⌟ → V ℓ'

      idⱽ  : ∀ {x}     → ⌞ Hom x x ⌟
      _∘ⱽ_ : ∀ {x y z} → ⌞ Hom y z ⌟ → ⌞ Hom x y ⌟ → ⌞ Hom x z ⌟

      idl : ∀ {x y} (f : ⌞ Hom x y ⌟) → idⱽ ∘ⱽ f ≡ f
      idr : ∀ {x y} (f : ⌞ Hom x y ⌟) → f ∘ⱽ idⱽ ≡ f

      assoc
        : ∀ {w x y z} (f : ⌞ Hom y z ⌟) (g : ⌞ Hom x y ⌟) (h : ⌞ Hom w x ⌟)
        → f ∘ⱽ (g ∘ⱽ h) ≡ (f ∘ⱽ g) ∘ⱽ h

  instance unquoteDecl demo = materialise-record demo (quote VCat)

  _ : Elⱽ (materialise! (VCat lzero lzero)) ≡ VCat lzero lzero
  _ = refl

  open VCat

  VSets : VCat (lsuc ℓ) ℓ
  VSets .Ob      = materialise! (V _)
  VSets .Hom X Y = materialise! (⌞ X ⌟ → ⌞ Y ⌟)

  VSets .idⱽ   = λ x → x
  VSets ._∘ⱽ_  = λ f g x → f (g x)

  VSets .idl   f     = refl
  VSets .idr   f     = refl
  VSets .assoc f g h = refl
```
