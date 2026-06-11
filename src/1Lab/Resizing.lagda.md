<!--
```agda
open import 1Lab.Function.Surjection
open import 1Lab.Path.IdentitySystem
open import 1Lab.Reflection.HLevel
open import 1Lab.HLevel.Universe
open import 1Lab.Extensionality
open import 1Lab.HLevel.Closure
open import 1Lab.Reflection using (arg ; typeError)
open import 1Lab.Truncation
open import 1Lab.Univalence
open import 1Lab.Inductive
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Data.List.Base
open import Data.Sum.Base

open import Meta.Idiom
open import Meta.Bind
```
-->

```agda
module 1Lab.Resizing where
```

# Propositional resizing {defines="propositional-resizing"}

Ordinarily, the collection of all $\kappa$-small predicates on
$\kappa$-small types lives in the next universe up, $\kappa^+$. This is
because _predicates_ are not special in type theory: they are ordinary
type families, that just so happen to be valued in [[propositions]]. For
most purposes we can work with this limitation: this is called
**predicative mathematics**. But, for a few classes of theorems,
predicativity is too restrictive: Even if we don't have a single
universe of propositions that can accommodate all predicates, we would
still like for universes to be closed under power-sets.

Using a handful of unsafe features, we can achieve this in a way which
does not break closed computation too much.  Specifically, we can use
the evil `NO_UNIVERSE_CHECK` pragma: We define the **small type of
propositions**, `Ω`, to be a record containing a `Type` (together with
an irrelevant proof that this type is a proposition), but contrary to
the universe checker, which would like us to put `Ω : Type₁`, we instead
force `Ω : Type`.

```agda
{-# NO_UNIVERSE_CHECK #-}
record Ω : Type where
  constructor el
  field
    ∣_∣   : Type
    is-tr : is-prop ∣_∣
open Ω public
```

This type, a priori, only contains the propositions whose underlying
type lives in the first universe. However, we can populate it using a
second `NO_UNIVERSE_CHECK` pragma, this time forcing the [[propositional
truncation]] of an arbitrary type into the first universe.

```agda
{-# NO_UNIVERSE_CHECK #-}
data □ {ℓ} (A : Type ℓ) : Type where
  inc    : A → □ A
  squash : (x y : □ A) → x ≡ y
```

Just like the ordinary propositional truncation, every type can be
squashed, but unlike the ordinary propositional truncation, the
`□`{.Agda}-squashing of a type always lives in the lowest universe. Thus
if $T$ is a proposition in any universe, $\Box T$ is its name in the
zeroth universe.

<!--
```agda
instance
  H-Level-□ : ∀ {ℓ} {T : Type ℓ} {n} → H-Level (□ T) (suc n)
  H-Level-□ = prop-instance squash

  open hlevel-projection
  Ω-hlevel-proj : hlevel-projection (quote Ω.∣_∣)
  Ω-hlevel-proj .has-level = quote Ω.is-tr
  Ω-hlevel-proj .get-level x = pure (quoteTerm (suc zero))
  Ω-hlevel-proj .get-argument (arg _ t ∷ _) = pure t
  Ω-hlevel-proj .get-argument _ = typeError []
```
-->

We can also prove a univalence principle for `Ω`{.Agda}: if $A, B :
\Omega$ are logically equivalent, then they are equal.

```agda
Ω-ua : {A B : Ω} → (∣ A ∣ → ∣ B ∣) → (∣ B ∣ → ∣ A ∣) → A ≡ B
Ω-ua {A} {B} f g i .∣_∣ = ua (prop-ext! f g) i
Ω-ua {A} {B} f g i .is-tr =
  is-prop→pathp (λ i → is-prop-is-prop {A = ua (prop-ext! f g) i})
    (A .is-tr) (B .is-tr) i

instance abstract
  H-Level-Ω : ∀ {n} → H-Level Ω (2 + n)
  H-Level-Ω = basic-instance 2 $ retract→is-hlevel 2
    (λ r → el ∣ r ∣ (r .is-tr))
    (λ r → el ∣ r ∣ (r .is-tr))
    (λ x → Ω-ua id id)
    (n-Type-is-hlevel {lzero} 1)
```

The `□`{.Agda} type former is a functor (in the handwavy sense that it
supports a "map" operation), and can be projected from into propositions
of any universe. These functions compute on `inc`{.Agda}s, as usual.

```agda
□-map : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
      → (A → B) → □ A → □ B
□-map f (inc x) = inc (f x)
□-map f (squash x y i) = squash (□-map f x) (□-map f y) i

□-rec : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → is-prop B → (A → B) → □ A → B
□-rec bp f (inc x)        = f x
□-rec bp f (squash x y i) = bp (□-rec bp f x) (□-rec bp f y) i

elΩ : ∀ {ℓ} (T : Type ℓ) → Ω
elΩ T .∣_∣ = □ T
elΩ T .is-tr = squash
```

<!--
```agda
□-elim
  : ∀ {ℓ ℓ'} {A : Type ℓ} {P : □ A → Type ℓ'}
  → (∀ x → is-prop (P x))
  → (∀ x → P (inc x))
  → ∀ x → P x
□-elim pprop go (inc x) = go x
□-elim pprop go (squash x y i) =
  is-prop→pathp (λ i → pprop (squash x y i)) (□-elim pprop go x) (□-elim pprop go y) i

instance
  Inductive-□
    : ∀ {ℓ ℓ' ℓm} {A : Type ℓ} {P : □ A → Type ℓ'} ⦃ i : Inductive (∀ x → P (inc x)) ℓm ⦄
    → ⦃ _ : ∀ {x} → H-Level (P x) 1 ⦄
    → Inductive (∀ x → P x) ℓm
  Inductive-□ ⦃ i ⦄ = record
    { methods = i .Inductive.methods
    ; from    = λ f → □-elim (λ x → hlevel 1) (i .Inductive.from f)
    }

□-out : ∀ {ℓ} {A : Type ℓ} → is-prop A → □ A → A
□-out ap = □-rec ap (λ x → x)

□-out!
  : ∀ {ℓ} {A : Type ℓ}
  → ⦃ _ : H-Level A 1 ⦄
  → □ A → A
□-out! = rec! λ x → x

□-out-rec : ∀ {ℓ ℓ'} {A : Type ℓ} {X : Type ℓ'} → is-prop A → (A → X) → □ A → X
□-out-rec A-prop go x = go (□-out A-prop x)

□-out-elim
  : ∀ {ℓ ℓ'} {A : Type ℓ} {P : □ A → Type ℓ'}
  → is-prop A
  → (∀ x → P (inc x))
  → ∀ x → P x
□-out-elim {P = P} A-prop go x =
  subst P prop! (go (□-out A-prop x))

□-rec-set
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → is-set B
  → (f : A → B)
  → (∀ x y → f x ≡ f y)
  → □ A → B
□-rec-set B-set f f-const a =
  fst $ □-elim
    (λ _ → is-constant→image-is-prop B-set f f-const)
    (λ a → f a , inc (a , refl))
    a

□-idempotent : ∀ {ℓ} {A : Type ℓ} → is-prop A → □ A ≃ A
□-idempotent aprop = prop-ext squash aprop (□-out aprop) inc

□-ap
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → □ (A → B) → □ A → □ B
□-ap (inc f) (inc g) = inc (f g)
□-ap (inc f) (squash g g' i) = squash (□-ap (inc f) g) (□-ap (inc f) g') i
□-ap (squash f f' i) g = squash (□-ap f g) (□-ap f' g) i

□-bind
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → □ A → (A → □ B) → □ B
□-bind (inc x) f = f x
□-bind (squash x x' i) f = squash (□-bind x f) (□-bind x' f) i

instance
  Map-□ : Map (eff □)
  Map-□ .Map.map = □-map

  Idiom-□ : Idiom (eff □)
  Idiom-□ .Idiom.pure = inc
  Idiom-□ .Idiom._<*>_ = □-ap

  Bind-□ : Bind (eff □)
  Bind-□ .Bind._>>=_ = □-bind

is-set→locally-small
  : ∀ {ℓ} {A : Type ℓ}
  → is-set A
  → is-identity-system {A = A} (λ x y → □ (x ≡ y)) (λ x → inc refl)
is-set→locally-small a-set .to-path = □-rec (a-set _ _) id
is-set→locally-small a-set .to-path-over p = is-prop→pathp (λ _ → squash) _ _

to-is-true
  : ∀ {P Q : Ω} ⦃ _ : H-Level ∣ Q ∣ 0 ⦄
  → ∣ P ∣
  → P ≡ Q
to-is-true prf = Ω-ua (λ _ → hlevel!) λ _ → prf

tr-□ : ∀ {ℓ} {A : Type ℓ} → ∥ A ∥ → □ A
tr-□ (inc x) = inc x
tr-□ (squash x y i) = squash (tr-□ x) (tr-□ y) i

□-tr : ∀ {ℓ} {A : Type ℓ} → □ A → ∥ A ∥
□-tr (inc x) = inc x
□-tr (squash x y i) = squash (□-tr x) (□-tr y) i
```
-->

## Connectives

The universe of small propositions contains true, false, conjunctions,
disjunctions, and (bi)implications.

<!--
```agda
infixr 10 _∧Ω_
infixr 9 _∨Ω_
infixr 8 _→Ω_
```
-->

```agda
⊤Ω : Ω
∣ ⊤Ω ∣ = ⊤
⊤Ω .is-tr = hlevel 1

⊥Ω : Ω
∣ ⊥Ω ∣ = ⊥
⊥Ω .is-tr = hlevel 1

_∧Ω_ : Ω → Ω → Ω
∣ P ∧Ω Q ∣ = ∣ P ∣ × ∣ Q ∣
(P ∧Ω Q) .is-tr = hlevel 1

_∨Ω_ : Ω → Ω → Ω
∣ P ∨Ω Q ∣ = ∥ ∣ P ∣ ⊎ ∣ Q ∣ ∥
(P ∨Ω Q) .is-tr = hlevel 1

_→Ω_ : Ω → Ω → Ω
∣ P →Ω Q ∣ = ∣ P ∣ → ∣ Q ∣
(P →Ω Q) .is-tr = hlevel 1

¬Ω_ : Ω → Ω
¬Ω P = P →Ω ⊥Ω
```

Furthermore, we can quantify over types of arbitrary size and still
land in `Ω`.

```agda
∃Ω : ∀ {ℓ} (A : Type ℓ) → (A → Ω) → Ω
∣ ∃Ω A P ∣ = □ (Σ[ x ∈ A ] ∣ P x ∣)
∃Ω A P .is-tr = squash

∀Ω : ∀ {ℓ} (A : Type ℓ) → (A → Ω) → Ω
∣ ∀Ω A P ∣ = □ (∀ (x : A) → ∣ P x ∣)
∀Ω A P .is-tr = squash

syntax ∃Ω A (λ x → B) = ∃Ω[ x ∈ A ] B
syntax ∀Ω A (λ x → B) = ∀Ω[ x ∈ A ] B
```

<!--
```agda
instance
  Extensional-Σ-□
    : ∀ {ℓ ℓ' ℓr} {A : Type ℓ} {B : A → Type ℓ'}
    → ⦃ ea : Extensional A ℓr ⦄ → Extensional (Σ A λ x → □ (B x)) ℓr
  Extensional-Σ-□ ⦃ ea ⦄ = Σ-prop-extensional (λ x → hlevel 1) ea
```
-->

These connectives and quantifiers are only provided for completeness;
if you find yourself building nested propositions, it is generally a good
idea to construct the large proposition by hand, and then use truncation
to turn it into a small proposition.

<!--
```agda
module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) where
  Ω-image : Type ℓ'
  Ω-image = Σ[ b ∈ B ] □ (fibre f b)

  Ω-corestriction : A → Ω-image
  Ω-corestriction a = f a , inc (a , refl)

  opaque
    Ω-corestriction-is-surjective : is-surjective Ω-corestriction
    Ω-corestriction-is-surjective = elim! λ y x fx=y → pure (x , Σ-prop-path! fx=y)
```
-->
