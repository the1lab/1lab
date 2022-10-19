```agda
open import 1Lab.Reflection
open import 1Lab.Prelude

open import Data.List

module Principles.Resizing where
```

# Propositional Resizing

Ordinarily, the collection of all $\kappa$-small predicates on
$\kappa$-small types lives in the next universe up, $\kappa^+$. This is
because _predicates_ are not special in type theory: they are ordinary
type families, that just so happen to be valued in \r{propositions}. For
most purposes we can work with this limitation: this is called
**predicative mathematics**. But, for a few classes of theorems,
predicativity is too restrictive: Even if we don't have a single
universe of propositions that can accomodate all predicates, we would
still like for universes to be closed under power-sets.

Using some of Agda's more suspicious features, we can achieve this in a
way that does not break computation (too hard). Note that this is still
unsafe --- Agda's termination checker relies on predicativity --- so it
is just as unsafe as having a postulate, but with better computational
properties.

Our construction of the type $\Omega$ of small propositions factors
through implementing a^[nasty and evil] record type `Squish-prop`{.Agda}
which, despite storing a type $T$ from the $\ell$-th universe, lives in
the 0th universe. We're justified in doing this because $T$, being a
proposition, doesn't store a lot of information at all.

```agda
private
  {-# NO_UNIVERSE_CHECK #-}
  record Squish-prop ℓ : Type where
    no-eta-equality
    constructor el
    field
      ∣_∣ : Type ℓ
      is-tr : is-prop ∣_∣

open Squish-prop public
```

The first thing we'll establish is an \r{identity system} on the type of
squished propositions. This is a special case of transfer along
equivalences (and pullback of) identity systems: but note that since our
construction of `Squish-prop`{.Agda} is _necessarily_ special-cased, we
can not use our regular tools for constructing identity systems.

Our choice of relation is the humble biimplication: a pair of functions
that goes both ways. Between inhabitants of $\Omega$, these are exactly
the equivalences.

```agda
record _↔_ {ℓ ℓ′} (A : Type ℓ) (B : Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  constructor bi
  field
    to   : A → B
    from : B → A
```

<!--
```agda
Squish-bi-to-equiv
  : ∀ {ℓ ℓ′} (A : Squish-prop ℓ) (B : Squish-prop ℓ′)
  → (f : ∣ A ∣ ↔ ∣ B ∣)
  → is-equiv (f ._↔_.to)
Squish-bi-to-equiv _ B f .is-eqv y .centre = f ._↔_.from y , B .is-tr _ _
Squish-bi-to-equiv A B f .is-eqv y .paths x =
  Σ-prop-path (λ _ → is-prop→is-set (B .is-tr) _ _)
    (A .is-tr _ _)
module Bi = _↔_
open Bi
```
-->

A direct and fairly straightforward computation establishes that
biimplications are indeed an identity system on the type `Squish-prop`.
This includes, as usual, an appeal to univalence.

```agda
Squish-prop-univalence : ∀ {ℓ} → is-identity-system {A = Squish-prop ℓ}
  (λ a b → ∣ a ∣ ↔ ∣ b ∣)
  λ a → bi (λ x → x) (λ x → x)
Squish-prop-univalence .to-path {a} {b} biimp i .∣_∣ = ua (_ , Squish-bi-to-equiv a b biimp) i
Squish-prop-univalence .to-path {a} {b} biimp i .is-tr =
  is-prop→pathp (λ i → is-hlevel-is-prop {A = ua (_ , Squish-bi-to-equiv a b biimp) i} 1)
    (a .is-tr)
    (b .is-tr) i
Squish-prop-univalence .to-path-over {a} {b} p i .to x =
  outS (ua-glue (p .to , Squish-bi-to-equiv a b p) i (λ _ → x) (inS (p .to x)))
Squish-prop-univalence .to-path-over {a} {b} p i .from x = hcomp (∂ i) λ where
  j (j = i0) → p .from (ua-unglue (p .to , Squish-bi-to-equiv a b p) i x)
  j (i = i0) → a .is-tr (p .from (p .to x)) x j
  j (i = i1) → p .from x

Squish-prop-ua : ∀ {ℓ} {A B : Squish-prop ℓ} → ∣ A ∣ ↔ ∣ B ∣ → A ≡ B
Squish-prop-ua = Squish-prop-univalence .to-path

instance
  H-Level-Ω : ∀ {ℓ} {n} → H-Level (Squish-prop ℓ) (2 + n)
  H-Level-Ω = basic-instance 2 $ identity-system→hlevel 1 Squish-prop-univalence p where
    p : ∀ {ℓ} (x y : Squish-prop ℓ) (p q : ∣ x ∣ ↔ ∣ y ∣) → p ≡ q
    p x y p q i .to a = y .is-tr (p .to a) (q .to a) i
    p x y p q i .from a = x .is-tr (p .from a) (q .from a) i
```

## The type Ω

The type of small propositions, `Ω`, is `Squish-prop lzero`: the
squished type of propositions living in the zeroth universe. Using the
fact that `Squish-prop` is really small (thus has identity types also in
the zeroth universe), and the fact that every proposition $P$ is
equivalent to $P = \top$, we can implement a **propositional resizing**
construct, which moves propositions between arbitrary universe levels,
first by squishing, then by lifting.

```agda
Ω : Type
Ω = Squish-prop lzero
{-# DISPLAY Squish-prop lzero = Ω #-}

resize : ∀ {ℓ} ℓ′ → (T : Type ℓ) → is-prop T → Σ[ T′ ∈ Type ℓ′ ] (T′ ≃ T)
resize ℓ′ T x =
    Lift ℓ′ (Path (Squish-prop _) (el T x) (el (Lift _ ⊤) (λ _ _ _ → lift tt)))
  , prop-ext (hlevel 1) x
    (λ p → transport (ap ∣_∣ (sym (Lift.lower p))) (lift tt))
    λ t → lift (Squish-prop-ua (bi (λ _ → lift tt) (λ _ → t)))

elΩ : ∀ {ℓ} (A : Type ℓ) → is-prop A → Ω
∣ elΩ A A-prop ∣    = resize lzero A A-prop .fst
elΩ A A-prop .is-tr = is-hlevel≃ 1 (resize lzero A A-prop .snd) A-prop
```

<!--
```agda
elΩ!
  : ∀ {ℓ} (A : Type ℓ) {@(tactic hlevel-tactic-worker) aprop : is-hlevel A 1}
  → Ω
∣ elΩ! A {t} ∣ = resize lzero A t .fst
elΩ! A {t} .is-tr = is-hlevel≃ 1 (resize lzero _ _ .snd) t

elΩ-ua : ∀ {ℓ} {A B : Type ℓ} {ap bp} → (A → B) → (B → A) → elΩ A ap ≡ elΩ B bp
elΩ-ua f g = Squish-prop-ua $ bi
  (λ x → Equiv.from (resize _ _ _ .snd) (f (Equiv.to (resize _ _ _ .snd) x)))
  (λ x → Equiv.from (resize _ _ _ .snd) (g (Equiv.to (resize _ _ _ .snd) x)))

elΩₗ-ua : ∀ {ℓ} {A : Type ℓ} {B : Ω} {ap} → (A → ∣ B ∣) → (∣ B ∣ → A) → elΩ A ap ≡ B
elΩₗ-ua f g = Squish-prop-ua $ bi
  (λ x → f (Equiv.to (resize _ _ _ .snd) x))
  (λ x → Equiv.from (resize _ _ _ .snd) (g x))

true→elΩ : ∀ {ℓ} {A : Type ℓ} {ap : is-prop A} → A → ∣ elΩ A ap ∣
true→elΩ x = lift (Squish-prop-ua (bi (λ _ → _) λ _ → x))

elΩ→true : ∀ {ℓ} {A : Type ℓ} {ap : is-prop A} → ∣ elΩ A ap ∣ → A
elΩ→true x = transport (ap ∣_∣ (sym (Lift.lower x))) (lift tt)
```
-->

Another application of univalence comes in proving that the type
$\Omega$ indeed does classify subobjects: so, under the assumption that
$\Omega$ exists, we can safely put the type of all subobjects of a fixed
type $B$ in the same universe as $B$.

```agda
Ω-subobjects : ∀ {ℓ} {B : Type ℓ} → (Σ (Type ℓ) (_↪ B)) ≃ (B → Squish-prop ℓ)
Ω-subobjects {B = B} = Iso→Equiv im where
  open is-iso
  im : Iso (Σ (Type _) (_↪ B)) (B → Squish-prop _)
  im .fst (A , f) x = el (fibre (f .fst) x) (f .snd x)
  im .snd .inv P = (Σ B λ x → ∣ P x ∣) , fst , Subset-proj-embedding (λ x → is-tr (P x))
  im .snd .rinv P = funext λ x → Squish-prop-ua $ bi
    (λ x → subst (λ e → ∣ P e ∣) (x .snd) (x .fst .snd))
    (λ w → (x , w) , refl)
  im .snd .linv (B , f , e) = Σ-pathp
    (ua (Total-equiv f e⁻¹))
      (Σ-prop-pathp (λ i x → Π-is-hlevel 1 λ _ → is-hlevel-is-prop 1)
      (ua→ λ { (x , y , p) → sym p }))
```

<!--
```
_∈_ : ∀ {ℓ ℓ′} {A : Type ℓ} → A → (A → Prop ℓ′) → Type ℓ′
x ∈ P = ∣ P x ∣

-- Like the membership relation defined just above but taking values in
-- the first universe no matter how big the proposition is.
_∈ᵣ_ : ∀ {ℓ ℓ′} {A : Type ℓ} → A → (A → Squish-prop ℓ′) → Type
x ∈ᵣ P = ∣ (elΩ ∣ P x ∣ (P x .is-tr)) ∣

open hlevel-projection
instance
  hlevel-proj-squish-prop : hlevel-projection
  hlevel-proj-squish-prop .underlying-type = quote Squish-prop.∣_∣
  hlevel-proj-squish-prop .has-level = quote Squish-prop.is-tr
  hlevel-proj-squish-prop .get-level _ = returnTC 1
  hlevel-proj-squish-prop .get-argument (_ ∷ t v∷ []) = pure  t
  hlevel-proj-squish-prop .get-argument _ = typeError []

module _ (A B : Ω) where
  _ : is-prop ∣ A ∣
  _ = hlevel!

  _ : is-prop (∣ A ∣ → ∣ B ∣)
  _ = hlevel!

  _ : ∀ {A : Type} (F : A → Ω) → is-prop (∀ x → ∣ F x ∣)
  _ = λ _ → hlevel!

  _ : Ω
  _ = elΩ! (∣ A ∣ × ∣ B ∣)
```
-->
