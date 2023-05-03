<!--
```agda
open import 1Lab.Path.IdentitySystem
open import 1Lab.HLevel.Retracts
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Data.Dec.Base
```
-->

```agda
module 1Lab.Path.IdentitySystem.Strict where
```

# Strict Identity Systems

[Identity systems] on `Sets`{.Agda ident=is-set} not only have their
own J eliminator, but also have their own version of the K eliminator!
This eliminator is normally added as an axiom to MLTT to squash any
homotopical content, but if the type already has no higher dimensional
structure, then we get it as a theorem.

[Identity systems]: 1Lab.Path.IdentitySystem.html

We begin by noting that if $A$ is a set equipped with an identity system
$R, r$, then the relation $R$ must be a proposition. We do this by
constructing a `PathP`{.Agda} from $s$ to $t$ that lies over some loop
$b = b$, and then using the fact that $A$ is a set to contract the loop
down to the reflexive path.

```agda
strict-identity-system→is-prop
  : ∀ {ℓ ℓ′} {A : Type ℓ} {R : A → A → Type ℓ′} {r : ∀ a → R a a} {a b : A}
  → is-identity-system R r
  → is-set A
  → is-prop (R a b)
strict-identity-system→is-prop {R = R} {a = a} {b = b} ids set s t =
  is-set→cast-pathp (λ b' → R a b') set $
  _∙P_ {B = λ b' → R a b'} (symP (ids .to-path-over s)) (ids .to-path-over t)
```

This immediately gives us the K eliminator for an identity system over a set:
given a family $P : A \to Type$, an element of that family at $r(a)$, and some
$s : R(a, a)$, we can transport the $P(r(a))$ to $P(s)$, as $R$ must be a proposition.

```agda
IdsK
  : ∀ {ℓ ℓ′ ℓ′′} {A : Type ℓ} {R : A → A → Type ℓ′} {r : ∀ a → R a a} {a : A}
  → is-identity-system R r
  → is-set A
  → (P : R a a → Type ℓ′′)
  → P (r a)
  → ∀ s → P s
IdsK {r = r} {a = a} ids set P pr s =
  transport (λ i → P (strict-identity-system→is-prop ids set (r a) s i)) pr
```

<!--
```agda
IdsK-refl
  : ∀ {ℓ ℓ′ ℓ′′} {A : Type ℓ} {R : A → A → Type ℓ′} {r : ∀ a → R a a} {a : A}
  → (ids : is-identity-system R r)
  → (set : is-set A)
  → (P : R a a → Type ℓ′′)
  → (x : P (r a))
  → IdsK ids set P x (r a) ≡ x
IdsK-refl {R = R} {r = r} {a = a} ids set P x =
  transport (λ i → P (strict-identity-system→is-prop ids set (r a) (r a) i)) x ≡⟨⟩
  subst P (strict-identity-system→is-prop ids set (r a) (r a)) x               ≡⟨ ap (λ ϕ → subst P ϕ x) lemma ⟩
  transport (λ i → P (r a)) x                                                  ≡⟨ transport-refl x ⟩
  x ∎
  where
    lemma : strict-identity-system→is-prop ids set (r a) (r a) ≡ refl
    lemma = is-prop→is-set (strict-identity-system→is-prop ids set) (r a) (r a) _ _
```
-->

<!--
```agda
module StrictIds
  {ℓ ℓ′} {A : Type ℓ} {R : A → A → Type ℓ′} {r : ∀ a → R a a}
  (ids : is-identity-system R r)
  (set : is-set A)
  where

  K : ∀ {ℓ′′} {a} → (P : R a a → Type ℓ′′) → P (r a) → ∀ s → P s
  K = IdsK ids set

  K-refl : ∀ {ℓ′′} {a} → (P : R a a → Type ℓ′′) → (x : P (r a)) → K P x (r a) ≡ x
  K-refl = IdsK-refl ids set

  instance
    R-H-level : ∀ {a b} {n} → H-Level (R a b) (1 + n)
    R-H-level = prop-instance (strict-identity-system→is-prop ids set)
```
-->
