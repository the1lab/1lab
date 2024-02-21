<!--
```agda
open import 1Lab.Path.IdentitySystem
open import 1Lab.HLevel.Closure
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.Path.IdentitySystem.Strict where
```

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A : Type ℓ'
  R : A → A → Type ℓ'
  r : ∀ a → R a a
```
-->

# Strict identity systems

Since [[identity systems]] are a tool for classifying identity _types_,
the relation underlying an identity system enjoys any additional
property that the type's own identity type enjoys. As a prominent
example, if $(R, r)$ is an identity system on a [[set]], then $R$
satisfies not only J, but also K: any property $P(x)$ for $x : R(a,a)$,
for _fixed_ $a$, follows from $P(r)$.

Since $(R, r)$ is equivalent to $(\equiv_A, \refl)$, if $A$ is a set,
then $R$ must be a proposition as well.

```agda
set-identity-is-prop
  : ∀ {r : (a : A) → R a a} {a b : A}
  → is-identity-system R r
  → is-set A
  → is-prop (R a b)
set-identity-is-prop {R = R} {a = a} {b = b} ids set =
  Equiv→is-hlevel 1 (identity-system-gives-path ids) (set a b)
```

This immediately gives us the K eliminator for an identity system over a
set: Given a type family $P : R(a, a) \to \ty$ and a witness $w :
P(r(a))$, since $R(-,-)$ is a proposition, we can transport $w$ to
$P(s)$ for an arbitrary $s : R(a,a)$.

```agda
IdsK
  : {r : (a : A) → R a a} {a : A}
  → is-identity-system R r
  → is-set A
  → (P : R a a → Type ℓ'') → P (r a) → ∀ s → P s
IdsK {r = r} {a = a} ids set P pr s =
  transport (λ i → P (set-identity-is-prop ids set (r a) s i)) pr
```

<!--
```agda
IdsK-refl
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {R : A → A → Type ℓ'} {r : ∀ a → R a a} {a : A}
  → (ids : is-identity-system R r)
  → (set : is-set A)
  → (P : R a a → Type ℓ'')
  → (x : P (r a))
  → IdsK ids set P x (r a) ≡ x
IdsK-refl {R = R} {r = r} {a = a} ids set P x =
  transport (λ i → P (set-identity-is-prop ids set (r a) (r a) i)) x ≡⟨⟩
  subst P (set-identity-is-prop ids set (r a) (r a)) x               ≡⟨ ap (λ ϕ → subst P ϕ x) lemma ⟩
  transport (λ i → P (r a)) x                                        ≡⟨ transport-refl x ⟩
  x ∎
  where
    lemma : set-identity-is-prop ids set (r a) (r a) ≡ refl
    lemma = is-prop→is-set (set-identity-is-prop ids set) (r a) (r a) _ _
```
-->

<!--
```agda
module StrictIds
  {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'} {r : ∀ a → R a a}
  (ids : is-identity-system R r)
  (set : is-set A)
  where

  K : ∀ {ℓ''} {a} → (P : R a a → Type ℓ'') → P (r a) → ∀ s → P s
  K = IdsK ids set

  K-refl : ∀ {ℓ''} {a} → (P : R a a → Type ℓ'') → (x : P (r a)) → K P x (r a) ≡ x
  K-refl = IdsK-refl ids set

  instance
    R-H-level : ∀ {a b} {n} → H-Level (R a b) (1 + n)
    R-H-level = prop-instance (set-identity-is-prop ids set)
```
-->
