<!--
```agda
open import 1Lab.Equiv.Embedding
open import 1Lab.Equiv.Fibrewise
open import 1Lab.HLevel.Retracts
open import 1Lab.Path.Groupoid
open import 1Lab.Type.Sigma
open import 1Lab.Univalence
open import 1Lab.Type.Pi
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.Path.IdentitySystem where
```

# Identity systems

An **identity system** is a way of characterising the path spaces of a
particular type, without necessarily having to construct a full
encode-decode equaivalence. Essentially, the data of an identity system
is precisely the data required to implement _path induction_, a.k.a. the
J eliminator. Any type with the data of an identity system satisfies its
own J, and conversely, if the type satisfies J, it is an identity
system.

We unravel the definition of being an identity system into the following
data, using a translation that takes advantage of cubical type theory's
native support for paths-over-paths:

```agda
record
  is-identity-system {ℓ ℓ′} {A : Type ℓ}
    (R : A → A → Type ℓ′)
    (refl : ∀ a → R a a)
    : Type (ℓ ⊔ ℓ′)
  where
  no-eta-equality
  field
    to-path      : ∀ {a b} → R a b → a ≡ b
    to-path-over
      : ∀ {a b} (p : R a b)
      → PathP (λ i → R a (to-path p i)) (refl a) p

  is-contr-ΣR : ∀ {a} → is-contr (Σ A (R a))
  is-contr-ΣR .centre    = _ , refl _
  is-contr-ΣR .paths x i = to-path (x .snd) i , to-path-over (x .snd) i

open is-identity-system public
```

As mentioned before, the data of an identity system gives is exactly
what is required to prove J for the relation $R$. This is essentially
the decomposition of J into _contractibility of singletons_, but with
singletons replaced by $R$-singletons.

```agda
IdsJ
  : ∀ {ℓ ℓ′ ℓ′′} {A : Type ℓ} {R : A → A → Type ℓ′} {r : ∀ a → R a a} {a : A}
  → is-identity-system R r
  → (P : ∀ b → R a b → Type ℓ′′)
  → P a (r a)
  → ∀ {b} s → P b s
IdsJ ids P pr s =
  transport (λ i → P (ids .to-path s i) (ids .to-path-over s i)) pr
```

<!--
```agda
IdsJ-refl
  : ∀ {ℓ ℓ′ ℓ′′} {A : Type ℓ} {R : A → A → Type ℓ′} {r : ∀ a → R a a} {a : A}
  → (ids : is-identity-system R r)
  → (P : ∀ b → R a b → Type ℓ′′)
  → (x : P a (r a))
  → IdsJ ids P x (r a) ≡ x
IdsJ-refl {R = R} {r = r} {a = a} ids P x =
  transport (λ i → P (ids .to-path (r a) i) (ids .to-path-over (r a) i)) x ≡⟨⟩
  subst P′ (λ i → ids .to-path (r a) i , ids .to-path-over (r a) i) x      ≡⟨ ap (λ e → subst P′ e x) lemma ⟩
  subst P′ refl x                                                          ≡⟨ transport-refl x ⟩
  x ∎
  where
    P′ : Σ _ (R a) → Type _
    P′ (b , r) = P b r

    lemma : Σ-pathp (ids .to-path (r a)) (ids .to-path-over (r a)) ≡ refl
    lemma = is-prop→is-set (is-contr→is-prop (is-contr-ΣR ids)) _ _ _ _

to-path-refl
  : ∀ {ℓ ℓ′} {A : Type ℓ} {R : A → A → Type ℓ′} {r : ∀ a → R a a} {a : A}
  → (ids : is-identity-system R r)
  → ids .to-path (r a) ≡ refl
to-path-refl {r = r} {a = a} ids = ap (ap fst) $
  is-prop→is-set (is-contr→is-prop (is-contr-ΣR ids)) (a , r a) (a , r a)
    (Σ-pathp (ids .to-path (r a)) (ids .to-path-over (r a)))
    refl
```
-->

If we have a relation $R$ together with reflexivity witness $r$, then
any equivalence $f : R(a, b) \simeq (a \equiv b)$ which maps $f(r) =
\id{refl}$ equips $(R, r)$ with the structure of an identity system. Of
course if we do not particularly care about the specific reflexivity
witness, we can simply define $r$ as $f^{-1}(\id{refl})$.

```agda
equiv-path→identity-system
  : ∀ {ℓ ℓ′} {A : Type ℓ} {R : A → A → Type ℓ′} {r : ∀ a → R a a}
  → (eqv : ∀ {a b} → R a b ≃ (a ≡ b))
  → (∀ a → Equiv.from eqv refl ≡ r a)
  → is-identity-system R r
equiv-path→identity-system {R = R} {r = r} eqv pres′ = ids where
  contract : ∀ {a} → is-contr (Σ _ (R a))
  contract = is-hlevel≃ 0 ((total (λ _ → eqv .fst) , equiv→total (eqv .snd)) e⁻¹)
    (contr _ Singleton-is-contr)

  pres : ∀ {a} → eqv .fst (r a) ≡ refl
  pres {a = a} = Equiv.injective₂ (eqv e⁻¹) (Equiv.η eqv _) (pres′ _)

  ids : is-identity-system R r
  ids .to-path = eqv .fst
  ids .to-path-over {a = a} {b = b} p i =
    is-prop→pathp
    (λ i → is-contr→is-prop (eqv .snd .is-eqv λ j → eqv .fst p (i ∧ j)))
    (r a , pres)
    (p , refl)
    i .fst
```

Note that for any $(R, r)$, the type of identity sytem data on $(R, r)$
is a proposition. This is because it is exactly equivalent to the type
$\sum_a (R a)$ being contractible for every $a$, which is a proposition
by standard results.

```agda
identity-system-gives-path
  : ∀ {ℓ ℓ′} {A : Type ℓ} {R : A → A → Type ℓ′} {r : ∀ a → R a a}
  → is-identity-system R r
  → ∀ {a b} → R a b ≃ (a ≡ b)
identity-system-gives-path ids {a = a} =
  ids .to-path {a = a}
  , total→equiv {f = λ x → ids .to-path {a = a} {b = x}}
    (is-contr→is-equiv (is-contr-ΣR ids) (contr _ Singleton-is-contr))
```

## In subtypes

Let $f : A \mono B$ be an embedding. If $(R, r)$ is an identity system
on $B$, then it can be pulled back along $f$ to an identity system on
$A$.

```agda
module
  _ {ℓ ℓ′ ℓ′′} {A : Type ℓ} {B : Type ℓ′}
    {R : B → B → Type ℓ′′} {r : ∀ a → R a a}
    (ids : is-identity-system R r)
    (f : A ↪ B)
  where

  pullback-identity-system
    : is-identity-system (λ x y → R (f .fst x) (f .fst y)) (λ _ → r _)
  pullback-identity-system .to-path {a} {b} x = ap fst $
    f .snd (f .fst b) (a , ids .to-path x) (b , refl)
  pullback-identity-system .to-path-over {a} {b} p i =
    comp
      (λ j → R (f .fst a) (f .snd (f .fst b) (a , ids .to-path p) (b , refl) i .snd (~ j)))
      (∂ i) λ where
      k (k = i0) → ids .to-path-over p (~ k)
      k (i = i0) → ids .to-path-over p (~ k ∨ i)
      k (i = i1) → p
```

## Univalence

Note that univalence is precisely the statement that equivalences are an
identity system on the universe:

```agda
univalence-identity-system
  : ∀ {ℓ} → is-identity-system {A = Type ℓ} _≃_ λ _ → id , id-equiv
univalence-identity-system .to-path = ua
univalence-identity-system .to-path-over p =
  Σ-prop-pathp (λ _ → is-equiv-is-prop) $ funextP $ λ a → path→ua-pathp p refl
```
