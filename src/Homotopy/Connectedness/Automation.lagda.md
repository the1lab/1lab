<!--
```agda
open import 1Lab.Prelude

open import Data.Nat.Properties

open import Homotopy.Connectedness
```
-->

```agda
module Homotopy.Connectedness.Automation where
```

# Automation

Just like for [h-levels], we can leverage Agda's instance search to make
proving things about $n$-[[connected]] types easier.
The only difference is that the offsetting goes the other way, since
connectedness is *downwards*-closed.

[h-levels]: 1Lab.HLevel.Closure.html#automation

```agda
record Connected {ℓ} (T : Type ℓ) (n : Nat) : Type ℓ where
  constructor conn-instance
  field
    has-n-connected : is-n-connected T n

n-connected : ∀ {ℓ} {T : Type ℓ} n ⦃ x : Connected T n ⦄ → is-n-connected T n
n-connected n ⦃ c ⦄ = Connected.has-n-connected c

basic-conn-instance
  : ∀ {ℓ} {T : Type ℓ} n {k}
  → is-n-connected T (n + k) → Connected T n
basic-conn-instance {T = T} n {k} c = conn-instance (is-connected-+ n k
  (subst (is-n-connected T) (+-commutative n k) c))

connected : ∀ {ℓ} {T : Type ℓ} → ⦃ Connected T 2 ⦄
  → ∀ (a b : T) → ∥ a ≡ b ∥
connected ⦃ conn-instance c ⦄ a b =
  n-connected-∥-∥.to 2 c .snd a b .fst

simply-connected : ∀ {ℓ} {T : Type ℓ} → ⦃ Connected T 3 ⦄
  → ∀ {a b : T} (p q : a ≡ b) → ∥ p ≡ q ∥
simply-connected ⦃ conn-instance c ⦄ {a} {b} p q =
  n-connected-∥-∥.to 3 c .snd a b .snd p q .fst

is-contr→is-connected
  : ∀ {ℓ} {A : Type ℓ} → is-contr A
  → ∀ {n} → is-n-connected-∥-∥ A n
is-contr→is-connected c {zero} = _
is-contr→is-connected c {suc n} .fst = inc (c .centre)
is-contr→is-connected c {suc n} .snd _ _ =
  is-contr→is-connected (Path-is-hlevel 0 c)

instance
  -- Note that this overlaps with other instances, but Agda doesn't mind
  -- because all instances of Connected A 0 are equal!
  0-Connected : ∀ {ℓ} {A : Type ℓ} → Connected A 0
  0-Connected = _

  Connected-⊤ : ∀ {n} → Connected ⊤ n
  Connected-⊤ {n} = conn-instance (n-connected-∥-∥.from n
    (is-contr→is-connected (hlevel 0)))

  Connected-Σ
    : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {n}
    → ⦃ Connected A n ⦄ → ⦃ ∀ {a} → Connected (B a) n ⦄
    → Connected (Σ A B) n
  Connected-Σ {n = n} ⦃ conn-instance ac ⦄ ⦃ bc ⦄ = conn-instance
    (Σ-is-n-connected n ac λ _ → Connected.has-n-connected bc)

  Connected-Path
    : ∀ {ℓ} {A : Type ℓ} {x y : A} {n}
    → ⦃ Connected A (suc n) ⦄
    → Connected (Path A x y) n
  Connected-Path {n = n} ⦃ conn-instance ac ⦄ = conn-instance
    (Path-is-connected n ac)
```
