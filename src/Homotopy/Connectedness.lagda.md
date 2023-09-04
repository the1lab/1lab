<!--
```agda
open import 1Lab.Reflection.HLevel
open import 1Lab.HLevel.Retracts
open import 1Lab.HIT.Truncation
open import 1Lab.Type.Pointed
open import 1Lab.Underlying
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type

open import Algebra.Group.Cat.Base
open import Algebra.Group.Homotopy

open import Data.Set.Truncation

open import Homotopy.Space.Suspension
open import Homotopy.Space.Circle
open import Homotopy.Space.Sphere
open import Homotopy.Base
```
-->

```agda
module Homotopy.Connectedness where
```

# Connectedness {defines="connected connectedness connectivity simply-connected"}

We say that a type is **$n$-connected** if its $n$-[[truncation]] is [[contractible]].

While being $n$-[[truncated]] expresses that all homotopy groups above $n$ are trivial,
being $n$-connected means that all homotopy *below* $n$ are trivial.
A type that is both $n$-truncated and $n$-connected is contractible.

We give definitions in terms of the [[propositional truncation]] and [[set truncation]]
for the lower levels, and then defer to the general "hubs and spokes" truncation.
Note that our indices are offset by 2, just like [[h-levels]].

```agda
is-n-connected : ∀ {ℓ} → Type ℓ → Nat → Type _
is-n-connected A zero = Lift _ ⊤
is-n-connected A (suc zero) = ∥ A ∥
is-n-connected A (suc (suc zero)) = is-contr ∥ A ∥₀
is-n-connected A n@(suc (suc (suc _))) = is-contr (n-Tr A n)
```

Being $n$-connected is a proposition:

```agda
is-n-connected-is-prop : ∀ {ℓ} {A : Type ℓ} (n : Nat) → is-prop (is-n-connected A n)
is-n-connected-is-prop zero _ _ = refl
is-n-connected-is-prop (suc zero) = is-prop-∥-∥
is-n-connected-is-prop (suc (suc zero)) = is-contr-is-prop
is-n-connected-is-prop (suc (suc (suc n))) = is-contr-is-prop
```

For short, we say that a type is **connected** if it is $0$-connected, and
**simply connected** if it is $1$-connected:

```agda
is-connected : ∀ {ℓ} → Type ℓ → Type _
is-connected A = is-n-connected A 2

is-simply-connected : ∀ {ℓ} → Type ℓ → Type _
is-simply-connected A = is-n-connected A 3
```

## Pointed connected types

In the case of [[pointed types]], there is an equivalent definition of being connected
that is sometimes easier to work with: a pointed type is connected if every point is
merely equal to the base point.

```agda
is-connected∙ : ∀ {ℓ} → Type∙ ℓ → Type _
is-connected∙ (X , pt) = (x : X) → ∥ x ≡ pt ∥

module _ {ℓ} {X@(_ , pt) : Type∙ ℓ} where
  is-connected∙→is-connected : is-connected∙ X → is-connected ⌞ X ⌟
  is-connected∙→is-connected c .centre = inc pt
  is-connected∙→is-connected c .paths =
    ∥-∥₀-elim hlevel! λ x → ∥-∥-rec! (ap inc ∘ sym) (c x)

  is-connected→is-connected∙ : is-connected ⌞ X ⌟ → is-connected∙ X
  is-connected→is-connected∙ c x =
    ∥-∥₀-path.to (is-contr→is-prop c (inc x) (inc pt))
```

This alternative definition lets us formulate a nice elimination principle for pointed
connected types: any family of propositions $P$ that holds on the base point holds everywhere.
In particular, since `being a proposition is a proposition`{.Agda ident=is-prop-is-prop},
we only need to check that $P(\point{})$ is a proposition.

```agda
connected∙-elim-prop
  : ∀ {ℓ ℓ′} {X : Type∙ ℓ} {P : ⌞ X ⌟ → Type ℓ′}
  → is-connected∙ X
  → is-prop (P (X .snd))
  → P (X .snd)
  → ∀ x → P x
connected∙-elim-prop {X = X} {P} conn prop pb x =
  ∥-∥-rec (P-is-prop x) (λ e → subst P (sym e) pb) (conn x)
  where abstract
    P-is-prop : ∀ x → is-prop (P x)
    P-is-prop x = ∥-∥-rec is-prop-is-prop (λ e → subst (is-prop ∘ P) (sym e) prop) (conn x)
```

Examples of pointed connected types include the [[circle]] and the [[delooping]] of a group.

```agda
S¹-is-connected : is-connected∙ (S¹ , base)
S¹-is-connected = S¹-elim (inc refl) prop!

Deloop-is-connected : ∀ {ℓ} {G : Group ℓ} → is-connected∙ (Deloop G , base)
Deloop-is-connected = Deloop-elim-prop _ _ hlevel! (inc refl)
```
