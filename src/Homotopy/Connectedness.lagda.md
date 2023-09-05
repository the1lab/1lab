<!--
```agda
open import 1Lab.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Group.Homotopy

open import Data.Set.Truncation

open import Homotopy.Space.Delooping
open import Homotopy.Space.Circle
open import Homotopy.Base
```
-->

```agda
module Homotopy.Connectedness where
```

# Connectedness {defines="connected connectedness connectivity simply-connected"}

We say that a type is **$n$-connected** if its $n$-[[truncation]] is [[contractible]].

While being $n$-[[truncated]] expresses that all homotopy groups above $n$ are trivial,
being $n$-connected means that all homotopy groups *below* $n$ are trivial.
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
    ∥-∥₀-elim (λ _ → is-hlevel-suc 2 squash (inc pt) _) λ x →
      ∥-∥-rec! {pprop = squash _ _} (ap inc ∘ sym) (c x)

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

```agda
is-n-connected-map : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → Nat → Type _
is-n-connected-map f n = ∀ x → is-n-connected (fibre f x) n

is-n-connected-Tr : ∀ {ℓ} {A : Type ℓ} n → is-n-connected A (suc n) → is-contr (n-Tr A (suc n))
is-n-connected-Tr zero a-conn = ∥-∥-proj do
  pt ← a-conn
  pure $ contr (inc pt) (λ x → n-Tr-is-hlevel 0 _ _)
is-n-connected-Tr (suc zero) a-conn =
  retract→is-hlevel 0
    (∥-∥₀-rec (n-Tr-is-hlevel 1) inc)
    (n-Tr-rec squash inc)
    (n-Tr-elim _ (λ _ → is-prop→is-set (n-Tr-is-hlevel 1 _ _)) λ _ → refl)
    a-conn
is-n-connected-Tr (suc (suc n)) a-conn = a-conn

is-n-connected-Tr-is-equiv : ∀ {ℓ} {A : Type ℓ} n → is-equiv (is-n-connected-Tr {A = A} n)
is-n-connected-Tr-is-equiv {A = A} n = prop-ext (is-n-connected-is-prop _) (hlevel 1) _ (from n) .snd where
  from : ∀ n → is-contr (n-Tr A (suc n)) → is-n-connected A (suc n)
  from zero c = n-Tr-elim (λ _ → ∥ A ∥) (λ _ → squash) inc (c .centre)
  from (suc zero) =
    retract→is-hlevel 0
      (n-Tr-rec squash inc)
      (∥-∥₀-rec (n-Tr-is-hlevel 1) inc)
      (∥-∥₀-elim (λ _ → is-prop→is-set (squash _ _)) λ _ → refl)
  from (suc (suc n)) x = x

module is-n-connected-Tr {ℓ} {A : Type ℓ} (n : Nat) = Equiv (_ , is-n-connected-Tr-is-equiv {A = A} n)

is-n-connected→n-type-const
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} n
  → is-hlevel B (suc n)
  → is-n-connected A (suc n)
  → is-equiv {B = A → B} (λ b a → b)
is-n-connected→n-type-const {A = A} {B} n B-hl A-conn =
  subst is-equiv (λ i x z → transp (λ i → B) i x) (rem₁ .snd)
  where
    rem₁ : B ≃ (A → B)
    rem₁ =
      B                    ≃⟨ is-contr→points (is-n-connected-Tr n A-conn) e⁻¹ ⟩
      (n-Tr A (suc n) → B) ≃⟨ n-Tr-univ n B-hl ⟩
      (A → B)              ≃∎

retract→is-n-connected
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → (n : Nat) (f : A → B) (g : B → A)
  → is-left-inverse f g
  → is-n-connected A n
  → is-n-connected B n
retract→is-n-connected 0 f g h a-conn = lift tt
retract→is-n-connected 1 f g h a-conn = f <$> a-conn
retract→is-n-connected (suc (suc n)) f g h a-conn =
  is-n-connected-Tr.from (suc n) $
    retract→is-contr
      (n-Tr-rec (n-Tr-is-hlevel (suc n)) (inc ∘ f))
      (n-Tr-rec (n-Tr-is-hlevel (suc n)) (inc ∘ g))
      (n-Tr-elim _ (λ _ → is-hlevel-suc (suc n) (n-Tr-is-hlevel (suc n) _ _))
        (λ x → ap n-Tr.inc (h x)))
      (is-n-connected-Tr (suc n) a-conn)

Path-is-connected : ∀ {ℓ} {A : Type ℓ} {x y} n → is-n-connected A (suc n) → is-n-connected (Path A x y) n
Path-is-connected 0 conn = lift tt
Path-is-connected {x = x} (suc n) conn = is-n-connected-Tr.from n (contr (ps _ _) $
  n-Tr-elim _ (λ _ → hlevel!)
    (J (λ y p → ps x y ≡ inc p) (Equiv.injective (Equiv.inverse n-Tr-path-equiv)
      (is-contr→is-set (is-n-connected-Tr _ conn) _ _ _ _))))
  where
    ps : ∀ x y → n-Tr (x ≡ y) (suc n)
    ps x y = Equiv.to n-Tr-path-equiv (is-contr→is-prop (is-n-connected-Tr _ conn) _ _)

is-connected-suc
  : ∀ {ℓ} {A : Type ℓ} n → is-n-connected A (2 + n) → is-n-connected A (suc n)
is-connected-suc {A = A} n w = is-n-connected-Tr.from n $
  n-Tr-elim _ (λ _ → hlevel!)
    (λ x → contr (inc x) (n-Tr-elim _ (λ _ → hlevel!) (rem₁ n w x)))
    (is-n-connected-Tr (suc n) w .centre)
  where
    rem₁ : ∀ n → is-n-connected A (2 + n) → ∀ x y → Path (n-Tr A (suc n)) (inc x) (inc y)
    rem₁ zero a-conn x y = n-Tr-is-hlevel 0 _ _
    rem₁ (suc n) a-conn x y = Equiv.from n-Tr-path-equiv
      (n-Tr-rec (is-hlevel-suc _ (n-Tr-is-hlevel n)) inc
        (is-n-connected-Tr _ (Path-is-connected (2 + n) a-conn) .centre))

connected-elim
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} (P : B → Type ℓ'')
  → (f : A → B)
  → ∀ n
  → is-n-connected-map f n
  → (∀ x → is-hlevel (P x) n)
  → is-equiv {A = (∀ b → P b)} {B = (∀ a → P (f a))} (_∘ f)

connected-elim {A = A} {B} P f 0 n-conn phl = is-contr→is-equiv (Π-is-hlevel 0 phl) (Π-is-hlevel 0 λ _ → phl _)

connected-elim {A = A} {B} P f 1 n-conn phl =
  prop-ext (Π-is-hlevel 1 phl) (Π-is-hlevel 1 λ _ → phl _)
    _ (λ g b → ∥-∥-rec (phl b) (λ (a , p) → subst P p (g a)) (n-conn b))
    .snd

connected-elim {A = A} {B} P f (suc (suc k)) n-conn phl =
  subst is-equiv (funext λ g → funext λ a → transport-refl _) (rem₁ .snd)
  where
  n = suc k
  open is-iso

  shuffle : ((b : B) → fibre f b → P b) ≃ ((a : A) → P (f a))
  shuffle = Iso→Equiv λ where
    .fst      g a         → g (f a) (a , refl)
    .snd .inv g b (a , p) → subst P p (g a)
    .snd .rinv g → funext λ a → transport-refl _
    .snd .linv g → funext λ b → funext λ { (a , p) →
      J (λ b p → subst P p (g (f a) (a , refl)) ≡ g b (a , p))
        (transport-refl _) p }

  rem₁ : ((b : B) → P b) ≃ ((a : A) → P (f a))
  rem₁ =
    ((b : B) → P b)                            ≃⟨ Π-cod≃ (λ x → is-contr→points {B = λ _ → P x} (is-n-connected-Tr _ (n-conn x)) e⁻¹) ⟩
    ((b : B) → n-Tr (fibre f b) (suc n) → P b) ≃⟨ Π-cod≃ (λ x → n-Tr-univ n (phl _)) ⟩
    ((b : B) → fibre f b → P b)                ≃⟨ shuffle ⟩
    ((a : A) → P (f a))                        ≃∎

connected-elim-relative
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} (P : B → Type ℓ'')
  → (f : A → B)
  → ∀ n k
  → is-n-connected-map f n
  → (∀ x → is-hlevel (P x) (k + n))
  → ∀ it → is-hlevel (fibre {A = ((b : B) → P b)} {B = (a : A) → P (f a)} (_∘ f) it) k

connected-elim-relative P f n zero f-conn P-hl it    = connected-elim P f n f-conn P-hl .is-eqv it
connected-elim-relative {A = A} {B = B} P f n (suc k) f-conn P-hl it = done where
  T = fibre {A = ((b : B) → P b)} {B = (a : A) → P (f a)} (_∘ f) it

  module _ (gp@(g , p) hq@(h , q) : T) where
    Q : B → Type _
    Q b = g b ≡ h b

    S = fibre {A = (∀ b → Q b)} {B = (∀ a → Q (f a))} (_∘ f) λ a → happly (p ∙ sym q) a

    rem₃ : ∀ {ℓ} {A : Type ℓ} {x y : A} (p q : x ≡ y) → (p ≡ q) ≡ (refl ≡ p ∙ sym q)
    rem₃ {x = x} p q = J (λ y q → (p : x ≡ y) → (p ≡ q) ≡ (refl ≡ p ∙ sym q))
      (λ p → sym (ap (refl ≡_) (∙-idr p) ∙ Iso→Path (sym , iso sym (λ _ → refl) (λ _ → refl)))) q p

    abstract
      remark
        : ∀ {h} (α : g ≡ h) {q : h ∘ f ≡ it}
        → (PathP (λ i → α i ∘ f ≡ it) p q)
        ≃ (happly α ∘ f ≡ happly (p ∙ sym q))
      remark α = J
        (λ h α → {q : h ∘ f ≡ it} → PathP (λ i →  α i ∘ f ≡ it) p q ≃ (happly α ∘ f ≡ happly (p ∙ sym q)))
        (path→equiv (rem₃ _ _) ∙e (_ , embedding→cancellable {f = happly} λ x →
          is-contr→is-prop (is-iso→is-equiv
            (iso funext (λ _ → refl) (λ _ → refl)) .is-eqv x)))
        α

    to : Path T gp hq → S
    to α = happly (ap fst α) , remark (ap fst α) .fst (ap snd α)

    from : S → Path T gp hq
    from (a , b) = ap₂ _,_ (funext a) (Equiv.from (remark (funext a)) b)

    linv : is-left-inverse from to
    linv x = ap₂ (ap₂ _,_) refl (Equiv.η (remark _) _)

  done = Path-is-hlevel→is-hlevel k $ λ x y →
    retract→is-hlevel k (from _ _) (to _ _) (linv _ _) $
      connected-elim-relative (Q x y) f n k f-conn
        (λ x → Path-is-hlevel' (k + n) (P-hl x) _ _) _
```
