```agda
open import 1Lab.Prelude

open import Data.Fin.Base

import Data.Nat as Nat

module Data.Fin.Properties where

```

# Finite Sets - Properties

## Ordering

As noted in [`Data.Fin.Base`], we've set up the ordering on `Fin` so that
we can re-use all the proofs about the ordering on `Nat`{.Agda}.

[`Data.Fin.Base`]: Data.Fin.Base.html

However, there are still quite a few interesting things one can say about
`skip`{.Agda} and `squish`{.Agda}. In particular, we can prove the
*simplicial identities*, which characterize the interactions between
these two functions.

These lemmas might seem somewhat arbitrary and complicated, which
is true! However, they are enough to describe all the possible
interactions of `skip`{.Agda} and `squish`{.Agda}, which in turn
are the building blocks for _every_ monotone function between
`Fin`{.Agda}, so it's not that surprising that they would be a bit
of a mess!

<!-- [TODO: Reed M, 23/02/2022] Link to Simplicial Sets Stuff -->

```agda
skip-comm : ∀ {n} (i j : Fin (suc n)) → i ≤ j
          → ∀ x → skip (weaken i) (skip j x) ≡ skip (fsuc j) (skip i x)
skip-comm fzero    j        le x        = refl
skip-comm (fsuc i) (fsuc j) le fzero    = refl
skip-comm (fsuc i) (fsuc j) le (fsuc x) = ap fsuc (skip-comm i j le x)

drop-comm : ∀ {n} (i j : Fin n) → i ≤ j
          → ∀ x → squish j (squish (weaken i) x) ≡ squish i (squish (fsuc j) x)
drop-comm fzero    fzero    le fzero = refl
drop-comm fzero    fzero    le (fsuc x) = refl
drop-comm fzero    (fsuc j) le fzero = refl
drop-comm fzero    (fsuc j) le (fsuc x) = refl
drop-comm (fsuc i) (fsuc j) le fzero = refl
drop-comm (fsuc i) (fsuc j) le (fsuc x) = ap fsuc (drop-comm i j le x)

squish-skip-comm : ∀ {n} (i : Fin (suc n)) (j : Fin n) → i < fsuc j
                 → ∀ x → squish (fsuc j) (skip (weaken i) x) ≡ skip i (squish j x)
squish-skip-comm fzero j le x = refl
squish-skip-comm (fsuc i) (fsuc j) le fzero = refl
squish-skip-comm (fsuc i) (fsuc j) le (fsuc x) = ap fsuc (squish-skip-comm i j le x)

squish-skip : ∀ {n} (i j : Fin n) → i ≡ j
            → ∀ x → squish j (skip (weaken j) x) ≡ x
squish-skip fzero fzero p x = refl
squish-skip fzero (fsuc j) p x = absurd (fzero≠fsuc p)
squish-skip (fsuc i) fzero p x = refl
squish-skip (fsuc i) (fsuc j) p fzero = refl
squish-skip (fsuc i) (fsuc j) p (fsuc x) = ap fsuc (squish-skip i j (fsuc-inj p) x)

squish-skip-fsuc : ∀ {n} (i : Fin (suc n)) (j : Fin n) → i ≡ fsuc j
                 → ∀ x → squish j (skip i x) ≡ x
squish-skip-fsuc fzero fzero p x = refl
squish-skip-fsuc fzero (fsuc j) p x = absurd (fzero≠fsuc p)
squish-skip-fsuc (fsuc i) fzero p fzero = refl
squish-skip-fsuc (fsuc fzero) fzero p (fsuc x) = refl
squish-skip-fsuc (fsuc (fsuc i)) fzero p (fsuc x) =
  absurd (fzero≠fsuc (fsuc-inj (sym p)))
squish-skip-fsuc (fsuc i) (fsuc j) p fzero = refl
squish-skip-fsuc (fsuc i) (fsuc j) p (fsuc x) =
  ap fsuc (squish-skip-fsuc i j (fsuc-inj p) x)

Fin-peel : ∀ {l k} → Fin (suc l) ≃ Fin (suc k) → Fin l ≃ Fin k
Fin-peel {l} {k} sl≃sk = (Iso→Equiv (l→k , (iso k→l b→a→b a→b→a))) where
  sk≃sl : Fin (suc k) ≃ Fin (suc l)
  sk≃sl = sl≃sk e⁻¹
  module sl≃sk = Equiv sl≃sk
  module sk≃sl = Equiv sk≃sl

  l→k : Fin l → Fin k
  l→k x with inspect (sl≃sk.to (fsuc x))
  ... | fsuc y , _ = y
  ... | fzero , p with inspect (sl≃sk.to fzero)
  ... | fsuc y , _ = y
  ... | fzero , q = absurd (fzero≠fsuc (sl≃sk.injective₂ q p))

  k→l : Fin k → Fin l
  k→l x with inspect (sk≃sl.to (fsuc x))
  ... | fsuc x , _ = x
  ... | fzero , p with inspect (sk≃sl.to fzero)
  ... | fsuc y , _ = y
  ... | fzero , q = absurd (fzero≠fsuc (sk≃sl.injective₂ q p))

  absurd-path : ∀ {ℓ} {A : Type ℓ} {y : A} {x : ⊥} → absurd x ≡ y
  absurd-path {x = ()}

  a→b→a : ∀ a → k→l (l→k a) ≡ a
  a→b→a a with inspect (sl≃sk.to (fsuc a))
  a→b→a a | fsuc x , p′ with inspect (sk≃sl.to (fsuc x))
  a→b→a a | fsuc x , p′ | fsuc y , q′ = fsuc-inj (
    sym q′ ∙ ap (sk≃sl.to) (sym p′) ∙ sl≃sk.η _)
  a→b→a a | fsuc x , p′ | fzero , q′ = absurd contra where
    r = sl≃sk.injective₂ p′ (sl≃sk.ε (fsuc x))
    contra = fzero≠fsuc (sym (r ∙ q′))
  a→b→a a | fzero , p′ with inspect (sl≃sk.to fzero)
  a→b→a a | fzero , p′ | fsuc x , q′ with inspect (sk≃sl.to (fsuc x))
  a→b→a a | fzero , p′ | fsuc x , q′ | fsuc y , r′ = absurd $
    fzero≠fsuc (sym (sym r′ ∙ ap sk≃sl.to (sym q′) ∙ sl≃sk.η fzero))
  a→b→a a | fzero , p′ | fsuc x , q′ | fzero , r′ with inspect (sk≃sl.to fzero)
  a→b→a a | fzero , p′ | fsuc x , q′ | fzero , r′ | fsuc z , s = fsuc-inj $
    sym s ∙ ap sk≃sl.to (sym p′) ∙ sl≃sk.η (fsuc a)
  a→b→a a | fzero , p′ | fsuc x , q′ | fzero , r′ | fzero , s = absurd-path
  a→b→a a | fzero , p′ | fzero , q′ = absurd $ fzero≠fsuc $
    sl≃sk.injective₂ q′ p′

  b→a→b : ∀ b → l→k (k→l b) ≡ b
  b→a→b b with inspect (sk≃sl.to (fsuc b))
  b→a→b b | fsuc x , p′ with inspect (sl≃sk.to (fsuc x))
  b→a→b b | fsuc x , p′ | fsuc y , q′ = fsuc-inj $
    sym q′ ∙ ap (sl≃sk.to) (sym p′) ∙ sk≃sl.η _
  b→a→b b | fsuc x , p′ | fzero , q′ = absurd contra where
    r = sk≃sl.injective₂ p′ (sk≃sl.ε (fsuc x))
    contra = fzero≠fsuc (sym (r ∙ q′))
  b→a→b b | fzero , p′ with inspect (sk≃sl.to fzero)
  b→a→b b | fzero , p′ | fsuc x , q′ with inspect (sl≃sk.to (fsuc x))
  b→a→b b | fzero , p′ | fsuc x , q′ | fsuc y , r′  = absurd $ fzero≠fsuc $
    sym (sym r′ ∙ ap (sl≃sk.to) (sym q′) ∙ sk≃sl.η _)
  b→a→b b | fzero , p′ | fsuc x , q′ | fzero , r′ with inspect (sl≃sk.to fzero)
  b→a→b a | fzero , p′ | fsuc x , q′ | fzero , r′ | fsuc z , s = fsuc-inj $
    sym s ∙ ap (sl≃sk.to) (sym p′) ∙ sk≃sl.η (fsuc a)
  b→a→b a | fzero , p′ | fsuc x , q′ | fzero , r′ | fzero , s = absurd-path
  b→a→b b | fzero , p′ | fzero , q′ = absurd $ fzero≠fsuc $
    sk≃sl.injective₂ q′ p′

Fin-injective : ∀ {l k} → Fin l ≃ Fin k → l ≡ k
Fin-injective {zero} {zero} l≃k = refl
Fin-injective {zero} {suc k} l≃k with equiv→inverse (l≃k .snd) fzero
... | ()
Fin-injective {suc l} {zero} l≃k with l≃k .fst fzero
... | ()
Fin-injective {suc l} {suc k} sl≃sk = ap suc $ Fin-injective (Fin-peel sl≃sk)
```
