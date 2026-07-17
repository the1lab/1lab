<!--
```agda
open import Cat.Diagram.Pullback.Along
open import Cat.Instances.FinSets
open import Cat.Diagram.Pullback
open import Cat.Diagram.Omega
open import Cat.Prelude

open import Data.Fin.Finite
open import Data.Fin.Base

import Cat.Displayed.Instances.Subobjects as Sub

open is-generic-subobject
open is-pullback-along
open Sub FinSets
open Subobject
```
-->

```agda
module Cat.Instances.FinSets.Omega where
```

# The subobject classifier in FinSets

In the [[category of finite sets]], the set $\{0, 1\}$, with the
inclusion of $1$, is a [[generic subobject]]. The construction of the
name of a subobject $S \mono X$ is by cases: since finite sets are
closed under dependent sum and identity, they are closed under fibres,
so we can define the name function at $x : X$ by cases on the
cardinality of $m^*(x)$.

```agda
fin-name : ∀ {X} → Subobject X → Fin X → Fin 2
fin-name {X = X} so m with cardinality {A = fibre (so .map) m}
... | zero  = 0
... | suc x = 1
```

<!--
```agda
tru : Subobject 2
tru .dom   = 1
tru .map _ = 1
tru .monic g h x = ext λ e → Fin-cases {P = λ x → x ≡ h e} (Fin-cases {P = λ x → 0 ≡ x} refl (λ ()) (h e)) (λ ()) (g e)

private
  inj : ∀ {X} (m : Subobject X) → injective (m .map)
  inj m {a} {b} α = m .monic {c = 1} (λ _ → a) (λ _ → b) (ext λ _ → α) $ₚ 0
```
-->

This construction satisfies the evident 'universal property': its value
at $x$ is $1$ if, and only if, the fibre $m^*(x)$ is actually inhabited
(in which case it's even contractible, since subobjects of finite sets
are embeddings).

```agda
from-name : ∀ {X} (m : Subobject X) x → fin-name m x ≡ 1 → fibre (m .map) x
from-name m x p with cardinality {A = fibre (m .map) x} | enumeration {A = fibre (m .map) x}
... | zero  | e = absurd (fzero≠fsuc p)
... | suc x | e = ∥-∥-out (injective→is-embedding! (inj m) _) (case e of λ eqv → pure (Equiv.from eqv 0))

to-name : ∀ {X} (m : Subobject X) x → fibre (m .map) x → fin-name m x ≡ 1
to-name m x p with cardinality {A = fibre (m .map) x} | enumeration {A = fibre (m .map) x}
... | zero  | e = absurd (case e of λ eqv → Fin-absurd (Equiv.to eqv p))
... | suc x | e = refl
```

These two helpers show that $m$ is the pullback of the true arrow along
$\name{m}$, as required.

```agda
FinSets-omega : Subobject-classifier FinSets
FinSets-omega .Subobject-classifier.Ω = 2
FinSets-omega .Subobject-classifier.true = tru
FinSets-omega .Subobject-classifier.generic .name       = fin-name
FinSets-omega .Subobject-classifier.generic .classifies m = record { top = λ _ → 0 ; has-is-pb = fb } where
  fb : is-pullback FinSets (m .map) (fin-name m) (λ _ → 0) (λ _ → 1)
  fb .is-pullback.square        = ext λ a → to-name m _ (a , refl)
  fb .is-pullback.universal α x = from-name m _ (happly α x) .fst
  fb .is-pullback.p₁∘universal  = ext λ a → from-name m _ _ .snd
  fb .is-pullback.p₂∘universal {p₂' = p₂'}  = ext λ a → Fin-cases {P = λ x → 0 ≡ x} refl (λ ()) (p₂' a)
  fb .is-pullback.unique a e = ext λ x → inj m (from-name m _ _ .snd ∙ sym a ·ₚ x)
```

We can show uniqueness also by cases on the cardinality of each fibre.
First, if the fibre is inhabited, then let $x'$ be the preimage of $x$;
we then have $n(x) = n(mx') = 1$ as needed.

```agda
FinSets-omega .Subobject-classifier.generic .unique {m = m} {nm} pb = sym $ ext uniq where
  uniq : ∀ x → nm x ≡ fin-name m x
  uniq x with cardinality {A = fibre (m .map) x} | enumeration {A = fibre (m .map) x} | from-name m x
  ... | suc n | e | f with (x' , α) ← f refl = ap nm (sym α) ∙ happly (pb .square) _
```

If the fibre is uninhabited, we show that $n(x) = 0$ by showing it can
not be $1$. For if it were $1$, its universal property as a pullback
would let us get our hands on an element of $m^*(x)$ --- but we already
know that this type has cardinality zero.

```agda
  ... | zero | e | _ =
    let
      a : nm x ≡ fin 1 → ⊥
      a w =
        let
          vl = pb .universal {P' = 1} {p₁' = λ _ → x} {p₂' = λ _ → 0} (ext λ _ → w) 0
          it : fibre (m .map) x
          it = vl , pb .p₁∘universal · 0
        in case e of λ eqv → absurd (Fin-absurd (Equiv.to eqv it))
    in
      Fin-cases {P = λ e → nm x ≡ e → nm x ≡ 0} (λ x → x)
        (fin-cons (λ nmx=0 → absurd (a nmx=0)) λ ())
        (nm x) refl
```
