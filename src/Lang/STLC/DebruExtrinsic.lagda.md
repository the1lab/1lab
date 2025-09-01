<!--
```agda
open import 1Lab.HLevel.Closure
open import 1Lab.Prelude

open import Data.Vec.Base
open import Data.Maybe
open import Data.Bool
open import Data.Dec
open import Data.Fin
open import Data.Nat
open import Data.Sum
```
-->

```agda
module Lang.STLC.DebruExtrinsic where
```

# The simply typed lambda calculus, fancier

We're doing the STLC again! See the first part [here]. The first time, we used string names for
variables. This time, however, we are going to use
a different implementation strategy that makes most of the proofs
significantly easier, and fixes that pesky substitution issue we had.

[here]: Lang.STLC.Named.html

First we define types in the same method.

```agda
data Ty : Type where
  `⊤ : Ty
  _`×_ : Ty → Ty → Ty
  _`⇒_ : Ty → Ty → Ty
```

This time, contexts are vectors, indexed by their length. A context
$\Gamma\ n$ contains $n$ elements.

```agda
Ctx : Nat → Type
Ctx n = Vec Ty n
```

Now for terms. First however, we must explain deb Bruijn indexes.
De Bruijn indexes are a naming scheme that does not rely on names, instead
referring to bound variables with natural numbers. The number $0$
represents the most recently bound term; $1$ the second most, etc.

A term is indexed by a natural number representing the maximum of how many
**unbound** variables it contains. For example, the term $0$ has one
unbound variable, but $\lambda. 0$ has none.


```agda
data Expr : Nat → Type where
```

We use this index in our variable constructor, such that a term of
type `Expr n`{.Agda} may only reference $n$ different variables.
`Fin n`{.Agda} is a type containing $n$ elements, and is therefore suitable.

```agda
  ` : ∀ {n} → Fin n → Expr n
```

In order to decrease this level when encountering lambdas, we require
the body to have a level one higher than the constructed term.

```agda
  `λ : ∀ {n} → Expr (suc n) → Expr n
  _`$_ : ∀ {n} → Expr n → Expr n → Expr n
  `⟨_,_⟩ : ∀ {n} → Expr n → Expr n → Expr n
  `π₁ : ∀ {n} → Expr n → Expr n
  `π₂ : ∀ {n} → Expr n → Expr n
  `tt : ∀ {n} → Expr n
```

We note that you can freely raise the level of a term
without modifying it, if you so wish.

```agda
raise : ∀ {n} → Expr n → Expr (suc n)
raise (` x) = ` (weaken x)
raise (`λ x) = `λ (raise x)
raise (f `$ x) = raise f `$ raise x
raise `⟨ a , b ⟩ = `⟨ raise a , raise b ⟩
raise (`π₁ x) = `π₁ (raise x)
raise (`π₂ x) = `π₂ (raise x)
raise `tt = `tt
```

We define similar typing rules as before, this time using our indexed
contexts and terms. This allows us to have a total index function, so
we don't have to deal with `Maybe`{.Agda} at all!

<!--
```agda
infix 3 _⊢_⦂_
```
-->

```agda
data _⊢_⦂_ : ∀ {n} → Ctx n → Expr n → Ty → Type where
  `var-intro
      : ∀ {n} {Γ : Ctx n} {k ty}
      →  lookup Γ k ≡ ty
      → Γ ⊢ ` k ⦂ ty
  `⇒-intro
      : ∀ {n} {Γ : Ctx n} {bd ret ty}
      → (ty ∷ Γ) ⊢ bd ⦂ ret
      → Γ ⊢ `λ bd ⦂ ty `⇒ ret
  `⇒-elim
      : ∀ {n} {Γ : Ctx n} {f x ty ret}
      → Γ ⊢ f ⦂ ty `⇒ ret
      → Γ ⊢ x ⦂ ty
      → Γ ⊢ f `$ x ⦂ ret
  `×-intro
      : ∀ {n} {Γ : Ctx n} {a b at bt}
      → Γ ⊢ a ⦂ at
      → Γ ⊢ b ⦂ bt
      → Γ ⊢ `⟨ a , b ⟩ ⦂ at `× bt
  `×-elim₁
      : ∀ {n} {Γ : Ctx n} {p at bt}
      → Γ ⊢ p ⦂ at `× bt
      → Γ ⊢ `π₁ p ⦂ at
  `×-elim₂
      : ∀ {n} {Γ : Ctx n} {p at bt}
      → Γ ⊢ p ⦂ at `× bt
      → Γ ⊢ `π₂ p ⦂ bt
  `tt-intro : ∀ {n} {Γ : Ctx n} → Γ ⊢ `tt ⦂ `⊤
```

The examples from before:

<!--
```agda
module _ where private
```
-->

```agda
  const : Expr 0
  const = `λ (`λ (` 0))

  const-is-`⊤⇒`⊤⇒`⊤ : [] ⊢ const ⦂ `⊤ `⇒ (`⊤ `⇒ `⊤)
  const-is-`⊤⇒`⊤⇒`⊤ = `⇒-intro (`⇒-intro (`var-intro refl))
```

Once again we define values:

```agda
data is-value : ∀ {n} → Expr n → Type where
  v-λ : ∀ {n} {body : Expr (suc n)} → is-value (`λ body)
  v-⟨,⟩ : ∀ {n} {a b : Expr n} → is-value (`⟨ a , b ⟩)
  v-⊤ : ∀ {n} → is-value {n} `tt
```

And now we must do substitution. How awful.

This time, instead of doing a single substitution, we are going to
consider substitution of every free variable at once. This is called
"simultaneous substitution."

We start by defining a particular extension of a renaming function.
This extension is important as it leaves the "bottom-most" variable
untouched (as is desired when working under binders like $\lambda$.)

```agda
fin-ext
    : ∀ {n k}
    → (Fin n → Fin k)
    → Fin (suc n) → Fin (suc k)
fin-ext f x with fin-view x
... | zero = fzero
... | suc i = fsuc (f i)
```

Then we can define renaming, which replaces every free variable with another.

```agda
rename
    : ∀ {n k}
    → (Fin n → Fin k)
    → Expr n → Expr k
rename f (` x) = ` (f x)
rename {n} {k} f (`λ x) = `λ (rename (fin-ext f) x)
rename f (a `$ b) = rename f a `$ rename f b
rename f `⟨ a , b ⟩ = `⟨ (rename f a) , (rename f b) ⟩
rename f (`π₁ x) = `π₁ (rename f x)
rename f (`π₂ x) = `π₂ (rename f x)
rename f `tt = `tt
```

We can show that under a particular set of conditions,
(namely that the new variables have the same types as the old ones),
renaming a term keeps its type the same.

```agda
rename-pres-tp
    : ∀ {n k} (Γ : Ctx n) (Δ : Ctx k)
    → (ren : Fin n → Fin k)
    → (ren~ : ∀ (f : Fin n) → lookup Γ f ≡ lookup Δ (ren f))
    → ∀ x {ty}
    → Γ ⊢ x ⦂ ty
    → Δ ⊢ rename ren x ⦂ ty
rename-pres-tp Γ Δ ren ren~ (` x) (`var-intro p) = `var-intro (sym (ren~ x) ∙ p)
rename-pres-tp {n} {k} Γ Δ ren ren~ (`λ x) (`⇒-intro {ty = ty} p) = `⇒-intro delta where
  extend : (f : Fin (suc n))
           → lookup (ty ∷ Γ) f ≡ lookup (ty ∷ Δ) (fin-ext ren f)
  extend f with fin-view f
  ... | zero = refl
  ... | suc i = ren~ i

  delta : ty ∷ Δ ⊢ rename (fin-ext ren) x ⦂ _
  delta = rename-pres-tp (ty ∷ Γ) (ty ∷ Δ) (fin-ext ren) extend x p

rename-pres-tp Γ Δ ren ren~ (x `$ x₁) (`⇒-elim p p₁) =
  `⇒-elim (rename-pres-tp Γ Δ ren ren~ x p) (rename-pres-tp Γ Δ ren ren~ x₁ p₁)
rename-pres-tp Γ Δ ren ren~ `⟨ x , x₁ ⟩ {ty} (`×-intro p p₁) =
  `×-intro (rename-pres-tp Γ Δ ren ren~ x p) (rename-pres-tp Γ Δ ren ren~ x₁ p₁)
rename-pres-tp Γ Δ ren ren~ (`π₁ x) (`×-elim₁ p) = `×-elim₁ (rename-pres-tp Γ Δ ren ren~ x p)
rename-pres-tp Γ Δ ren ren~ (`π₂ x) (`×-elim₂ p) = `×-elim₂ (rename-pres-tp Γ Δ ren ren~ x p)
rename-pres-tp Γ Δ ren ren~ `tt `tt-intro = `tt-intro

```

This particular renaming increases every free variable in an expression by one.
Note that we can add whatever type we'd like to the context, and the term's type
remains the same.

```agda
incr : ∀ {n} → Expr n → Expr (suc n)
incr x = rename fsuc x

incr-pres-tp : ∀ {n} (Γ : Ctx n) x {t n}
      → Γ ⊢ x ⦂ t
      → n ∷ Γ ⊢ incr x ⦂ t
incr-pres-tp Γ x {t} {n} p = rename-pres-tp Γ (n ∷ Γ) fsuc (λ f → refl) x p
```

Now we can consider not just renaming, but substitutions, which
we model as functions from free variables to terms.
The following extending of a substitution function is
similar to our `fin-ext`{.Agda} from renaming. It leaves the new bottom-most
variable unchanged, so that variables under a binder are not modified.

```agda
extend : ∀ {n k}
      → (Fin n → Expr k)
      → Fin (suc n) → Expr (suc k)
extend f x with fin-view x
... | zero = ` fzero
... | suc i = incr (f i)
```

Now substitution itself:

```agda
simsub
    : ∀ {n k}
    → (Fin n → Expr k)
    → Expr n → Expr k
simsub f (` x) = f x
simsub {n} {k} f (`λ x) = `λ (simsub (extend f) x)
simsub f (a `$ b) = (simsub f a) `$ (simsub f b)
simsub f `⟨ a , b ⟩ = `⟨ (simsub f a) , (simsub f b) ⟩
simsub f (`π₁ x) = `π₁ (simsub f x)
simsub f (`π₂ x) = `π₂ (simsub f x)
simsub f `tt = `tt

```

Similarly to showing renaming retains types, we can show that the same
is true for substitution, assuming every new term has the same type
as the variable it is replacing.

```agda
simsub-pres-tp
    : ∀ {n k} (Γ : Ctx n) (Δ : Ctx k)
    → (ren : ∀ (f : Fin n) → Expr k)
    → (ren~ : ∀ (f : Fin n) {t} → lookup Γ f ≡ t → Δ ⊢ (ren f) ⦂ t)
    → ∀ (x : Expr n) {ty}
    → Γ ⊢ x ⦂ ty
    → Δ ⊢ simsub ren x ⦂ ty
simsub-pres-tp Γ Δ ren ren~ (` x) (`var-intro x₁) = ren~ x x₁
simsub-pres-tp {n} Γ Δ ren ren~ (`λ x) (`⇒-intro {ty = ty} p) = `⇒-intro delta where
  extnd : (f : Fin (suc n)) {t : Ty}
           → lookup (ty ∷ Γ) f ≡ t → ty ∷ Δ ⊢ extend ren f ⦂ t
  extnd f x with fin-view f
  ... | zero = `var-intro x
  ... | suc i = incr-pres-tp Δ (ren i) (ren~ i x)

  delta : _ ∷ Δ ⊢ simsub (extend ren) x ⦂ _
  delta = simsub-pres-tp (ty ∷ Γ) (_ ∷ Δ) (extend ren) extnd x p

simsub-pres-tp Γ Δ ren ren~ (x `$ x₁) (`⇒-elim p p₁) =
  `⇒-elim (simsub-pres-tp Γ Δ ren ren~ x p) (simsub-pres-tp Γ Δ ren ren~ x₁ p₁)
simsub-pres-tp Γ Δ ren ren~ `⟨ x , x₁ ⟩ (`×-intro p p₁) =
  `×-intro (simsub-pres-tp Γ Δ ren ren~ x p) (simsub-pres-tp Γ Δ ren ren~ x₁ p₁)
simsub-pres-tp Γ Δ ren ren~ (`π₁ x) (`×-elim₁ p) = `×-elim₁ (simsub-pres-tp Γ Δ ren ren~ x p)
simsub-pres-tp Γ Δ ren ren~ (`π₂ x) (`×-elim₂ p) = `×-elim₂ (simsub-pres-tp Γ Δ ren ren~ x p)
simsub-pres-tp Γ Δ ren ren~ `tt `tt-intro = `tt-intro
```

Then it's simple enough to define "regular" substitution.

```agda
subst-down : ∀ {n} → Expr n → Fin (suc n) → Expr n
subst-down x f with fin-view f
... | zero = x
... | suc i = ` i

infix 30 _[_]
_[_] : ∀ {n} → Expr (suc n) → Expr n → Expr n
_[_] {n} a s = simsub (subst-down s) a

single-subst-correct
    : ∀ {n} (Γ : Ctx n) (f : Expr (suc n)) (x : Expr n) {t₁ t₂}
    → t₁ ∷ Γ ⊢ f ⦂ t₂
    → Γ ⊢ x ⦂ t₁
    → Γ ⊢ f [ x ] ⦂ t₂
single-subst-correct {n} Γ f x {t₁} fp xp =
                         simsub-pres-tp (t₁ ∷ Γ) Γ (subst-down x) extnd f fp
  where
    extnd : (f₁ : Fin (suc n)) {t : Ty} →
            lookup (t₁ ∷ Γ) f₁ ≡ t → Γ ⊢ subst-down x f₁ ⦂ t
    extnd f₁ x with fin-view f₁
    ... | zero = subst (λ k → _ ⊢ _ ⦂ k) x xp
    ... | suc i = `var-intro x
```

Then we have reduction rules, as before.

```agda
infix 10 _↦_
data _↦_ : ∀ {n} → Expr n → Expr n → Type where
     β-λ
       : ∀ {n} {f : Expr (suc n)} {x : Expr n} {f[x]}
       → is-value x
       → f[x] ≡ f [ x ]
       → (`λ f) `$ x ↦ f[x]
     β-π₁ : ∀ {n} {a b : Expr n} → `π₁ `⟨ a , b ⟩ ↦ a
     β-π₂ : ∀ {n} {a b : Expr n} → `π₂ `⟨ a , b ⟩ ↦ b

     ξ-π₁ : ∀ {n} {a b : Expr n} → a ↦ b → `π₁ a  ↦ `π₁ b
     ξ-π₂ : ∀ {n} {a b : Expr n} → a ↦ b → `π₂ a  ↦ `π₂ b
     
     ξ-$ₗ : ∀ {n} {f g x : Expr n} → f ↦ g →              f `$ x ↦ g `$ x
     ξ-$ᵣ : ∀ {n} {f x y : Expr n} → is-value f → x ↦ y → f `$ x ↦ f `$ y
```

Values don't reduce.

```agda
value-¬reduce : ∀ {n} {x y : Expr n} → is-value x → ¬ (x ↦ y)
value-¬reduce v-λ ()
value-¬reduce v-⟨,⟩ ()
value-¬reduce v-⊤ ()
```

Reduction preserves types (preservation).

```agda
↦-pres-tp : ∀ {n} (Γ : Ctx n) (x y : Expr n) {ty}
     → Γ ⊢ x ⦂ ty
     → x ↦ y
     → Γ ⊢ y ⦂ ty
↦-pres-tp Γ (f `$ x) y (`⇒-elim p p₁) (ξ-$ₗ r) = `⇒-elim (↦-pres-tp Γ f _ p r) p₁
↦-pres-tp Γ (f `$ x) y (`⇒-elim p p₁) (ξ-$ᵣ x₁ r) = `⇒-elim p (↦-pres-tp Γ x _ p₁ r)
↦-pres-tp Γ ((`λ f) `$ x) y (`⇒-elim (`⇒-intro p) p₁) (β-λ k eq) =
     subst (λ k → _ ⊢ k ⦂ _) (sym eq) (single-subst-correct Γ f x p p₁)
↦-pres-tp Γ (`π₁ x) y (`×-elim₁ p) (ξ-π₁ r) = `×-elim₁ (↦-pres-tp Γ x _ p r)
↦-pres-tp Γ (`π₂ x) y (`×-elim₂ p) (ξ-π₂ r) = `×-elim₂ (↦-pres-tp Γ x _ p r)
↦-pres-tp Γ (`π₁ x) y (`×-elim₁ (`×-intro p p₁)) β-π₁ = p
↦-pres-tp Γ (`π₂ x) y (`×-elim₂ (`×-intro p p₁)) β-π₂ = p₁
```

Then, we show progress similarly to before.

```agda
data Progress {n : Nat} (x : Expr n) : Type where
     going : ∀ {y} → x ↦ y → Progress x
     done : is-value x → Progress x

progress
    : ∀ {x : Expr 0} {ty}
    → [] ⊢ x ⦂ ty
    → Progress x
progress (`⇒-intro x) = done v-λ
progress (`⇒-elim f x) with progress f
... | going f₁ = going (ξ-$ₗ f₁)
... | done f₁ with progress x
... | going x₁ = going (ξ-$ᵣ f₁ x₁)
... | done x₁ with f₁
... | v-λ = going (β-λ x₁ refl)
progress (`×-intro x x₁) = done v-⟨,⟩
progress (`×-elim₁ x) with progress x
... | going x₁ = going (ξ-π₁ x₁)
... | done v-⟨,⟩ = going β-π₁
progress (`×-elim₂ x) with progress x
... | going x₁ = going (ξ-π₂ x₁)
... | done v-⟨,⟩ = going β-π₂
progress `tt-intro = done v-⊤
```

An upgrade from last time: reduction in *any* context is deterministic!

```agda
deterministic : ∀ {n} {Γ : Ctx n} {x y z : Expr n} {ty}
    → Γ ⊢ x ⦂ ty
    → x ↦ y
    → x ↦ z
    → z ≡ y
deterministic (`var-intro x) () r
deterministic (`⇒-intro ⊢x) () r
deterministic (`⇒-elim ⊢x ⊢x₁) (β-λ x eq₁) (β-λ x₁ eq₂) = eq₂ ∙ sym eq₁
deterministic (`⇒-elim ⊢x ⊢x₁) (β-λ x eq) (ξ-$ᵣ x₁ r) = absurd (value-¬reduce x r)
deterministic (`⇒-elim ⊢x ⊢x₁) (ξ-$ₗ l) (ξ-$ₗ r) = ap₂ _`$_ (deterministic ⊢x l r) refl
deterministic (`⇒-elim ⊢x ⊢x₁) (ξ-$ₗ l) (ξ-$ᵣ x r) = absurd (value-¬reduce x l)
deterministic (`⇒-elim ⊢x ⊢x₁) (ξ-$ᵣ x l) (β-λ x₁ eq) = absurd (value-¬reduce x₁ l)
deterministic (`⇒-elim ⊢x ⊢x₁) (ξ-$ᵣ x l) (ξ-$ₗ r) = absurd (value-¬reduce x r)
deterministic (`⇒-elim ⊢x ⊢x₁) (ξ-$ᵣ x l) (ξ-$ᵣ x₁ r) = ap₂ _`$_ refl (deterministic ⊢x₁ l r)
deterministic (`×-intro ⊢x ⊢x₁) () r
deterministic (`×-elim₁ ⊢x) β-π₁ β-π₁ = refl
deterministic (`×-elim₁ ⊢x) (ξ-π₁ l) (ξ-π₁ r) = ap `π₁ (deterministic ⊢x l r)
deterministic (`×-elim₂ ⊢x) β-π₂ β-π₂ = refl
deterministic (`×-elim₂ ⊢x) (ξ-π₂ l) (ξ-π₂ r) = ap `π₂ (deterministic ⊢x l r)
deterministic `tt-intro () r
```
