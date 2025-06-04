<!--
```agda
open import 1Lab.HLevel.Closure
open import 1Lab.Prelude

open import Data.Maybe
open import Data.Bool
open import Data.Dec
open import Data.Fin
open import Data.Nat
open import Data.Sum
open import Data.Vec.Base
```
-->

```agda
module ProgrammingLanguage.STLC.DebruExtrinsic where
```

# The simply typed lambda calculus, fancier

We're doing the STLC again! This time, however, we are going to use
a different implementation strategy that makes most of the proofs
significantly easier, and fixes that pesky substitution issue we had!

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
Con : Nat → Type
Con n = Vec Ty n

_#_ : ∀ {n k} → Con n → Con k → Con (n + k)
[] # Δ = Δ
(x ∷ Γ) # Δ = x ∷ (Γ # Δ)
```

Now for terms. First, we must explain Debrujin indexes:

<insert prose>

A term is indexed by a natural number representing how many 
**unbound** variables it contains. For example, the term $0$ has one
unbound variable, but $\lambda. 0$ has none.

In order to decrease this level when encountering lambdas, we require
the body to have a level one higher than the constructed term.

```agda
data Expr : Nat → Type where
  ` : ∀ {n} → Fin n → Expr n
  `λ : ∀ {n} → Expr (suc n) → Expr n
  _`$_ : ∀ {n} → Expr n → Expr n → Expr n
  `⟨_,_⟩ : ∀ {n} → Expr n → Expr n → Expr n
  `π₁ : ∀ {n} → Expr n → Expr n
  `π₂ : ∀ {n} → Expr n → Expr n
  `tt : ∀ {n} → Expr n
``` 

We note that you can freely raise the level of a term, if you so wish.

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
data _⊢_⦂_ : ∀ {n} → Con n → Expr n → Ty → Type where
  `var-intro : ∀ {n} {Γ : Con n} {k ty} → 
               lookup Γ k ≡ ty →
               Γ ⊢ ` k ⦂ ty
  `⇒-intro : ∀ {n} {Γ : Con n} {bd ret ty} →
               (ty ∷ Γ) ⊢ bd ⦂ ret →
               Γ ⊢ `λ bd ⦂ ty `⇒ ret
  `⇒-elim : ∀ {n} {Γ : Con n} {f x ty ret} →
               Γ ⊢ f ⦂ ty `⇒ ret →
               Γ ⊢ x ⦂ ty →
               Γ ⊢ f `$ x ⦂ ret
  `×-intro : ∀ {n} {Γ : Con n} {a b at bt} →
               Γ ⊢ a ⦂ at →
               Γ ⊢ b ⦂ bt →
               Γ ⊢ `⟨ a , b ⟩ ⦂ at `× bt
  `×-elim₁ : ∀ {n} {Γ : Con n} {p at bt} →
               Γ ⊢ p ⦂ at `× bt →
               Γ ⊢ `π₁ p ⦂ at
  `×-elim₂ : ∀ {n} {Γ : Con n} {p at bt} →
               Γ ⊢ p ⦂ at `× bt →
               Γ ⊢ `π₂ p ⦂ bt
  `tt-intro : ∀ {n} {Γ : Con n} →
               Γ ⊢ `tt ⦂ `⊤
```

The examples from before:

<!--
```agda
module Example-1 where
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
data Value : ∀ {n} → Expr n → Type where
  v-λ : ∀ {n} {body : Expr (suc n)} → Value (`λ body)
  v-⟨,⟩ : ∀ {n} {a b : Expr n} → Value (`⟨ a , b ⟩)
  v-⊤ : ∀ {n} → Value {n} `tt
```


And now we must do substitution. How awful. 

```agda
exts : ∀ {n k} → (Fin n → Fin k) → Fin (suc n) → Fin (suc k)
exts f x with fin-view x
... | zero = fzero
... | suc i = fsuc (f i)

rename : ∀ {n k} → (Fin n → Fin k) → Expr n → Expr k
rename f (` x) = ` (f x)
rename {n} {k} f (`λ x) = `λ (rename (exts f) x)
rename f (a `$ b) = rename f a `$ rename f b
rename f `⟨ a , b ⟩ = `⟨ (rename f a) , (rename f b) ⟩
rename f (`π₁ x) = `π₁ (rename f x)
rename f (`π₂ x) = `π₂ (rename f x)
rename f `tt = `tt

rename~ : ∀ {n k} (Γ : Con n) (Δ : Con k) → 
          (ren : Fin n → Fin k) →
          (ren~ : ∀ (f : Fin n) → lookup Γ f ≡ lookup Δ (ren f)) →
          ∀ x {ty} →
          Γ ⊢ x ⦂ ty →
          Δ ⊢ rename ren x ⦂ ty
rename~ Γ Δ ren ren~ (` x) (`var-intro p) = `var-intro (sym (ren~ x) ∙ p)
rename~ {n} {k} Γ Δ ren ren~ (`λ x) (`⇒-intro {ty = ty} p) = `⇒-intro hm
  where
    help : (f : Fin (suc n)) →
            lookup (ty ∷ Γ) f ≡ lookup (ty ∷ Δ) (exts ren f)
    help f with fin-view f 
    ... | zero = refl
    ... | suc i = ren~ i

    hm : ty ∷ Δ ⊢ rename (exts ren) x ⦂ _
    hm = rename~ (ty ∷ Γ) (ty ∷ Δ) (exts ren) help x p
rename~ Γ Δ ren ren~ (x `$ x₁) (`⇒-elim p p₁) = `⇒-elim (rename~ Γ Δ ren ren~ x p) (rename~ Γ Δ ren ren~ x₁ p₁)
rename~ Γ Δ ren ren~ `⟨ x , x₁ ⟩ {ty} (`×-intro p p₁) = `×-intro (rename~ Γ Δ ren ren~ x p) (rename~ Γ Δ ren ren~ x₁ p₁)
rename~ Γ Δ ren ren~ (`π₁ x) (`×-elim₁ p) = `×-elim₁ (rename~ Γ Δ ren ren~ x p)
rename~ Γ Δ ren ren~ (`π₂ x) (`×-elim₂ p) = `×-elim₂ (rename~ Γ Δ ren ren~ x p)
rename~ Γ Δ ren ren~ `tt `tt-intro = `tt-intro

incr : ∀ {n} → Expr n → Expr (suc n)
incr x = rename fsuc x

incr~ : ∀ {n} (Γ : Con n) x {t₁ t₂} →
        Γ ⊢ x ⦂ t₂ →
        t₁ ∷ Γ ⊢ incr x ⦂ t₂
incr~ Γ x {t₁} {t₂} p = rename~ Γ (t₁ ∷ Γ) fsuc (λ f → refl) x p

extnd : ∀ {n k} → (Fin n → Expr k) → Fin (suc n) → Expr (suc k)
extnd f x with fin-view x 
... | zero = ` fzero
... | suc i = incr (f i)

simsub : ∀ {n k} → (Fin n → Expr k) → Expr n → Expr k
simsub f (` x) = f x
simsub {n} {k} f (`λ x) = `λ (simsub (extnd f) x)
simsub f (a `$ b) = (simsub f a) `$ (simsub f b)
simsub f `⟨ a , b ⟩ = `⟨ (simsub f a) , (simsub f b) ⟩
simsub f (`π₁ x) = `π₁ (simsub f x)
simsub f (`π₂ x) = `π₂ (simsub f x)
simsub f `tt = `tt

simsub~ : ∀ {n k} (Γ : Con n) (Δ : Con k) →
           (ren : ∀ (f : Fin n) → Expr k) →
           (ren~ : ∀ (f : Fin n) {t} → lookup Γ f ≡ t → Δ ⊢ (ren f) ⦂ t) →
           ∀ (x : Expr n) {ty} →
           Γ ⊢ x ⦂ ty →
           Δ ⊢ simsub ren x ⦂ ty
simsub~ Γ Δ ren ren~ (` x) (`var-intro x₁) = ren~ x x₁
simsub~ {n} Γ Δ ren ren~ (`λ x) (`⇒-intro {ty = ty} p) = `⇒-intro ex
  where
    rest : (f : Fin (suc n)) {t : Ty} →
            lookup (ty ∷ Γ) f ≡ t → ty ∷ Δ ⊢ extnd ren f ⦂ t
    rest f x with fin-view f 
    ... | zero = `var-intro x
    ... | suc i = incr~ Δ (ren i) (ren~ i x)

    ex : _ ∷ Δ ⊢ simsub (extnd ren) x ⦂ _
    ex = simsub~ (ty ∷ Γ) (_ ∷ Δ) (extnd ren) rest x p
simsub~ Γ Δ ren ren~ (x `$ x₁) (`⇒-elim p p₁) = `⇒-elim (simsub~ Γ Δ ren ren~ x p) (simsub~ Γ Δ ren ren~ x₁ p₁)
simsub~ Γ Δ ren ren~ `⟨ x , x₁ ⟩ (`×-intro p p₁) = `×-intro (simsub~ Γ Δ ren ren~ x p) (simsub~ Γ Δ ren ren~ x₁ p₁)
simsub~ Γ Δ ren ren~ (`π₁ x) (`×-elim₁ p) = `×-elim₁ (simsub~ Γ Δ ren ren~ x p)
simsub~ Γ Δ ren ren~ (`π₂ x) (`×-elim₂ p) = `×-elim₂ (simsub~ Γ Δ ren ren~ x p)
simsub~ Γ Δ ren ren~ `tt `tt-intro = `tt-intro

subst-down : ∀ {n} → Expr n → Fin (suc n) → Expr n
subst-down x f with fin-view f 
... | zero = x
... | suc i = ` i

infix 30 _[_]
_[_] : ∀ {n} → Expr (suc n) → Expr n → Expr n
_[_] {n} a s = simsub (subst-down s) a

single-subst-correct : ∀ {n} (Γ : Con n) (f : Expr (suc n)) 
                         (x : Expr n) {t₁ t₂} →
                       t₁ ∷ Γ ⊢ f ⦂ t₂ →
                       Γ ⊢ x ⦂ t₁ →
                       Γ ⊢ f [ x ] ⦂ t₂
single-subst-correct {n} Γ f x {t₁} fp xp = simsub~ (t₁ ∷ Γ) Γ (subst-down x) rest f fp
  where
    rest : (f₁ : Fin (suc n)) {t : Ty} →
            lookup (t₁ ∷ Γ) f₁ ≡ t → Γ ⊢ subst-down x f₁ ⦂ t
    rest f₁ x with fin-view f₁ 
    ... | zero = subst (λ k → _ ⊢ _ ⦂ k) x xp
    ... | suc i = `var-intro x

infix 10 _~>_
data _~>_ : ∀ {n} → Expr n → Expr n → Type where
     ~β : ∀ {n} {f : Expr (suc n)} {x : Expr n} →
          (`λ f) `$ x ~> f [ x ]
     ~η₁ : ∀ {n} {a b : Expr n} →
          `π₁ `⟨ a , b ⟩ ~> a
     ~η₂ : ∀ {n} {a b : Expr n} →
          `π₂ `⟨ a , b ⟩ ~> b
     ~ζₗ : ∀ {n} {f g x : Expr n} →
           Value x →
           f ~> g →
           f `$ x ~> g `$ x
     ~ζᵣ : ∀ {n} {f x y : Expr n} →
           x ~> y →
           f `$ x ~> f `$ y
     ~ξₗ : ∀ {n} {x y b : Expr n} →
           x ~> y →
           `⟨ x , b ⟩ ~> `⟨ y , b ⟩
     ~ξᵣ : ∀ {n} {a x y : Expr n} →
           x ~> y →
           `⟨ a , x ⟩ ~> `⟨ a , y ⟩

infix 10 _~>*_
infixr 10 ⟨_⟩then_to_
data _~>*_ : ∀ {n} → Expr n → Expr n → Type where
     ⟨_⟩rfl : ∀ {n} (x : Expr n) → x ~>* x
     ⟨_⟩then_to_ : ∀ {n} {x} y {z : Expr n} →
          x ~> y →
          y ~>* z →
          x ~>* z

red~ : ∀ {n} (Γ : Con n) (x y : Expr n) {ty} →
         Γ ⊢ x ⦂ ty →
         x ~> y →
         Γ ⊢ y ⦂ ty
red~ Γ (f `$ x) y (`⇒-elim p p₁) (~ζₗ x₁ r) = `⇒-elim (red~ Γ f _ p r) p₁
red~ Γ (f `$ x) y (`⇒-elim p p₁) (~ζᵣ r) = `⇒-elim p (red~ Γ x _ p₁ r)
red~ Γ ((`λ f) `$ x) y (`⇒-elim (`⇒-intro p) p₁) ~β = single-subst-correct Γ f x p p₁
red~ Γ `⟨ a , b ⟩ y (`×-intro p p₁) (~ξₗ r) = `×-intro (red~ Γ a _ p r) p₁
red~ Γ `⟨ a , b ⟩ y (`×-intro p p₁) (~ξᵣ r) = `×-intro p (red~ Γ b _ p₁ r)
red~ Γ (`π₁ x) y (`×-elim₁ (`×-intro p _)) ~η₁ = p
red~ Γ (`π₂ x) y (`×-elim₂ (`×-intro _ p)) ~η₂ = p

rtc~ : ∀ {n} (Γ : Con n) (x y : Expr n) {ty} →
         Γ ⊢ x ⦂ ty →
         x ~>* y →
         Γ ⊢ y ⦂ ty
rtc~ Γ x y p ⟨ _ ⟩rfl = p
rtc~ Γ x y p (⟨ y₁ ⟩then x₁ to k) = rtc~ Γ y₁ y (red~ Γ x y₁ p x₁) k
```
