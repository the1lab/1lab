{-
Adaptation of the ring solver from the Agda standard library to work
with the 1Lab's weird primitives.
Agda's ring solver was originally implemented by Nils Anders Danielsson,
and the referenced version includes contributions by Matthew Daggit,
Guillaume Allais, Donnacha Oisín Kidney, and Markus Wageringel.
Uses ideas from the Coq ring tactic. See "Proving Equalities in a
Commutative Ring Done Right in Coq" by Grégoire and Mahboubi. The
code below is not optimised like theirs, though (in particular, our
Horner normal forms are not sparse).
-}
open import 1Lab.Reflection.Variables
open import 1Lab.Reflection.Solver
open import 1Lab.Reflection

open import Algebra.Ring.Cat.Initial
open import Algebra.Ring.Commutative
open import Algebra.Group.Ab
open import Algebra.Group
open import Algebra.Ring

open import Cat.Displayed.Total
open import Cat.Prelude hiding (_+_ ; _*_ ; _-_)

open import Data.Fin.Product
open import Data.Fin.Base
open import Data.Int.Base
open import Data.List hiding (lookup ; tabulate)
open import Data.Dec
open import Data.Nat

import Algebra.Ring.Reasoning as Kit

import Data.Int.Base as B

open ∫Hom

module Algebra.Ring.Solver where

module Impl {ℓ} {R : Type ℓ} (cring : CRing-on R) where
  private
    R' : Ring _
    R' = record { fst = el _ (CRing-on.has-is-set cring) ; snd = CRing-on.has-ring-on cring }

    module R = Kit R'

    ℤ↪R-rh = Int-is-initial R' .centre
    module ℤ↪R = is-ring-hom (ℤ↪R-rh .snd)

    open CRing-on cring using (*-commutes)

  embed-coe : Int → R
  embed-coe x = ℤ↪R-rh .fst (lift x)

  embed-lemma
    : {h' : Int → R}
    → is-ring-hom (Liftℤ {ℓ} .snd) (R' .snd) (h' ⊙ lower)
    → ∀ x → embed-coe x ≡ h' x
  embed-lemma p x = Int-is-initial R' .paths (∫hom _ p) ·ₚ lift x

  data Poly   : Nat → Type ℓ
  data Normal : Nat → Type ℓ

  data Poly where
    ∅     : ∀ {n} → Poly n
    _*x+_ : ∀ {n} → Poly (suc n) → Normal n → Poly (suc n)

  data Normal where
    con  : Int → Normal 0
    poly : ∀ {n} → Poly (suc n) → Normal (suc n)

  Ep : ∀ {n} → Poly (suc n) → Vec R (suc n) → R
  En : ∀ {n} → Normal n → Vec R n → R

  Ep ∅ i = R.0r
  Ep (p *x+ c) (x ∷ e) = Ep p (x ∷ e) R.* x R.+ En c e

  En (con x) i = embed-coe x
  En (poly x) i = Ep x i

  0h : ∀ {n} → Poly n
  0n : ∀ {n} → Normal n
  0h = ∅
  0n {zero} = con 0
  0n {suc n} = poly 0h

  1h : ∀ {n} → Poly (suc n)
  1n : ∀ {n} → Normal n

  1h {n} = ∅ *x+ 1n {n}
  1n {zero} = con 1
  1n {suc n} = poly 1h

  -- The more cases that we can approximate here, the more powerful the
  -- solver becomes.
  _==ₕ_ : ∀ {n} (x y : Poly n) → Maybe (x ≡ y)
  _==ₙ_ : ∀ {n} (x y : Normal n) → Maybe (x ≡ y)

  ∅ ==ₕ ∅ = just refl
  ∅ ==ₕ (_ *x+ _) = nothing
  (_ *x+ _) ==ₕ ∅ = nothing
  (p *x+ x) ==ₕ (q *x+ y) with p ==ₕ q | x ==ₙ y
  ... | just p=q | just x=y = just $ ap₂ _*x+_ p=q x=y
  ... | just _   | nothing = nothing
  ... | nothing  | just _  = nothing
  ... | nothing  | nothing = nothing

  con c ==ₙ con d with c ≡? d
  ... | yes c=d = just (ap con c=d)
  ... | no ¬c=d = nothing
  poly x ==ₙ poly y with x ==ₕ y
  ... | just x=y = just $ ap poly x=y
  ... | nothing  = nothing

  _*x+ₙ_ : ∀ {n} → Poly (suc n) → Normal n → Poly (suc n)
  (p *x+ c') *x+ₙ c = (p *x+ c') *x+ c
  ∅          *x+ₙ c with c ==ₙ 0n
  ... | just c≈0 = ∅
  ... | nothing  = ∅ *x+ c

  _+ₚ_ : ∀ {n} → Poly (suc n) → Poly (suc n) → Poly (suc n)
  _+ₙ_ : ∀ {n} → Normal n → Normal n → Normal n

  ∅         +ₚ y         = y
  y         +ₚ ∅         = y
  (p *x+ x) +ₚ (q *x+ y) = (p +ₚ q) *x+ₙ (x +ₙ y)

  con x  +ₙ con y = con (x +ℤ y)
  poly x +ₙ poly y = poly (x +ₚ y)

  _*x+ₚ_ : ∀ {n} → Poly (suc n) → Poly (suc n) → Poly (suc n)
  p *x+ₚ (q *x+ d) = (p +ₚ q) *x+ₙ d
  ∅ *x+ₚ ∅         = ∅
  (p *x+ c) *x+ₚ ∅ = (p *x+ c) *x+ 0n

  _*ₙₚ_ : ∀ {n} → Normal n → Poly (suc n) → Poly (suc n)
  _*ₚₙ_ : ∀ {n} → Poly (suc n) → Normal n → Poly (suc n)
  _*ₚ_  : ∀ {n} → Poly (suc n) → Poly (suc n) → Poly (suc n)
  _*ₙ_  : ∀ {n} → Normal n → Normal n → Normal n

  infix 30 _*ₙₚ_ _*ₚₙ_ _*ₚ_ _*ₙ_

  c *ₙₚ ∅ = ∅
  c *ₙₚ (p *x+ d) with c ==ₙ 0n
  ... | just _  = ∅
  ... | nothing = (c *ₙₚ p) *x+ (c *ₙ d)

  ∅ *ₚₙ y = ∅
  (p *x+ c) *ₚₙ d with d ==ₙ 0n
  ... | just _  = ∅
  ... | nothing = (p *ₚₙ d) *x+ (c *ₙ d)

  con x  *ₙ con y  = con (x *ℤ y)
  poly x *ₙ poly y = poly (x *ₚ y)

  ∅ *ₚ _ = ∅
  (p *x+ c) *ₚ ∅ = ∅
  (p *x+ c) *ₚ (q *x+ d) = ((p *ₚ q) *x+ₚ (p *ₚₙ d +ₚ c *ₙₚ q)) *x+ₙ (c *ₙ d)

  -ₙ_ : ∀ {n} → Normal n → Normal n
  -ₚ_ : ∀ {n} → Poly (suc n) → Poly (suc n)

  -ₙ con x = con (negℤ x)
  -ₙ poly x = poly (-ₚ x)

  -ₚ x = (-ₙ 1n) *ₙₚ x

  data Op : Type where
    [+] : Op
    [*] : Op

  data Polynomial (m : Nat) : Type ℓ where
    op   : (o : Op) (p q : Polynomial m) → Polynomial m
    con  : (c : Int) → Polynomial m
    var  : (x : Fin m) → Polynomial m
    :-_  : (p : Polynomial m) → Polynomial m

  -- Short-hand notation.

  infixl 30 _:-_ _:+_
  infixl 40 _:*_

  _:+_ : ∀ {n} → Polynomial n → Polynomial n → Polynomial n
  _:+_ = op [+]

  _:*_ : ∀ {n} → Polynomial n → Polynomial n → Polynomial n
  _:*_ = op [*]

  _:-_ : ∀ {n} → Polynomial n → Polynomial n → Polynomial n
  x :- y = x :+ (:- y)

  _:×_ : ∀ {n} → Nat → Polynomial n → Polynomial n
  zero :× p = con 0
  suc m :× p = p :+ (m :× p)

  sem : Op → R → R → R
  sem [+] = R._+_
  sem [*] = R._*_

  eval : ∀ {n} → Polynomial n → Vec R n → R

  instance
    ⟦⟧-Polynomial : ∀ {n} → ⟦⟧-notation (Polynomial n)
    ⟦⟧-Polynomial = brackets _ eval

    Number-Polynomial : ∀ {n} → Number (Polynomial n)
    Number-Polynomial .Number.Constraint x = Lift _ ⊤
    Number-Polynomial .Number.fromNat n = con (pos n)

  eval (op o p₁ p₂) ρ = sem o (⟦ p₁ ⟧ ρ) (⟦ p₂ ⟧ ρ)
  eval (con c)      ρ = embed-coe c
  eval (var x)      ρ = lookup ρ x
  eval (:- p)       ρ = R.- ⟦ p ⟧ ρ

  ---

  normal-coe : ∀ {n} → Int → Normal n
  normal-coe {zero} x  = con x
  normal-coe {suc n} x = poly (∅ *x+ₙ normal-coe x)

  normal-var : ∀ {n} → Fin n → Normal n
  normal-var i with fin-view i
  ... | zero  = poly ((∅ *x+ 1n) *x+ 0n)
  ... | suc f = poly (∅ *x+ₙ normal-var f)

  normal : ∀ {n} → Polynomial n → Normal n
  normal (op [+] x y) = normal x +ₙ normal y
  normal (op [*] x y) = normal x *ₙ normal y
  normal (con c) = normal-coe c
  normal (var x) = normal-var x
  normal (:- x) = -ₙ (normal x)

  ⟦_⟧ₙ : ∀ {n} → Polynomial n → Vec R n → R
  ⟦ x ⟧ₙ ρ = En (normal x) ρ

  0n-hom : ∀ {n} (ρ : Vec R n) → En 0n ρ ≡ R.0r
  0n-hom [] = ℤ↪R.pres-0
  0n-hom (x ∷ ρ) = refl

  1n-hom : ∀ {n} (ρ : Vec R n) → En 1n ρ ≡ R.1r
  1n-hom [] = ℤ↪R.pres-id
  1n-hom (x ∷ ρ) =
    (R.0r R.* x) R.+ (En 1n ρ) ≡⟨ R.eliml R.*-zerol ⟩
    En 1n ρ                    ≡⟨ 1n-hom ρ ⟩
    R.1r                       ∎

  *x+ₙ-sound
    : ∀ {n} (p : Poly (suc n)) (c : Normal n) ρ
    → Ep (p *x+ₙ c) ρ ≡ Ep (p *x+ c) ρ
  *x+ₙ-sound ∅ c (e ∷ ρ) with c ==ₙ 0n
  ... | just x = sym $
    Ep (∅ *x+ ⌜ c ⌝) (e ∷ ρ)   ≡⟨ ap! x ⟩
    Ep (∅ *x+ 0n) (e ∷ ρ)      ≡⟨⟩
    (R.0r R.* e) R.+ En 0n ρ ≡⟨ R.eliml R.*-zerol ⟩
    En 0n ρ                  ≡⟨ 0n-hom ρ ⟩
    R.0r                               ∎
  ... | nothing = refl
  *x+ₙ-sound (p *x+ x) c ρ = refl

  ∅*x+ₙ-hom
    : ∀ {n} (c : Normal n) x ρ
    → Ep (∅ *x+ₙ c) (x ∷ ρ) ≡ En c ρ
  ∅*x+ₙ-hom c x ρ with c ==ₙ 0n
  ... | just x = sym (ap (λ c → En c ρ) x ∙ 0n-hom ρ)
  ... | nothing = R.eliml R.*-zerol

  +ₚ-hom
    : ∀ {n} (p q : Poly (suc n)) ρ
    → Ep (p +ₚ q) ρ ≡ Ep p ρ R.+ Ep q ρ
  +ₙ-hom
    : ∀ {n} (p q : Normal n) ρ
    → En (p +ₙ q) ρ ≡ En p ρ R.+ En q ρ

  +ₚ-hom ∅ q ρ = sym R.+-idl
  +ₚ-hom (p *x+ x) ∅ ρ = sym R.+-idr
  +ₚ-hom (p *x+ c) (q *x+ d) (x ∷ ρ) =
    Ep ((p +ₚ q) *x+ₙ (c +ₙ d)) (x ∷ ρ)                                 ≡⟨ *x+ₙ-sound (p +ₚ q) (c +ₙ d) (x ∷ ρ) ⟩
    Ep ((p +ₚ q) *x+ (c +ₙ d)) (x ∷ ρ)                                  ≡⟨⟩
    ⌜ Ep (p +ₚ q) (x ∷ ρ) ⌝ R.* x R.+ En (c +ₙ d) ρ                     ≡⟨ ap! (+ₚ-hom p q (x ∷ ρ)) ⟩
    (Ep p (x ∷ ρ) R.+ Ep q (x ∷ ρ)) R.* x R.+ ⌜ En (c +ₙ d) ρ ⌝         ≡⟨ ap! (+ₙ-hom c d ρ) ⟩
    ⌜ (Ep p (x ∷ ρ) R.+ Ep q (x ∷ ρ)) R.* x ⌝ R.+ (En c ρ R.+ En d ρ)   ≡⟨ ap! R.*-distribr  ⟩
    Ep p (x ∷ ρ) R.* x R.+ Ep q (x ∷ ρ) R.* x R.+ (En c ρ R.+ En d ρ)   ≡⟨ R.a.pullr (R.pulll R.+-commutes) ⟩
    Ep p (x ∷ ρ) R.* x R.+ (En c ρ R.+ Ep q (x ∷ ρ) R.* x R.+ En d ρ)   ≡⟨ R.a.extendl (R.a.pulll refl) ⟩
    Ep p (x ∷ ρ) R.* x R.+ En c ρ R.+ (Ep q (x ∷ ρ) R.* x R.+ En d ρ)   ∎
  +ₙ-hom (con x)  (con y)  ρ = ℤ↪R.pres-+ (lift x) (lift y)
  +ₙ-hom (poly p) (poly q) ρ = +ₚ-hom p q ρ

  *x+-hom
    : ∀ {n} (p q : Poly (suc n)) x ρ
    → Ep (p *x+ₚ q) (x ∷ ρ)
    ≡ Ep p (x ∷ ρ) R.* x R.+ Ep q (x ∷ ρ)
  *x+-hom ∅ ∅ x ρ = R.introl R.*-zerol
  *x+-hom (p *x+ c) ∅ x ρ = ap₂ R._+_ refl (0n-hom ρ)
  *x+-hom p (q *x+ d) x ρ =
    Ep (p *x+ₚ (q *x+ d)) (x ∷ ρ)                          ≡⟨⟩
    Ep ((p +ₚ q) *x+ₙ d) (x ∷ ρ)                           ≡⟨ *x+ₙ-sound (p +ₚ q) d (x ∷ ρ) ⟩
    ⌜ Ep (p +ₚ q) (x ∷ ρ) ⌝ R.* x R.+ En d ρ               ≡⟨ ap! (+ₚ-hom p q (x ∷ ρ)) ⟩
    ⌜ (Ep p (x ∷ ρ) R.+ Ep q (x ∷ ρ)) R.* x ⌝ R.+ En d ρ   ≡⟨ ap! R.*-distribr ⟩
    Ep p (x ∷ ρ) R.* x R.+ Ep q (x ∷ ρ) R.* x R.+ En d ρ   ≡⟨ R.pullr refl ⟩
    Ep p (x ∷ ρ) R.* x R.+ (Ep q (x ∷ ρ) R.* x R.+ En d ρ) ∎

  *ₙₚ-hom
    : ∀ {n} (c : Normal n) (p : Poly (suc n)) x ρ
    → Ep (c *ₙₚ p) (x ∷ ρ) ≡ En c ρ R.* Ep p (x ∷ ρ)
  *ₚₙ-hom
    : ∀ {n} (c : Normal n) (p : Poly (suc n)) x ρ
    → Ep (p *ₚₙ c) (x ∷ ρ) ≡ Ep p (x ∷ ρ) R.* En c ρ
  *ₙ-hom : ∀ {n} (c d : Normal n) ρ → En (c *ₙ d) ρ ≡ En c ρ R.* En d ρ
  *ₚ-hom : ∀ {n} (p q : Poly (suc n)) ρ → Ep (p *ₚ q) ρ ≡ Ep p ρ R.* Ep q ρ

  *ₚ-hom ∅ q ρ = sym R.*-zerol
  *ₚ-hom (p *x+ c) ∅ ρ = sym R.*-zeror
  *ₚ-hom (p *x+ c) (q *x+ d) (x ∷ ρ) =
      *x+ₙ-sound ((p *ₚ q) *x+ₚ ((p *ₚₙ d) +ₚ (c *ₙₚ q))) _ (x ∷ ρ)
    ∙ ap₂ R._+_ (ap₂ R._*_ (*x+-hom (p *ₚ q) ((p *ₚₙ d) +ₚ (c *ₙₚ q)) x ρ) refl) refl
    ∙ ap₂ R._+_ (ap₂ R._*_ (ap₂ R._+_ (ap (R._* x) (*ₚ-hom p q (x ∷ ρ)))
        (+ₚ-hom (p *ₚₙ d) (c *ₙₚ q) (x ∷ ρ))) refl
        ∙ ap₂ R._*_ (ap₂ R._+_ refl (ap₂ R._+_ (*ₚₙ-hom d p x ρ) (*ₙₚ-hom c q x ρ)))
        refl) refl
    ∙ ap₂ R._+_ refl (*ₙ-hom c d ρ) ∙ lemma _ _ _ _ _
    where
    lemma
      : ∀ p q x d c
      → (p R.* q R.* x R.+ ((p R.* d) R.+ (c R.* q))) R.* x R.+ (c R.* d)
      ≡ (p R.* x R.+ c) R.* (q R.* x R.+ d)
    lemma a c x d b =
      (a R.* c R.* x R.+ (a R.* d R.+ b R.* c)) R.* x R.+ b R.* d                 ≡⟨ ap₂ R._+_ R.*-distribr refl ⟩
      (a R.* c R.* x R.* x R.+ (a R.* d R.+ b R.* c) R.* x) R.+ b R.* d           ≡⟨ sym R.+-associative ⟩
      a R.* c R.* x R.* x R.+ ((a R.* d R.+ b R.* c) R.* x R.+ b R.* d)           ≡⟨ ap₂ R._+_ lem₁ (ap₂ R._+_ lem₂ refl) ⟩
      a R.* x R.* (c R.* x) R.+ (a R.* x R.* d R.+ b R.* (c R.* x) R.+ b R.* d)   ≡⟨ ap₂ R._+_ refl (sym R.+-associative) ⟩
      a R.* x R.* (c R.* x) R.+ (a R.* x R.* d R.+ (b R.* (c R.* x) R.+ b R.* d)) ≡⟨ R.+-associative ⟩
      a R.* x R.* (c R.* x) R.+ a R.* x R.* d R.+ (b R.* (c R.* x) R.+ b R.* d)   ≡˘⟨ ap₂ R._+_ R.*-distribl R.*-distribl ⟩
      a R.* x R.* (c R.* x R.+ d) R.+ b R.* (c R.* x R.+ d)                       ≡˘⟨ R.*-distribr ⟩
      (a R.* x R.+ b) R.* (c R.* x R.+ d)                                         ∎
      where
      lem₁' =
        a R.* c R.* x     ≡˘⟨ R.*-associative ⟩
        a R.* ⌜ c R.* x ⌝ ≡⟨ ap! *-commutes ⟩
        a R.* (x R.* c)   ≡⟨ R.*-associative ⟩
        a R.* x R.* c     ∎

      lem₁ =
        a R.* c R.* x R.* x    ≡⟨ ap₂ R._*_ lem₁' refl ⟩
        a R.* x R.* c R.* x    ≡˘⟨ R.*-associative ⟩
        a R.* x R.* (c R.* x)  ∎

      lem₂ =
        (a R.* d R.+ b R.* c) R.* x           ≡⟨ R.*-distribr ⟩
        a R.* d R.* x R.+ b R.* c R.* x       ≡˘⟨ ap₂ R._+_ R.*-associative R.*-associative ⟩
        a R.* ⌜ d R.* x ⌝ R.+ b R.* (c R.* x) ≡⟨ ap! *-commutes ⟩
        a R.* (x R.* d) R.+ b R.* (c R.* x)   ≡⟨ ap₂ R._+_ R.*-associative refl ⟩
        a R.* x R.* d R.+ b R.* (c R.* x)     ∎

  *ₙ-hom (con x) (con y) ρ = ℤ↪R.pres-* (lift x) (lift y)
  *ₙ-hom (poly p) (poly q) ρ = *ₚ-hom p q ρ

  *ₙₚ-hom c ∅ x ρ = sym R.*-zeror
  *ₙₚ-hom c (p *x+ d) x ρ with c ==ₙ 0n
  ... | just c=0 = sym (ap₂ R._*_ (ap (λ e → En e ρ) c=0 ∙ 0n-hom ρ) refl ∙ R.*-zerol)
  ... | nothing =
      ap₂ R._+_ (ap (R._* x) (*ₙₚ-hom c p x ρ) ∙ sym R.*-associative) (*ₙ-hom c d ρ)
    ∙ sym R.*-distribl

  *ₚₙ-hom c ∅ x ρ = sym R.*-zerol
  *ₚₙ-hom c (p *x+ d) x ρ with c ==ₙ 0n
  ... | just c=0 = sym (ap₂ R._*_ refl (ap (λ e → En e ρ) c=0 ∙ 0n-hom ρ) ∙ R.*-zeror)
  ... | nothing  =
      ap₂ R._+_ (ap (R._* x) (*ₚₙ-hom c p x ρ) ∙∙ sym R.*-associative ∙∙ ap₂ R._*_ refl *-commutes ∙ R.*-associative)
        (*ₙ-hom d c ρ)
    ∙ sym R.*-distribr

  -ₚ-hom : ∀ {n} (p : Poly (suc n)) ρ → Ep (-ₚ p) ρ ≡ R.- Ep p ρ
  -ₙ-hom : ∀ {n} (n : Normal n) ρ → En (-ₙ n) ρ ≡ R.- En n ρ

  -ₚ-hom p (x ∷ ρ) =
      *ₙₚ-hom (-ₙ 1n) p x ρ
    ∙ ap₂ R._*_ (-ₙ-hom 1n ρ ∙ ap R.-_ (1n-hom ρ)) refl
    ∙ R.*-negatel ∙ ap R.-_ R.*-idl
  -ₙ-hom (con x) ρ = ℤ↪R.pres-neg {x = lift x}
  -ₙ-hom (poly x) ρ = -ₚ-hom x ρ

  sound-coe
    : ∀ {n} (c : Int) (ρ : Vec R n) → En (normal-coe c) ρ ≡ embed-coe c
  sound-coe c [] = refl
  sound-coe c (x ∷ ρ) = ∅*x+ₙ-hom (normal-coe c) x ρ ∙ sound-coe c ρ

  sound-var : ∀ {n} (j : Fin n) ρ → En (normal-var j) ρ ≡ lookup ρ j
  sound-var i _ with fin-view i
  sound-var _ (x ∷ ρ) | zero =
    Ep (∅ *x+ 1n) (x ∷ ρ) R.* x R.+ En 0n ρ ≡⟨ R.elimr (0n-hom ρ) ⟩
    ⌜ Ep (∅ *x+ 1n) (x ∷ ρ) ⌝ R.* x         ≡⟨ ap! (R.eliml R.*-zerol ∙ 1n-hom ρ) ⟩
    R.1r R.* x                              ≡⟨ R.*-idl ⟩
    x                                       ∎
  sound-var _ (x ∷ ρ) | suc j = ∅*x+ₙ-hom (normal-var j) x ρ ∙ sound-var j ρ

  sound : ∀ {n} (p : Polynomial n) ρ → En (normal p) ρ ≡ ⟦ p ⟧ ρ
  sound (op [+] p q) ρ = +ₙ-hom (normal p) (normal q) ρ ∙ ap₂ R._+_ (sound p ρ) (sound q ρ)
  sound (op [*] p q) ρ = *ₙ-hom (normal p) (normal q) ρ ∙ ap₂ R._*_ (sound p ρ) (sound q ρ)
  sound (con c) ρ = sound-coe c ρ
  sound (var x) ρ = sound-var x ρ
  sound (:- p) ρ = -ₙ-hom (normal p) ρ ∙ ap R.-_ (sound p ρ)

  expand : ∀ {n} → Polynomial n → Vec R n → R
  expand e ρ = ⟦ e ⟧ ρ

  solve
    : ∀ {n} (p q : Polynomial n) (r : Vec R n)
    → En (normal p) r ≡ En (normal q) r → ⟦ p ⟧ r ≡ ⟦ q ⟧ r
  solve p q r prf = sym (sound p r) ∙∙ prf ∙∙ sound q r

  private
    test-distrib : ∀ x y z → x R.* (y R.+ z) ≡ y R.* x R.+ z R.* x
    test-distrib x y z =
      solve (var 0 :* (var 1 :+ var 2)) ((var 1 :* var 0) :+ (var 2 :* var 0)) (x ∷ y ∷ z ∷ []) refl

    test-identities : ∀ x → x R.+ (R.0r R.* R.1r) ≡ (R.1r R.+ R.0r) R.* x
    test-identities x =
      solve (var 0 :+ (con 0 :* con 1)) ((con 1 :+ con 0) :* var 0) (x ∷ []) refl

module Explicit {ℓ} (R : CRing ℓ) where
  private module I = Impl (R .snd)

  open I renaming (solve to solve-impl)
  open I public using (Polynomial ; _:+_ ; _:-_ ; :-_ ; _:*_ ; con ; Number-Polynomial)

  _≔_ : ∀ {n} → Polynomial n → Polynomial n → Polynomial n × Polynomial n
  x ≔ y = x , y

  private
    variables : ∀ {n} → Πᶠ {n = n} λ i → Polynomial n
    variables = tabulateₚ var

  abstract
    solve
      : (n : Nat) (f : Arrᶠ {n = n} (λ i → Polynomial n) (Polynomial n × Polynomial n))
      → (let (lhs , rhs) = applyᶠ {n = n} f variables)
      → ∀ᶠ n (λ i → ⌞ R ⌟) λ vs
        → (let rs = tabulate (indexₚ vs))
        → En (normal lhs) rs ≡ En (normal rhs) rs
        → ⟦ lhs ⟧ rs ≡ ⟦ rhs ⟧ rs
    solve n f = curry-∀ᶠ {n = n} (λ a → solve-impl lhs rhs (tabulate (indexₚ a)))
      where open Σ (applyᶠ {n = n} f variables) renaming (fst to lhs ; snd to rhs)

module Reflection where
  private
    pattern ring-args cring args = (_ hm∷ _ hm∷ cring v∷ args)
    pattern is-ring-args is-ring args = (_ hm∷ _ hm∷ _ hm∷ _ hm∷ _ hm∷ is-ring v∷ args)
    pattern is-group-args is-group args = (_ hm∷ _ hm∷ _ hm∷ is-group v∷ args)
    pattern ring-field field-name cring args =
      def field-name (ring-args (def (quote CRing-on.has-ring-on) (ring-args cring [])) args)
    pattern group-field field-name cring args =
      def field-name
        (is-group-args
          (def (quote (is-abelian-group.has-is-group))
            (_ hm∷ _ hm∷ _ hm∷ def (quote is-ring.+-group)
              (is-ring-args (ring-field (quote Ring-on.has-is-ring) cring []) []) v∷ []))
          args)

    mk-cring-args : Term → List (Arg Term) → List (Arg Term)
    mk-cring-args cring args = unknown h∷ unknown h∷ cring v∷ args

    pattern “1” cring = ring-field (quote Ring-on.1r) cring []
    pattern “*” cring x y = ring-field (quote Ring-on._*_) cring (x v∷ y v∷ [])
    pattern “+” cring x y = ring-field (quote Ring-on._+_) cring (x v∷ y v∷ [])
    pattern “0” cring = group-field (quote is-group.unit) cring []
    pattern “-” cring x = group-field (quote is-group.inverse) cring (x v∷ [])

  “expand” : Term → Term → Term → Term
  “expand” cring p env = def (quote Impl.expand) (mk-cring-args cring (unknown h∷ p v∷ env v∷ []))

  “solve” : Term → Term → Term → Term → Term
  “solve” cring lhs rhs env =
    def (quote Impl.solve) (mk-cring-args cring (unknown h∷ lhs v∷ rhs v∷ env v∷ “refl” v∷ []))

  build-expr : ∀ {ℓ} {A : Type ℓ} → Term → Variables A → Term → TC (Term × Variables A)
  build-expr cring vs (“0” cring') = do
    unify cring cring'
    z ← quoteTC (Int.pos 0)
    pure $ con (quote Impl.Polynomial.con) (z v∷ []) , vs
  build-expr cring vs (“1” cring') = do
    unify cring cring'
    o ← quoteTC (Int.pos 1)
    pure $ con (quote Impl.Polynomial.con) (o v∷ []) , vs
  build-expr cring vs (“*” cring' t1 t2) = do
    unify cring cring'
    e1 , vs ← build-expr cring vs t1
    e2 , vs ← build-expr cring vs t2
    pure $ def (quote Impl._:*_) (mk-cring-args cring $ e1 v∷ e2 v∷ []) , vs
  build-expr cring vs (“+” cring' t1 t2) = do
    unify cring cring'
    e1 , vs ← build-expr cring vs t1
    e2 , vs ← build-expr cring vs t2
    pure $ def (quote Impl._:+_) (mk-cring-args cring $ e1 v∷ e2 v∷ []) , vs
  build-expr cring vs (“-” cring' tm) = do
    unify cring cring'
    e , vs ← build-expr cring vs tm
    pure $ con (quote Impl.Polynomial.:-_) (e v∷ []) , vs
  build-expr cring vs tm = do
    (v , vs) ← bind-var vs tm
    pure $ con (quote Impl.Polynomial.var) (v v∷ []) , vs

  dont-reduce : List Name
  dont-reduce =
    quote Number.fromNat ∷
    quote Ring-on.1r ∷
    quote Ring-on._*_ ∷
    quote Ring-on._+_ ∷
    []

  cring-solver : ∀ {ℓ} {A : Type ℓ} → CRing-on A → TC (VariableSolver A)
  cring-solver {A = A} cring = do
    cring-tm ← quoteTC cring
    pure $ var-solver dont-reduce (build-expr cring-tm) (“solve” cring-tm) (“expand” cring-tm)

  repr-macro : ∀ {ℓ} {A : Type ℓ} → CRing-on A → Term → Term → TC ⊤
  repr-macro cring tm hole = do
    solver ← cring-solver cring
    mk-var-repr solver tm

  expand-macro : ∀ {ℓ} {A : Type ℓ} → CRing-on A → Term → Term → TC ⊤
  expand-macro cring tm hole = do
    solver ← cring-solver cring
    mk-var-normalise solver tm hole

  solve-macro : ∀ {ℓ} {A : Type ℓ} → CRing-on A → Term → TC ⊤
  solve-macro cring hole = do
    solver ← cring-solver cring
    mk-var-solver solver hole

macro
  cring-repr! : ∀ {ℓ} → CRing ℓ → Term → Term → TC ⊤
  cring-repr! cring tm = Reflection.repr-macro (cring .snd) tm

  cring-simpl! : ∀ {ℓ} → CRing ℓ → Term → Term → TC ⊤
  cring-simpl! cring tm = Reflection.expand-macro (cring .snd) tm

  cring-on! : ∀ {ℓ} {A : Type ℓ} → CRing-on A → Term → TC ⊤
  cring-on! cring = Reflection.solve-macro cring

  cring! : ∀ {ℓ} → CRing ℓ → Term → TC ⊤
  cring! cring = Reflection.solve-macro (cring .snd)

private module TestCRing {ℓ} (R : CRing ℓ) where
  module R = CRing-on (R .snd)

  test-distrib : ∀ x y z → x R.* (y R.+ z) ≡ (y R.* x) R.+ (z R.* x)
  test-distrib x y z = cring! R

  test-identities : ∀ x → x R.+ (R.0r R.* R.1r) ≡ (R.1r R.+ R.0r) R.* x
  test-identities x = cring! R

  test-negation : ∀ x y → x R.* (R.- y) ≡ R.- (x R.* y)
  test-negation x y = cring! R

private module TestExplicit where
  open Explicit ℤ-comm

  _ : ∀ x y u v → (x B.*ℤ y) B.*ℤ (u B.*ℤ v) ≡ (x B.*ℤ u) B.*ℤ (y B.*ℤ v)
  _ = λ x y u v → solve 4
    (λ x y u v → (x :* y) :* (u :* v) ≔ (x :* u) :* (y :* v))
    x y u v refl
