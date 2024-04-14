open import 1Lab.Reflection.Copattern
open import 1Lab.Reflection.Signature
open import 1Lab.Reflection

open import Cat.Prelude

open import Data.List.Base

import Cat.Functor.Compose

module Cat.Functor.Coherence where

open Cat.Functor.Compose public

private
  variable
    o ℓ : Level
    C D E : Precategory o ℓ
    f g h i : Functor C D

  _⊗_ = _F∘_
  infixr 30 _⊗_

  _⇒_ = _=>_
  infix 20 _⇒_

  {-# INLINE _⊗_ #-}
  {-# INLINE _⇒_ #-}

record Dualises {ℓ} (T : Type ℓ) : Type where
  field
    dualiser : Name

open Dualises

instance
  Dualises-nat-trans
    : ∀ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
        {F G : Functor C D}
    → Dualises (F => G)
  Dualises-nat-trans .dualiser = quote _=>_.op

private
  get-dual : Term → TC Name
  get-dual T = resetting do
    (mv , _) ← new-meta' (def (quote Dualises) [ argN T ])
    (qn ∷ []) ← get-instances mv
      where _ → typeError [ "Don't know how to dualise type " , termErr T ]
    unquoteTC =<< normalise (def (quote dualiser) [ argN qn ])

make-cohere : ∀ {ℓ} {S : Type ℓ} → S → Term → TC ⊤
make-cohere tm hole = do
  `tm ← quoteTC tm
  `T ← infer-type hole
  `R ← repack-record `tm `T
  unify hole `R

make-dualise : ∀ {ℓ} {S : Type ℓ} → S → Term → TC ⊤
make-dualise tm hole = do
  `tm ← quoteTC tm
  `T ← infer-type hole
  dual ← get-dual `T
  -- Repack using the duality lemma.
  `R ← repack-record (def dual [ argN `tm ]) `T
  unify hole `R

macro
  cohere!  = make-cohere
  dualise! = make-dualise

cohere-into : ∀ {ℓ ℓ'} {S : Type ℓ'} → Name → (T : Type ℓ) → S → TC ⊤
cohere-into nm T s = do
  `s ← quoteTC s
  `T ← quoteTC T
  make-copattern true nm `s `T

dualise-into : ∀ {ℓ ℓ'} {S : Type ℓ'} → Name → (T : Type ℓ) → ⦃ Dualises T ⦄ → S → TC ⊤
dualise-into nm T ⦃ dual ⦄ s = do
  `s ← quoteTC s
  `T ← quoteTC T
  make-copattern true nm (def (dual .dualiser) (argN `s ∷ [])) `T

define-coherence : Name → TC ⊤
define-coherence nm = define-eta-expansion nm

define-dualiser : Name → TC ⊤
define-dualiser nm  = do
  tp ← infer-type (def nm [])
  let (tele , cod-tp) = pi-view tp
  -- Find the appropriate duality lemma, and construct a copattern using that lemma.
  dual ← in-context (reverse tele) (get-dual cod-tp)
  let tm = tel→lam tele (def dual (argN (var 0 []) ∷ []))
  make-copattern false nm tm tp

nat-assoc-to    : f ⇒ g ⊗ h ⊗ i → f ⇒ (g ⊗ h) ⊗ i
nat-assoc-from  : f ⊗ g ⊗ h ⇒ i → (f ⊗ g) ⊗ h ⇒ i
op-compose-into : f ⇒ Functor.op (g ⊗ h) → f ⇒ Functor.op g ⊗ Functor.op h

unquoteDef nat-assoc-to nat-assoc-from op-compose-into = do
  define-eta-expansion nat-assoc-to
  define-eta-expansion nat-assoc-from
  define-eta-expansion op-compose-into
