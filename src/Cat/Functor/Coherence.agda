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

define-coherence : Name → TC ⊤
define-coherence nm = define-eta-expansion nm

nat-assoc-to     : f ⇒ g ⊗ h ⊗ i → f ⇒ (g ⊗ h) ⊗ i
nat-assoc-from   : f ⊗ g ⊗ h ⇒ i → (f ⊗ g) ⊗ h ⇒ i
nat-unassoc-to   : f ⇒ (g ⊗ h) ⊗ i → f ⇒ g ⊗ h ⊗ i
nat-unassoc-from : (f ⊗ g) ⊗ h ⇒ i → f ⊗ g ⊗ h ⇒ i
nat-idl-to       : f ⇒ Id ⊗ g → f ⇒ g
nat-idl-from     : Id ⊗ f ⇒ g → f ⇒ g
nat-unidl-to   : f ⇒ g → f ⇒ Id ⊗ g
nat-unidl-from   : f ⇒ g → Id ⊗ f ⇒ g
nat-unidr-to   : f ⇒ g → f ⇒ g ⊗ Id
nat-unidr-from   : f ⇒ g → f ⊗ Id ⇒ g
op-compose-into  : f ⇒ Functor.op (g ⊗ h) → f ⇒ Functor.op g ⊗ Functor.op h

unquoteDef nat-assoc-to nat-assoc-from nat-unassoc-to nat-unassoc-from nat-idl-to nat-idl-from nat-unidl-to nat-unidl-from nat-unidr-to nat-unidr-from op-compose-into = do
  define-eta-expansion nat-assoc-to
  define-eta-expansion nat-assoc-from
  define-eta-expansion nat-unassoc-to
  define-eta-expansion nat-unassoc-from
  define-eta-expansion nat-idl-to
  define-eta-expansion nat-idl-from
  define-eta-expansion nat-unidl-to
  define-eta-expansion nat-unidl-from
  define-eta-expansion nat-unidr-to
  define-eta-expansion nat-unidr-from
  define-eta-expansion op-compose-into
