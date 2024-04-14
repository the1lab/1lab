open import 1Lab.Reflection.Signature
open import 1Lab.Reflection.Copattern
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
  get-dual : Bool → Term → TC (Term → Term)
  get-dual false _ = pure (λ t → t)
  get-dual true T = resetting do
    (mv , _) ← new-meta' (def (quote Dualises) [ argN T ])
    (qn ∷ []) ← get-instances mv
      where _ → typeError [ "Don't know how to dualise type " , termErr T ]
    du ← normalise (def (quote dualiser) [ argN qn ])
      >>= unquoteTC {A = Name}
    pure λ t → def du [ argN t ]

cohere-dualise : Bool → ∀ {ℓ} {S : Type ℓ} → S → Term → TC ⊤
cohere-dualise is-dual tm hole = do
  `tm ← quoteTC tm
  `T ← infer-type hole
  (c , fs) ← get-record `T
  dual ← get-dual is-dual `T
  args ← for fs λ (arg ai prj) → do
    t ← reduce $ def prj [ argN (dual `tm) ]
    pure (argN t)

  unify hole (con c args)

nat-assoc-to    : f ⇒ g ⊗ h ⊗ i → f ⇒ (g ⊗ h) ⊗ i
nat-assoc-from  : f ⊗ g ⊗ h ⇒ i → (f ⊗ g) ⊗ h ⇒ i
op-compose-into : f ⇒ Functor.op (g ⊗ h) → f ⇒ Functor.op g ⊗ Functor.op h
nat-assoc-to-op : f ⇒ g ⊗ h ⊗ i → (Functor.op g ⊗ Functor.op h) ⊗ Functor.op i ⇒ Functor.op f

unquoteDef nat-assoc-to nat-assoc-from op-compose-into nat-assoc-to-op = do
  define-eta-expansion nat-assoc-to
  define-eta-expansion nat-assoc-from
  define-eta-expansion op-compose-into
  define-eta-expansion-with nat-assoc-to-op (quote _=>_.op)
