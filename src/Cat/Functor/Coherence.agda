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

cohere-dualise-into : Bool → ∀ {ℓ ℓ'} {S : Type ℓ'} → Name → (T : Type ℓ) → S → TC ⊤
cohere-dualise-into is-dual nam T tm = do
  `tm ← quoteTC tm
  `T ← quoteTC T
  (_ , fs) ← get-record `T
  dual ← get-dual is-dual `T
  clauses ← for fs λ (arg ai prj) → do
    t ← reduce $ def prj [ argN (dual `tm) ]
    pure $ clause [] [ arg ai (proj prj) ] t

  declare (argN nam) `T
  define-function nam clauses

define-coherator-dualiser : Bool → Name → TC ⊤
define-coherator-dualiser is-dual nam = do
  (fs , dual) ← run-speculative do
    `T ← infer-type (def nam [ argN unknown ])
    (_ , fs) ← get-record `T
    dual ← get-dual is-dual `T
    pure ((fs , dual) , false)
  clauses ← for fs λ (arg ai prj) → do
    pure $ clause (("α" , argN unknown) ∷ [])
              [ argN (var 0) , arg ai (proj prj) ]
              (def prj [ argN (dual (var 0 [])) ])

  define-function nam clauses

macro
  cohere!  = cohere-dualise false
  dualise! = cohere-dualise true

cohere-into      = cohere-dualise-into false
dualise-into     = cohere-dualise-into true
define-coherence = define-coherator-dualiser false
define-dualiser  = define-coherator-dualiser true

nat-assoc-to    : f ⇒ g ⊗ h ⊗ i → f ⇒ (g ⊗ h) ⊗ i
nat-assoc-from  : f ⊗ g ⊗ h ⇒ i → (f ⊗ g) ⊗ h ⇒ i
op-compose-into : f ⇒ Functor.op (g ⊗ h) → f ⇒ Functor.op g ⊗ Functor.op h

unquoteDef nat-assoc-to nat-assoc-from op-compose-into = do
  define-coherence nat-assoc-to
  define-coherence nat-assoc-from
  define-coherence op-compose-into
