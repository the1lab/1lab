open import 1Lab.Reflection

open import Cat.Prelude

import Cat.Instances.Functor.Compose

module Cat.Functor.Coherence where

open Cat.Instances.Functor.Compose public
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
    fields   : List (Arg Name)
    dualiser : Name

instance
  Dualises-nat-trans
    : ∀ {o ℓ o′ ℓ′} {C : Precategory o ℓ} {D : Precategory o′ ℓ′}
        {F G : Functor C D}
    → Dualises (F => G)
  Dualises-nat-trans .Dualises.fields   =
      argN (quote _=>_.η)
    ∷ argN (quote _=>_.is-natural)
    ∷ []
  Dualises-nat-trans .Dualises.dualiser = quote _=>_.op

open Dualises

cohere-dualise-into
  : Bool → ∀ {ℓ ℓ′} {S : Type ℓ′} → Name → (T : Type ℓ) → ⦃ Dualises T ⦄ → S → TC ⊤
cohere-dualise-into is-dual a T ⦃ du ⦄ tm = do
  `tm ← quoteTC tm
  clauses ← for (du .fields) λ where (arg ai prj) → do
    t ← if is-dual
      then (reduce (def prj [ argN (def (du .dualiser) [ argN `tm ]) ]))
      else (reduce (def prj [ argN `tm ]))
    pure $ clause [] [ arg ai (proj prj) ] t

  `T ← quoteTC T
  declareDef (argN a) `T
  defineFun a clauses

define-coherator-dualiser : Bool → Name → TC ⊤
define-coherator-dualiser is-dual nam = do
  (fs , dual) ← runSpeculative do
    ty ← inferType (def nam [ argN unknown ])
    (mv , _) ← new-meta′ (def (quote Dualises) [ argN ty ])
    getInstances mv >>= λ where
      (qn ∷ []) -> do
        fs ← normalise (def (quote Dualises.fields) [ argN qn ])
          >>= unquoteTC {A = List (Arg Name)}
        du ← normalise (def (quote Dualises.dualiser) [ argN qn ])
          >>= unquoteTC {A = Name}
        pure ((fs , du) , false)
      _ → typeError [ strErr "Failed to determine how to define a coherence map for"
                    , termErr (def nam [])
                    ]

  clauses ← for fs λ where (arg ai prj) → do
    pure $ if is-dual
      then (clause (("α" , argN unknown) ∷ [])
              [ argN (var 0) , arg ai (proj prj) ]
              (def prj [ argN (def dual [ argN (var 0 []) ]) ]))
      else (clause (("α" , argN unknown) ∷ [])
              [ argN (var 0) , arg ai (proj prj) ]
              (def prj [ argN (var 0 []) ]))

  defineFun nam clauses

define-coherence = define-coherator-dualiser false
define-dualiser  = define-coherator-dualiser true
cohere-into      = cohere-dualise-into false
dualise-into     = cohere-dualise-into true

nat-assoc-to    : f ⇒ g ⊗ h ⊗ i → f ⇒ (g ⊗ h) ⊗ i
nat-assoc-from  : f ⊗ g ⊗ h ⇒ i → (f ⊗ g) ⊗ h ⇒ i
op-compose-into : f ⇒ Functor.op (g ⊗ h) → f ⇒ Functor.op g ⊗ Functor.op h

unquoteDef nat-assoc-to nat-assoc-from op-compose-into = do
  define-coherence nat-assoc-to
  define-coherence nat-assoc-from
  define-coherence op-compose-into
