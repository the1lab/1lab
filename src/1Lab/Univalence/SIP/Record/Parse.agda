open import 1Lab.Univalence.SIP.Record.Base
open import 1Lab.Univalence.SIP.Record.Prop
open import 1Lab.Univalence.SIP.Auto
open import 1Lab.Univalence.SIP
open import 1Lab.Reflection
open import 1Lab.Type.Sigma
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Type

open import Data.List

module 1Lab.Univalence.SIP.Record.Parse where

parseFields : Term → Term → Term → TC (List (InternalField × TypedTm))
parseFields _ _ (con (quote record:) _) = returnTC []
parseFields s h (con (quote _field[_by_]) (ℓ h∷ ℓ₁ h∷ ℓ₁' h∷ R h∷ ι h∷ fs v∷ ℓ₂ h∷ ℓ₂' h∷ S h∷ ι' h∷ sfieldTerm v∷ efieldTerm v∷ []))
  = do ℓ ← reduce ℓ
       struct-field ← findName sfieldTerm
       pres-field ← findName efieldTerm

       desc ← newMeta (def (quote Str-term) (ℓ v∷ ℓ₂' v∷ S v∷ []))
       tt ← makeAutoStr-term 100 desc

       let f : InternalField × TypedTm
           f = (structureField struct-field pres-field)
             , record { type = def (quote tm→⌜is-univalent⌝) (desc v∷ [])
                      ; term = def (quote tm→is-univalent') (desc v∷ [])
                      }
       rest <- parseFields s h fs
       returnTC (f ∷ rest)

parseFields strTerm homTerm (con (quote _axiom[_by_])
            (ℓ h∷ ℓ₁ h∷ ℓ₁' h∷ R h∷ ι h∷ fs v∷ ℓ₂ h∷ P h∷ fieldTerm v∷ is-prop v∷ []))
  = do struct-field ← findName fieldTerm
       let f : InternalField × TypedTm
           f = propertyField struct-field
             , record { type = def (quote PropHelperType)
                                  (strTerm v∷ homTerm v∷ fs v∷ P v∷ fieldTerm v∷ [])
                      ; term = def (quote derivePropHelper)
                                  (strTerm v∷ homTerm v∷ fs v∷ P v∷ fieldTerm v∷ is-prop v∷ [])
                      }
       rest <- parseFields strTerm homTerm fs
       returnTC (f ∷ rest)

parseFields _ _ tm = typeError (termErr tm ∷ strErr " ← This is not a field descriptor!" ∷ [])

parseSpec : Term → TC (Spec TypedTm)
parseSpec (con (quote record-desc) (ℓ h∷ ℓ₁ h∷ ℓ₁' h∷ strTerm v∷ homTerm v∷ fs v∷ [])) =
  do fs' ← parseFields strTerm homTerm fs
     returnTC λ { .Spec.structure → strTerm
                ; .Spec.homomorphism → homTerm
                ; .Spec.fields → fs'
                }

parseSpec tm = typeError (termErr tm ∷ strErr " ← This is not an AutoRecord!" ∷ [])
