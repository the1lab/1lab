open import 1Lab.Path.IdentitySystem
open import 1Lab.Path
open import 1Lab.Type

open import Data.List.Base
open import Data.Dec.Base
open import Data.Id.Base
open import Data.Bool

module 1Lab.Reflection.Data.Argument where

data Visibility : Type where
  visible hidden instance' : Visibility

{-# BUILTIN HIDING   Visibility #-}
{-# BUILTIN VISIBLE  visible    #-}
{-# BUILTIN HIDDEN   hidden     #-}
{-# BUILTIN INSTANCE instance'  #-}

data Relevance : Type where
  relevant irrelevant : Relevance

{-# BUILTIN RELEVANCE  Relevance  #-}
{-# BUILTIN RELEVANT   relevant   #-}
{-# BUILTIN IRRELEVANT irrelevant #-}

data Quantity : Type where
  quantity-0 quantity-ω : Quantity

{-# BUILTIN QUANTITY   Quantity   #-}
{-# BUILTIN QUANTITY-0 quantity-0 #-}
{-# BUILTIN QUANTITY-ω quantity-ω #-}

instance
  Discrete-Visibility : Discrete Visibility
  Discrete-Visibility = Discreteᵢ→discrete λ where
    visible visible   → yes reflᵢ
    visible hidden    → no (λ ())
    visible instance' → no (λ ())

    hidden visible      → no (λ ())
    hidden hidden       → yes reflᵢ
    hidden instance'    → no (λ ())

    instance' visible   → no (λ ())
    instance' hidden    → no (λ ())
    instance' instance' → yes reflᵢ

  Discrete-Relevance : Discrete Relevance
  Discrete-Relevance = Discreteᵢ→discrete λ where
    relevant relevant   → yes reflᵢ
    relevant irrelevant → no (λ ())

    irrelevant relevant   → no (λ ())
    irrelevant irrelevant → yes reflᵢ

  Discrete-Quantity : Discrete Quantity
  Discrete-Quantity = Discreteᵢ→discrete λ where
    quantity-0 quantity-0 → yes reflᵢ
    quantity-0 quantity-ω → no (λ ())
    quantity-ω quantity-0 → no (λ ())
    quantity-ω quantity-ω → yes reflᵢ

record Modality : Type where
  constructor modality
  field
    r : Relevance
    q : Quantity

{-# BUILTIN MODALITY             Modality #-}
{-# BUILTIN MODALITY-CONSTRUCTOR modality #-}

pattern default-modality = modality relevant quantity-ω

record ArgInfo : Type where
  constructor arginfo
  field
    arg-vis : Visibility
    arg-modality : Modality

pattern default-ai = arginfo visible default-modality

record Arg {a} (A : Type a) : Type a where
  constructor arg
  field
    arg-info : ArgInfo
    unarg : A

{-# BUILTIN ARGINFO    ArgInfo  #-}
{-# BUILTIN ARGARGINFO arginfo #-}
{-# BUILTIN ARG        Arg      #-}
{-# BUILTIN ARGARG     arg      #-}

instance
  Discrete-Modality : Discrete Modality
  Discrete-Modality = Discrete-inj
    (λ (modality r q) → r , q)
    (λ p → ap₂ modality (ap fst p) (ap snd p))
    auto

  Discrete-ArgInfo : Discrete ArgInfo
  Discrete-ArgInfo = Discrete-inj
    (λ (arginfo r q) → r , q)
    (λ p → ap₂ arginfo (ap fst p) (ap snd p))
    auto

  Discrete-Arg : ∀ {ℓ} {A : Type ℓ} ⦃ _ : Discrete A ⦄ → Discrete (Arg A)
  Discrete-Arg = Discrete-inj
    (λ (arg r q) → r , q)
    (λ p → ap₂ arg (ap fst p) (ap snd p))
    auto

pattern _v∷_ t xs = arg (arginfo visible (modality relevant quantity-ω)) t ∷ xs
pattern _h∷_ t xs = arg (arginfo hidden (modality relevant quantity-ω)) t ∷ xs
pattern _hm∷_ t xs = arg (arginfo hidden (modality relevant _)) t ∷ xs
infixr 30 _v∷_ _h∷_ _hm∷_

argH0 argI argH argN : ∀ {ℓ} {A : Type ℓ} → A → Arg A
argH  = arg (arginfo hidden (modality relevant quantity-ω))
argH0 = arg (arginfo hidden (modality relevant quantity-0))
argI  = arg (arginfo instance' (modality relevant quantity-ω))
argN  = arg (arginfo visible (modality relevant quantity-ω))
