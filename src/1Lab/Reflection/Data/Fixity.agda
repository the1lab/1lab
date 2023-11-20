open import 1Lab.Path
open import 1Lab.Type

open import Data.Dec.Base
open import Data.Id.Base

open import Prim.Data.Float

module 1Lab.Reflection.Data.Fixity where

data Associativity : Type where
  left-assoc  : Associativity
  right-assoc : Associativity
  non-assoc   : Associativity

data Precedence : Type where
  related   : Float → Precedence
  unrelated : Precedence

data Fixity : Type where
  fixity : Associativity → Precedence → Fixity

{-# BUILTIN ASSOC      Associativity #-}
{-# BUILTIN ASSOCLEFT  left-assoc    #-}
{-# BUILTIN ASSOCRIGHT right-assoc   #-}
{-# BUILTIN ASSOCNON   non-assoc     #-}

{-# BUILTIN PRECEDENCE    Precedence #-}
{-# BUILTIN PRECRELATED   related    #-}
{-# BUILTIN PRECUNRELATED unrelated  #-}

{-# BUILTIN FIXITY       Fixity #-}
{-# BUILTIN FIXITYFIXITY fixity #-}

instance
  Discrete-Associativity : Discrete Associativity
  Discrete-Associativity = Discreteᵢ→discrete λ where
    left-assoc  left-assoc  → yes reflᵢ
    left-assoc  right-assoc → no (λ ())
    left-assoc  non-assoc   → no (λ ())

    right-assoc left-assoc  → no (λ ())
    right-assoc right-assoc → yes reflᵢ
    right-assoc non-assoc   → no (λ ())

    non-assoc   left-assoc  → no (λ ())
    non-assoc   right-assoc → no (λ ())
    non-assoc   non-assoc   → yes reflᵢ

  Discrete-Precedence : Discrete Precedence
  Discrete-Precedence = Discreteᵢ→discrete λ where
    (related x) (related y) → case x ≡ᵢ? y of λ where
      (yes reflᵢ) → yes reflᵢ
      (no ¬a)     → no λ { reflᵢ → ¬a reflᵢ }
    (related x) unrelated → no (λ ())
    unrelated (related x) → no (λ ())
    unrelated unrelated   → yes reflᵢ

  Discrete-Fixity : Discrete Fixity
  Discrete-Fixity = Discreteᵢ→discrete λ where
    (fixity a p) (fixity a' p') → case (a ≡ᵢ? a' , p ≡ᵢ? p') of λ where
      (yes reflᵢ , yes reflᵢ) → yes reflᵢ
      (yes as , no ¬ps)       → no λ { reflᵢ → ¬ps reflᵢ }
      (no ¬as , _)            → no λ { reflᵢ → ¬as reflᵢ }
