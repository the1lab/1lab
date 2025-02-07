open import 1Lab.Path.IdentitySystem
open import 1Lab.Path
open import 1Lab.Type

open import Data.List.Base
open import Data.Dec.Base
open import Data.Id.Base
open import Data.Bool

open import Meta.Traversable
open import Meta.Idiom

module Data.Reflection.Argument where

data Visibility : Type where
  visible hidden instance' : Visibility

data Relevance : Type where
  relevant irrelevant : Relevance

data Quantity : Type where
  quantity-0 quantity-ω : Quantity

record Modality : Type where
  constructor modality
  field
    r : Relevance
    q : Quantity


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

{-# BUILTIN HIDING               Visibility #-}
{-# BUILTIN VISIBLE              visible    #-}
{-# BUILTIN HIDDEN               hidden     #-}
{-# BUILTIN INSTANCE             instance'  #-}
{-# BUILTIN RELEVANCE            Relevance  #-}
{-# BUILTIN RELEVANT             relevant   #-}
{-# BUILTIN IRRELEVANT           irrelevant #-}
{-# BUILTIN QUANTITY             Quantity   #-}
{-# BUILTIN QUANTITY-0           quantity-0 #-}
{-# BUILTIN QUANTITY-ω           quantity-ω #-}
{-# BUILTIN MODALITY             Modality   #-}
{-# BUILTIN MODALITY-CONSTRUCTOR modality   #-}
{-# BUILTIN ARGINFO              ArgInfo    #-}
{-# BUILTIN ARGARGINFO           arginfo    #-}
{-# BUILTIN ARG                  Arg        #-}
{-# BUILTIN ARGARG               arg        #-}

pattern _v∷_ t xs = arg (arginfo visible (modality relevant quantity-ω)) t ∷ xs
pattern _h∷_ t xs = arg (arginfo hidden (modality relevant quantity-ω)) t ∷ xs
pattern _hm∷_ t xs = arg (arginfo hidden (modality relevant _)) t ∷ xs
infixr 20 _v∷_ _h∷_ _hm∷_

argH0 argI argH argN : ∀ {ℓ} {A : Type ℓ} → A → Arg A
argH  = arg (arginfo hidden (modality relevant quantity-ω))
argH0 = arg (arginfo hidden (modality relevant quantity-0))
argI  = arg (arginfo instance' (modality relevant quantity-ω))
argN  = arg (arginfo visible (modality relevant quantity-ω))

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

  Map-Arg : Map (eff Arg)
  Map-Arg .Map.map f (arg ai x) = arg ai (f x)

  Traversable-Arg : Traversable (eff Arg)
  Traversable-Arg .Traversable.traverse f (arg ai x) = arg ai <$> f x

record Has-visibility {ℓ} (A : Type ℓ) : Type ℓ where
  field set-visibility : Visibility → A → A

open Has-visibility ⦃ ... ⦄ public

instance
  Has-visibility-ArgInfo : Has-visibility ArgInfo
  Has-visibility-ArgInfo .set-visibility v (arginfo _ m) = arginfo v m

  Has-visibility-Arg : ∀ {ℓ} {A : Type ℓ} → Has-visibility (Arg A)
  Has-visibility-Arg .set-visibility v (arg (arginfo _ m) x) = arg (arginfo v m) x

  Has-visibility-Args : ∀ {ℓ} {A : Type ℓ} → Has-visibility (List (Arg A))
  Has-visibility-Args .set-visibility v l = set-visibility v <$> l

hide : ∀ {ℓ} {A : Type ℓ} → ⦃ Has-visibility A ⦄ → A → A
hide = set-visibility hidden

hide-if : ∀ {ℓ} {A : Type ℓ} → ⦃ Has-visibility A ⦄ → Bool → A → A
hide-if true a = hide a
hide-if false a = a
