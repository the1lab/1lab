open import 1Lab.Path.IdentitySystem
open import 1Lab.Path
open import 1Lab.Type

open import Data.Bool.Base
open import Data.List.Base
open import Data.Dec.Base
open import Data.Id.Base

open import Meta.Traversable
open import Meta.Idiom

module Data.Reflection.Argument where

data Visibility : Type where
  visible hidden instance' : Visibility

record ArgInfo : Type where
  constructor arginfo
  field
    arg-vis : Visibility

pattern default-ai = arginfo visible

record Arg {a} (A : Type a) : Type a where
  constructor arg
  field
    arg-info : ArgInfo
    unarg : A

{-# BUILTIN HIDING               Visibility #-}
{-# BUILTIN VISIBLE              visible    #-}
{-# BUILTIN HIDDEN               hidden     #-}
{-# BUILTIN INSTANCE             instance'  #-}
{-# BUILTIN ARGINFO              ArgInfo    #-}
{-# BUILTIN ARGARGINFO           arginfo    #-}
{-# BUILTIN ARG                  Arg        #-}
{-# BUILTIN ARGARG               arg        #-}

pattern _v∷_ t xs = arg (arginfo visible) t ∷ xs
pattern _h∷_ t xs = arg (arginfo hidden) t ∷ xs
pattern _i∷_ t xs = arg (arginfo instance') t ∷ xs
infixr 20 _v∷_ _h∷_ _i∷_

argI argH argN : ∀ {ℓ} {A : Type ℓ} → A → Arg A
argH  = arg (arginfo hidden)
argI  = arg (arginfo instance')
argN  = arg (arginfo visible)

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

  Discrete-ArgInfo : Discrete ArgInfo
  Discrete-ArgInfo = Discrete-inj (λ (arginfo r) → r) (λ p → ap arginfo p) auto

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
  Has-visibility-ArgInfo .set-visibility v (arginfo _) = arginfo v

  Has-visibility-Arg : ∀ {ℓ} {A : Type ℓ} → Has-visibility (Arg A)
  Has-visibility-Arg .set-visibility v (arg (arginfo _) x) = arg (arginfo v) x

  Has-visibility-Args : ∀ {ℓ} {A : Type ℓ} → Has-visibility (List (Arg A))
  Has-visibility-Args .set-visibility v l = set-visibility v <$> l

hide : ∀ {ℓ} {A : Type ℓ} → ⦃ Has-visibility A ⦄ → A → A
hide = set-visibility hidden

hide-if : ∀ {ℓ} {A : Type ℓ} → ⦃ Has-visibility A ⦄ → Bool → A → A
hide-if true a = hide a
hide-if false a = a
