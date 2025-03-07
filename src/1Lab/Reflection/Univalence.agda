open import 1Lab.Reflection
open import 1Lab.Univalence
open import 1Lab.Type

open import Prim.Extension
open import Prim.HCompU
open import Prim.Kan

import 1Lab.Univalence as U

module 1Lab.Reflection.Univalence where

name-of-glue : Name
unquoteDef name-of-glue = do
  nm ← resetting do
    def nm _ ← reduce (def (quote Glue) (unknown v∷ unknown v∷ []))
      where anything → typeError ("insane: Glue did not reduce to a defined type?\n" ∷ termErr anything ∷ [])
    pure nm

  define-function name-of-glue (clause [] [] (lit (name nm)) ∷ [])

macro
  -- Simple helper macro to shadow the 'unglue' function with something
  -- that can actually infer the φ argument.

  unglue : Term → Term → TC ⊤
  unglue x goal = do
    let
      fail : Term → TC ⊤
      fail ty = typeError
        [ "unglue: the argument " , termErr x , " does not have a Glue type. instead, it is\n"
        , "  " , termErr ty
        ]

    ty ← wait-for-type =<< reduce =<< infer-type x
    case ty of λ where
      (def (quote primHComp) (ℓ h∷ _ h∷ φ h∷ s v∷ b v∷ [])) → unify goal
        (def (quote prim^unglueU)
          (unknown h∷ φ h∷ s h∷ def (quote inS) (b v∷ []) h∷ x v∷ []))

      ty@(def a (_ h∷ _ h∷ _ v∷ φ h∷ _)) → case a ≡? name-of-glue of λ where
        (yes _) → do
          wait-for-type φ
          unify goal (def (quote U.unattach) (φ v∷ x v∷ []))
        (no _) → fail ty
      ty → fail ty

{-# DISPLAY unattach _ x = unglue x #-}
