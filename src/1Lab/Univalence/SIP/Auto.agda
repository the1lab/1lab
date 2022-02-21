open import 1Lab.Univalence.SIP
open import 1Lab.Reflection
open import 1Lab.Type.Sigma
open import 1Lab.Univalence
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Univalence.SIP.Auto where

open import Agda.Builtin.Reflection
  renaming ( bindTC to _>>=_
           ; catchTC to infixr 8 _<|>_
           )
  hiding (Type)

makeAutoStr-term : Nat → Term → TC ⊤
makeAutoStr-term zero t = typeError (strErr "autoDesc ran out of fuel" ∷ [])
makeAutoStr-term (suc n) t =
  tryPoint
    <|> tryBin (quote _s→_)
    <|> tryBin (quote _s×_)
    <|> useConst
  where
    tryPoint = do
      unify t (con (quote s∙) [])

    tryBin : Name → TC ⊤
    tryBin namen = do
      h1 ← newMeta unknown
      h2 ← newMeta unknown
      tt ← unify (con namen (h1 v∷ h2 v∷ [])) t
      tt ← makeAutoStr-term n h1
      makeAutoStr-term n h2

    useConst = do
      unify t (con (quote s-const) (unknown v∷ []))

macro
  auto-str-term : Term → TC ⊤
  auto-str-term = makeAutoStr-term 100
