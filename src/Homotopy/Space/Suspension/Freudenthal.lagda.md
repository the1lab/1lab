<!--
```agda
open import 1Lab.Path.Reasoning
open import 1Lab.Prelude hiding (_*_)

open import Homotopy.Space.Suspension.Properties
open import Homotopy.Space.Suspension
open import Homotopy.Connectedness
open import Homotopy.Truncation
open import Homotopy.Loopspace
open import Homotopy.Wedge
```
-->

```agda
module Homotopy.Space.Suspension.Freudenthal
```

<!--
```agda
  {ℓ} {A∙@(A , a₀) : Type∙ ℓ} (n : Nat)
  (conn : is-n-connected A (2 + n))
  (let 2n = (suc n) + (suc n))
  where
```
-->

# Freudenthal suspension theorem

```agda
private
  ∥_∥₂ₙ : ∀ {ℓ} → Type ℓ → Type ℓ
  ∥ A ∥₂ₙ = n-Tr A 2n

  module wc (p : north ≡ north) =
    Wedge {A∙ = A∙} {A∙} {λ a b → suspend A∙ b ≡ p → ∥ fibre (suspend (A , a)) p ∥₂ₙ}
      n n conn conn (λ x y → hlevel 2n)
      (λ a p → inc (a , ∙-invr (merid a) ∙ sym (∙-invr (merid a₀)) ∙ p))
      (λ a p → inc (a , p))
      (funext λ x → ap (λ e → n-Tr.inc {n = 2n} (a₀ , e))
        (∙-cancell (sym (∙-invr (merid a₀))) x))

  fwd : ∀ p a → ∥ fibre (suspend A∙) p ∥₂ₙ → ∥ fibre (suspend (A , a)) p ∥₂ₙ
  fwd = elim! wc.elim

  abstract
    fwd-is-equiv : ∀ p a → is-equiv (fwd p a)
    fwd-is-equiv p a .is-eqv =
      let
        eqv = relative-n-type-const
          (λ a → ∀ t → is-contr (fibre (fwd p a) t))
          (λ _ → a₀) (suc n) (point-is-n-connected a₀ n conn)
          (λ x → hlevel (suc n))

        it : ∀ a (t : n-Tr (fibre (suspend A∙) p) 2n)
          → is-contr (fibre (fwd p a₀) t)
        it = elim! λ _ x q →
          subst (λ e → is-contr (fibre e (inc (x , q)))) {x = id} {y = _}
            (funext (n-Tr-elim! _ λ (x , q) → sym (happly (wc.β₂ p x) q)))
            Singleton'-is-contr
      in Equiv.from (_ , eqv) it a

  interpolate : (a : A) → PathP (λ i → A → north ≡ merid a i) (suspend (A , a)) merid
  interpolate a i x j = ∙-filler (merid x) (sym (merid a)) (~ i) j

  code : (y : Susp A) → north ≡ y → Type ℓ
  code north p = ∥ fibre (suspend A∙) p ∥₂ₙ
  code south p = ∥ fibre merid p        ∥₂ₙ
  code (merid p i) q = Glue ∥ fibre (interpolate p i) q ∥₂ₙ λ where
    (i = i0) → _ , fwd q p , fwd-is-equiv q p
    (i = i1) → _ , id≃

  encode : (y : Susp A) (p : north ≡ y) → code y p
  encode y = J code (inc (a₀ , ∙-invr (merid a₀)))

  encode-paths : ∀ p c → encode south p ≡ c
  encode-paths p = elim! λ a → J (λ p r → encode south p ≡ inc (a , r))
    let
      gp i = n-Tr (fibre (interpolate a i) (λ j → merid a (i ∧ j))) 2n

      rem₁ =
        wc.elim refl a a₀ (∙-invr (merid a₀))                                    ≡⟨ happly (wc.β₁ refl a) (∙-invr (merid a₀)) ⟩
        inc (a , ∙-invr (merid a) ∙ sym (∙-invr (merid a₀)) ∙ ∙-invr (merid a₀)) ≡⟨ ap (λ e → n-Tr.inc (a , e)) (∙-elimr (∙-invl (∙-invr (merid a₀)))) ⟩
        inc (a , ∙-invr (merid a))                                               ∎

      rem₂ =
        transport gp (fwd refl a (inc (a₀ , ∙-invr (merid a₀)))) ≡⟨ ap (transport gp) rem₁ ⟩
        transport gp (inc (a , ∙-invr (merid a)))                ≡⟨ from-pathp {A = λ i → gp i} (λ i → inc (a , λ j k → ∙-invr-filler (merid a) j k (~ i))) ⟩
        inc (a , refl)                                           ∎
    in rem₂

  merid-is-n-connected : is-n-connected-map merid 2n
  merid-is-n-connected x = n-connected.from (n + suc n) record
    { centre = encode south x
    ; paths  = encode-paths x
    }

suspend-is-n-connected : is-n-connected-map (suspend A∙) 2n
suspend-is-n-connected = transport
  (λ i → is-n-connected-map (λ z → interpolate a₀ (~ i) z) 2n)
  merid-is-n-connected

freudenthal-equivalence
  : n-Tr∙ A∙ 2n ≃∙ n-Tr∙ (Ωⁿ 1 (Σ¹ A∙)) 2n
freudenthal-equivalence .fst .fst = _
freudenthal-equivalence .fst .snd = is-n-connected-map→is-equiv-tr
  _ _ suspend-is-n-connected
freudenthal-equivalence .snd = ap n-Tr.inc (∙-invr (merid a₀))
```
