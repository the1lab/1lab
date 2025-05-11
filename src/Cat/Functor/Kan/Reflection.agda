open import 1Lab.Reflection.Subst
open import 1Lab.Reflection

open import Cat.Functor.Naturality.Reflection
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.Kan.Unique
open import Cat.Functor.Naturality
open import Cat.Functor.Kan.Base
open import Cat.Functor.Compose
open import Cat.Functor.Base
open import Cat.Reasoning
open import Cat.Prelude

module Cat.Functor.Kan.Reflection where

module _
    {o ℓ o' ℓ' od ℓd}
    {C : Precategory o ℓ} {C' : Precategory o' ℓ'} {D : Precategory od ℓd}
    {p p' : Functor C C'} {F F' : Functor C D}
    {G G' : Functor C' D} {eps : G F∘ p => F} {eps' : G' F∘ p' => F'}
    where

  cohere-eps! : Term → TC ⊤
  cohere-eps! hole = do
    `D ← quoteTC D
    `G ← quoteTC G
    unify hole $ def₀ (quote Nat-path)
      ##ₙ vlam "c" (def₀ (quote _∙∙_∙∙_)
        ##ₙ (def₀ (quote idl) ##ₙ raise 1 `D ##ₙ unknown)
        ##ₙ (def₀ (quote elimr)
          ##ₙ raise 1 `D
          ##ₙ (def₀ (quote eliml)
            ##ₙ raise 1 `D
            ##ₙ (def₀ (quote Functor.F-id) ##ₙ raise 1 `G)))
        ##ₙ def₀ (quote trivial!))

  trivial-is-ran!
    : {@(tactic trivial-isoⁿ p p') p-iso : p ≅ⁿ p'}
    → {@(tactic trivial-isoⁿ F F') F-iso : F ≅ⁿ F'}
    → {@(tactic trivial-isoⁿ G G') G-iso : G ≅ⁿ G'}
    → {@(tactic cohere-eps!) q : Isoⁿ.to F-iso ∘nt eps ∘nt (Isoⁿ.from G-iso ◆ Isoⁿ.from p-iso) ≡ eps'}
    → is-ran p F G eps
    → is-ran p' F' G' eps'
  trivial-is-ran! {p-iso = p-iso} {F-iso} {G-iso} {q} =
    natural-isos→is-ran p-iso F-iso G-iso q

  trivial-ran-equiv!
    : {@(tactic trivial-isoⁿ p p') p-iso : p ≅ⁿ p'}
    → {@(tactic trivial-isoⁿ F F') F-iso : F ≅ⁿ F'}
    → {@(tactic trivial-isoⁿ G G') G-iso : G ≅ⁿ G'}
    → {@(tactic cohere-eps!) q : Isoⁿ.to F-iso ∘nt eps ∘nt (Isoⁿ.from G-iso ◆ Isoⁿ.from p-iso) ≡ eps'}
    → is-ran p F G eps
    ≃ is-ran p' F' G' eps'
  trivial-ran-equiv! {p-iso = p-iso} {F-iso} {G-iso} {q} =
    natural-isos→ran-equiv p-iso F-iso G-iso q

module _
    {o ℓ o' ℓ' od ℓd}
    {C : Precategory o ℓ} {C' : Precategory o' ℓ'} {D : Precategory od ℓd}
    {p p' : Functor C C'} {F F' : Functor C D}
    {G G' : Functor C' D} {eta : F => G F∘ p} {eta' : F' => G' F∘ p'}
    where

  cohere-eta! : Term → TC ⊤
  cohere-eta! hole = do
    `D ← quoteTC D
    `G' ← quoteTC G'
    unify hole $ def₀ (quote Nat-path)
      ##ₙ vlam "c" (def₀ (quote _∙∙_∙∙_)
        ##ₙ (def₀ (quote eliml)
          ##ₙ raise 1 `D
          ##ₙ (def₀ (quote eliml)
            ##ₙ raise 1 `D
            ##ₙ (def₀ (quote Functor.F-id) ##ₙ raise 1 `G')))
        ##ₙ def₀ (quote trivial!)
        ##ₙ (def₀ (quote idr) ##ₙ raise 1 `D ##ₙ unknown))

  trivial-is-lan!
    : {@(tactic trivial-isoⁿ p p') p-iso : p ≅ⁿ p'}
    → {@(tactic trivial-isoⁿ F F') F-iso : F ≅ⁿ F'}
    → {@(tactic trivial-isoⁿ G G') G-iso : G ≅ⁿ G'}
    → {@(tactic cohere-eta!) q : (Isoⁿ.to G-iso ◆ Isoⁿ.to p-iso) ∘nt eta ∘nt Isoⁿ.from F-iso ≡ eta'}
    → is-lan p F G eta
    → is-lan p' F' G' eta'
  trivial-is-lan! {p-iso = p-iso} {F-iso} {G-iso} {q} =
    natural-isos→is-lan p-iso F-iso G-iso q

  trivial-lan-equiv!
    : {@(tactic trivial-isoⁿ p p') p-iso : p ≅ⁿ p'}
    → {@(tactic trivial-isoⁿ F F') F-iso : F ≅ⁿ F'}
    → {@(tactic trivial-isoⁿ G G') G-iso : G ≅ⁿ G'}
    → {@(tactic cohere-eta!) q : (Isoⁿ.to G-iso ◆ Isoⁿ.to p-iso) ∘nt eta ∘nt Isoⁿ.from F-iso ≡ eta'}
    → is-lan p F G eta
    ≃ is-lan p' F' G' eta'
  trivial-lan-equiv! {p-iso = p-iso} {F-iso} {G-iso} {q} =
    natural-isos→lan-equiv p-iso F-iso G-iso q

module _
    {o ℓ od ℓd}
    {C : Precategory o ℓ} {D : Precategory od ℓd}
    {F F' : Functor C D}
    {G G' : Functor ⊤Cat D} {eps : G F∘ !F => F} {eps' : G' F∘ !F => F'}
    where

  trivial-is-limit!
    : {@(tactic trivial-isoⁿ F F') F-iso : F ≅ⁿ F'}
    → {@(tactic trivial-isoⁿ G G') G-iso : G ≅ⁿ G'}
    → {@(tactic cohere-eps! {eps = eps} {eps' = eps'}) q : Isoⁿ.to F-iso ∘nt eps ∘nt (Isoⁿ.from G-iso ◆ Isoⁿ.from idni) ≡ eps'}
    → is-ran !F F G eps
    → is-ran !F F' G' eps'
  trivial-is-limit! {F-iso = F-iso} {G-iso} {q} =
    natural-isos→is-ran idni F-iso G-iso q

  trivial-limit-equiv!
    : {@(tactic trivial-isoⁿ F F') F-iso : F ≅ⁿ F'}
    → {@(tactic trivial-isoⁿ G G') G-iso : G ≅ⁿ G'}
    → {@(tactic cohere-eps! {eps = eps} {eps' = eps'}) q : Isoⁿ.to F-iso ∘nt eps ∘nt (Isoⁿ.from G-iso ◆ Isoⁿ.from idni) ≡ eps'}
    → is-ran !F F G eps
    ≃ is-ran !F F' G' eps'
  trivial-limit-equiv! {F-iso = F-iso} {G-iso} {q} =
    natural-isos→ran-equiv idni F-iso G-iso q

module _
    {o ℓ od ℓd}
    {C : Precategory o ℓ} {D : Precategory od ℓd}
    {F F' : Functor C D}
    {G G' : Functor ⊤Cat D} {eta : F => G F∘ !F} {eta' : F' => G' F∘ !F}
    where

  trivial-is-colimit!
    : {@(tactic trivial-isoⁿ F F') F-iso : F ≅ⁿ F'}
    → {@(tactic trivial-isoⁿ G G') G-iso : G ≅ⁿ G'}
    → {@(tactic cohere-eta! {eta = eta} {eta' = eta'}) q : (Isoⁿ.to G-iso ◆ Isoⁿ.to idni) ∘nt eta ∘nt Isoⁿ.from F-iso ≡ eta'}
    → is-lan !F F G eta
    → is-lan !F F' G' eta'
  trivial-is-colimit! {F-iso = F-iso} {G-iso} {q} =
    natural-isos→is-lan idni F-iso G-iso q

  trivial-colimit-equiv!
    : {@(tactic trivial-isoⁿ F F') F-iso : F ≅ⁿ F'}
    → {@(tactic trivial-isoⁿ G G') G-iso : G ≅ⁿ G'}
    → {@(tactic cohere-eta! {eta = eta} {eta' = eta'}) q : (Isoⁿ.to G-iso ◆ Isoⁿ.to idni) ∘nt eta ∘nt Isoⁿ.from F-iso ≡ eta'}
    → is-lan !F F G eta
    ≃ is-lan !F F' G' eta'
  trivial-colimit-equiv! {F-iso = F-iso} {G-iso} {q} =
    natural-isos→lan-equiv idni F-iso G-iso q

-- Tests

module _
    {o ℓ o' ℓ' od ℓd}
    {C : Precategory o ℓ} {C' : Precategory o' ℓ'} {D : Precategory od ℓd}
    {p : Functor C C'} {F : Functor C D}
    {G : Functor C' D} {eta : F => G F∘ p} {eps : G F∘ p => F}
    where private

  _ : is-ran p F G eps → is-ran p F G eps
  _ = trivial-is-ran!

  _ : is-lan p F G eta → is-lan p F G eta
  _ = trivial-is-lan!
