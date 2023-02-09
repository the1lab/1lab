---
description: We establish that right adjoints preserve limits.
---
```agda
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Functor
open import Cat.Diagram.Terminal
open import Cat.Diagram.Initial
open import Cat.Functor.Adjoint
open import Cat.Functor.Adjoint.Kan
open import Cat.Diagram.Duals
open import Cat.Functor.Base
open import Cat.Prelude

open import Data.Bool

module Cat.Functor.Adjoint.Continuous where
```

<!--
```agda
module _
    {o o′ ℓ ℓ′} {C : Precategory o ℓ} {D : Precategory o′ ℓ′}
    {L : Functor C D} {R : Functor D C}
    (L⊣R : L ⊣ R)
  where
  private
    module L = Functor L
    module R = Functor R
    import Cat.Reasoning C as C
    import Cat.Reasoning D as D
    module adj = _⊣_ L⊣R
```
-->

# Continuity of adjoints

We prove that every functor $R : \cD \to \cC$ admitting a left
adjoint $L \dashv R$ preserves every limit which exists in $\cD$. We
then instantiate this theorem to the "canonical" shapes of limit:
[terminal objects], [products], [pullbacks] and [equalisers].

[terminal objects]: Cat.Diagram.Terminal.html
[products]: Cat.Diagram.Product.html
[pullbacks]: Cat.Diagram.Pullback.html
[equalisers]: Cat.Diagram.Equaliser.html

This follows directly from the fact that [adjoints preserve kan
extensions].

[adjoints preserve kan extensions]: Cat.Functor.Adjoint.Kan.html


```agda
  module _ {od ℓd} {J : Precategory od ℓd} {F : Functor J D} where

  right-adjoint-is-continuous
    : ∀ {os ℓs} → is-continuous {oshape = os} {hshape = ℓs} R
  right-adjoint-is-continuous lim =
    right-adjoint→right-extension lim L⊣R

  left-adjoint-is-cocontinuous
    : ∀ {os ℓs} → is-cocontinuous {oshape = os} {hshape = ℓs} L
  left-adjoint-is-cocontinuous colim =
    left-adjoint→left-extension colim L⊣R
```

-- ## Concrete limits

-- For establishing the preservation of "concrete limits", in addition to
-- the preexisting conversion functions (`Lim→Prod`{.Agda},
-- `Limit→Pullback`{.Agda}, `Limit→Equaliser`{.Agda}, etc.), we must
-- establish results analogous to `canonical-functors`{.Agda}: Functors out
-- of shape categories are entirely determined by the "introduction forms"
-- `cospan→cospan-diagram`{.Agda} and `par-arrows→par-diagram`{.Agda}.

-- ```agda
--   open import Cat.Instances.Shape.Parallel
--   open import Cat.Instances.Shape.Cospan
--   open import Cat.Diagram.Limit.Equaliser
--   open import Cat.Diagram.Limit.Pullback
--   open import Cat.Diagram.Limit.Product
--   open import Cat.Diagram.Equaliser
--   open import Cat.Diagram.Pullback
--   open import Cat.Diagram.Product

--   right-adjoint→product
--     : ∀ {A B} → Product D A B → Product C (R.₀ A) (R.₀ B)
--   right-adjoint→product {A = A} {B} prod =
--     Lim→Prod C (fixup (right-adjoint-limit (Prod→Lim D prod)))
--     where
--       fixup : Limit (R F∘ 2-object-diagram D {iss = Bool-is-set} A B)
--             → Limit (2-object-diagram C {iss = Bool-is-set} (R.₀ A) (R.₀ B))
--       fixup = subst Limit (canonical-functors _ _)

--   right-adjoint→pullback
--     : ∀ {A B c} {f : D.Hom A c} {g : D.Hom B c}
--     → Pullback D f g → Pullback C (R.₁ f) (R.₁ g)
--   right-adjoint→pullback {f = f} {g} pb =
--     Limit→Pullback C {x = lzero} {y = lzero}
--       (right-adjoint-limit (Pullback→Limit D pb))

--   right-adjoint→equaliser
--     : ∀ {A B} {f g : D.Hom A B}
--     → Equaliser D f g → Equaliser C (R.₁ f) (R.₁ g)
--   right-adjoint→equaliser {f = f} {g} eq =
--     Limit→Equaliser C (right-adjoint-limit
--       (Equaliser→Limit D {F = par-arrows→par-diagram f g} eq))

--   right-adjoint→terminal
--     : ∀ {X} → is-terminal D X → is-terminal C (R.₀ X)
--   right-adjoint→terminal term x = contr fin uniq where
--     fin = L-adjunct L⊣R (term (L.₀ x) .centre)
--     uniq : ∀ x → fin ≡ x
--     uniq x = ap fst $ is-contr→is-prop (R-adjunct-is-equiv L⊣R .is-eqv _)
--       (_ , equiv→counit (R-adjunct-is-equiv L⊣R) _)
--       (x , is-contr→is-prop (term _) _ _)

--   right-adjoint→lex : is-lex R
--   right-adjoint→lex .is-lex.pres-⊤ = right-adjoint→terminal
--   right-adjoint→lex .is-lex.pres-pullback {f = f} {g = g} pb =
--     right-adjoint→pullback (record { p₁ = _ ; p₂ = _ ; has-is-pb = pb }) .Pullback.has-is-pb
-- ```

-- <!--
-- ```agda
-- module _
--     {o o′ ℓ ℓ′} {C : Precategory o ℓ} {D : Precategory o′ ℓ′}
--     {L : Functor C D} {R : Functor D C}
--     (L⊣R : L ⊣ R)
--   where

--   private
--     adj′ : Functor.op R ⊣ Functor.op L
--     adj′ = opposite-adjunction L⊣R

--   module _ {od ℓd} {J : Precategory od ℓd} {F : Functor J C} where
--     left-adjoint-colimit : Colimit F → Colimit (L F∘ F)
--     left-adjoint-colimit colim = colim′′ where
--       lim : Limit (Functor.op F)
--       lim = Colimit→Co-limit _ colim

--       lim′ : Limit (Functor.op L F∘ Functor.op F)
--       lim′ = right-adjoint-limit adj′ lim

--       colim′ : Colimit (Functor.op (Functor.op L F∘ Functor.op F))
--       colim′ = Co-limit→Colimit _ (subst Limit (sym F^op^op≡F) lim′)

--       colim′′ : Colimit (L F∘ F)
--       colim′′ = subst Colimit (Functor-path (λ x → refl) λ x → refl) colim′

-- ```

-- TODO [Amy 2022-04-05]
-- cocontinuity
-- -->
