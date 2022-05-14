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

We prove that every functor $R : \ca{D} \to \ca{C}$ admitting a left
adjoint $L \dashv R$ preserves every limit which exists in $\ca{D}$. We
then instantiate this theorem to the "canonical" shapes of limit:
[terminal objects], [products], [pullbacks] and [equalisers].

[terminal objects]: Cat.Diagram.Terminal.html
[products]: Cat.Diagram.Product.html
[pullbacks]: Cat.Diagram.Pullbacks.html
[equalisers]: Cat.Diagram.Equaliser.html

```agda
  module _ {od ℓd} {J : Precategory od ℓd} {F : Functor J D} where
```

<!--
```agda
    private module F = Functor F
    open Cone-hom
    open Terminal hiding (! ; !-unique)
    open Cone
```
-->

## Passing cones along

The first thing we prove is that, given a cone over a diagram $F$ in
$\ca{D}$, we can get a cone in $\ca{C}$ over $R \circ F$, by passing
both the apex and the morphisms "over" using $R$. In reality, this is
just the canonically-defined action of $R$ on cones over $F$:

```agda
    cone-right-adjoint : Cone F → Cone (R F∘ F)
    cone-right-adjoint = F-map-cone R
```

Conversely, if we have a cone over $R \circ F$, we can turn that into a
cone for $F$. In this direction, we use $L$ on the apex, but we must
additionally use the `adjunction counit`{.Agda ident=adj.counit.ε} to
"adjust" the cone maps (that's `ψ`{.Agda}).

```agda
    right-adjoint-cone : Cone (R F∘ F) → Cone F
    right-adjoint-cone K .apex     = L.₀ (K .apex)
    right-adjoint-cone K .ψ x      = adj.counit.ε _ D.∘ L.₁ (K .ψ x)
    right-adjoint-cone K .commutes {x} {y} f =
      F.₁ f D.∘ adj.counit.ε _ D.∘ L.₁ (K .ψ x)                    ≡⟨ D.extendl (sym (adj.counit.is-natural _ _ _)) ⟩
      adj.counit.ε (F.₀ y) D.∘ L.₁ (R.₁ (F.₁ f)) D.∘ L.₁ (K .ψ x)  ≡˘⟨ ap (λ e → adj.counit.ε _ D.∘ e) (L.F-∘ _ _) ⟩
      adj.counit.ε (F.₀ y) D.∘ L.₁ (R.₁ (F.₁ f) C.∘ K .ψ x)        ≡⟨ ap (λ e → adj.counit.ε _ D.∘ L.₁ e) (K .commutes f) ⟩
      adj.counit.ε _ D.∘ L.₁ _                                     ∎
```

The key fact is that we can also pass _homomorphisms_ along, both ways!

```agda
    cone-hom-right-adjoint
      : {K : Cone (R F∘ F)} {K′ : Cone F}
      → Cone-hom F (right-adjoint-cone K) K′
      → Cone-hom (R F∘ F) K (cone-right-adjoint K′)
    cone-hom-right-adjoint map .hom = R.₁ (map .hom) C.∘ adj.unit.η _
    cone-hom-right-adjoint {K = K} {K′ = K′} map .commutes o =
      R.₁ (K′ .ψ o) C.∘ R.₁ (map .hom) C.∘ adj.unit.η _                 ≡⟨ C.pulll (sym (R.F-∘ _ _)) ⟩
      R.₁ (K′ .ψ o D.∘ map .hom) C.∘ adj.unit.η _                       ≡⟨ ap (λ e → R.₁ e C.∘ _) (map .commutes _) ⟩
      R.₁ (adj.counit.ε _ D.∘ L.₁ (Cone.ψ K o)) C.∘ adj.unit.η _        ≡⟨ C.pushl (R.F-∘ _ _) ⟩
      R.₁ (adj.counit.ε _) C.∘ R.₁ (L.₁ (Cone.ψ K o)) C.∘ adj.unit.η _  ≡˘⟨ C.pullr (adj.unit.is-natural _ _ _) ⟩
      (R.F₁ (adj.counit.ε _) C.∘ adj.unit.η _) C.∘ Cone.ψ K o           ≡⟨ ap (λ e → e C.∘ Cone.ψ K _) adj.zag ⟩
      C.id C.∘ Cone.ψ K o                                               ≡⟨ C.idl _ ⟩
      Cone.ψ K o                                                        ∎

    right-adjoint-cone-hom
      : {K : Cone (R F∘ F)} {K′ : Cone F}
      → Cone-hom (R F∘ F) K (cone-right-adjoint K′)
      → Cone-hom F (right-adjoint-cone K) K′
    right-adjoint-cone-hom map .hom = adj.counit.ε _ D.∘ L.₁ (map .hom)
    right-adjoint-cone-hom {K = K} {K′ = K′} map .commutes o =
      K′ .ψ o D.∘ adj.counit.ε _ D.∘ L.₁ (map .hom)               ≡⟨ D.extendl (sym (adj.counit.is-natural _ _ _)) ⟩
      adj.counit.ε _ D.∘ (L.₁ (R.₁ (K′ .ψ o)) D.∘ L.₁ (map .hom)) ≡⟨ ap (λ e → _ D.∘ e) (sym (L.F-∘ _ _)) ⟩
      adj.counit.ε _ D.∘ (L.₁ (R.₁ (K′ .ψ o) C.∘ map .hom))       ≡⟨ ap (λ e → _ D.∘ L.₁ e) (map .commutes _) ⟩
      adj.counit.ε _ D.∘ L.₁ (K .ψ o)                             ∎
```

Hence, if we have a limit for $F$, the two lemmas above (in the "towards
right adjoint" direction) already get us 66% of the way to having a
limit for $R \circ F$. The missing bit is a very short calculation:

```
    right-adjoint-limit : Limit F → Limit (R F∘ F)
    right-adjoint-limit lim .top = cone-right-adjoint (lim .top)
    right-adjoint-limit lim .has⊤ cone = contr ! !-unique where
      pre! = lim .has⊤ _ .centre
      ! = cone-hom-right-adjoint pre!

      !-unique : ∀ x → ! ≡ x
      !-unique x = Cone-hom-path _ (
        R.₁ (pre! .hom) C.∘ adj.unit.η _                             ≡⟨ ap (λ e → R.₁ e C.∘ _) (ap hom (lim .has⊤ _ .paths (right-adjoint-cone-hom x))) ⟩
        R.₁ (adj.counit.ε _ D.∘ L.₁ (x .hom)) C.∘ adj.unit.η _       ≡˘⟨ C.pulll (sym (R.F-∘ _ _)) ⟩
        R.₁ (adj.counit.ε _) C.∘ R.₁ (L.₁ (x .hom)) C.∘ adj.unit.η _ ≡˘⟨ ap (R.₁ _ C.∘_) (adj.unit.is-natural _ _ _) ⟩
        R.₁ (adj.counit.ε _) C.∘ adj.unit.η _ C.∘ x .hom             ≡⟨ C.cancell adj.zag ⟩
        x .hom                                                       ∎)
```

We then have the promised theorem: right adjoints preserve limits.

```agda
  right-adjoint-is-continuous
    : ∀ {os ℓs} → is-continuous {oshape = os} {hshape = ℓs} R
  right-adjoint-is-continuous L x = Terminal.has⊤ (right-adjoint-limit (record { top = L ; has⊤ = x }))
```

## Concrete limits

For establishing the preservation of "concrete limits", in addition to
the preexisting conversion functions (`Lim→Prod`{.Agda},
`Limit→Pullback`{.Agda}, `Limit→Equaliser`{.Agda}, etc.), we must
establish results analogous to `canonical-functors`{.Agda}: Functors out
of shape categories are entirely determined by the "introduction forms"
`cospan→cospan-diagram`{.Agda} and `par-arrows→par-diagram`{.Agda}.

```agda
  open import Cat.Instances.Shape.Parallel
  open import Cat.Instances.Shape.Cospan
  open import Cat.Diagram.Limit.Equaliser
  open import Cat.Diagram.Limit.Pullback
  open import Cat.Diagram.Limit.Product
  open import Cat.Diagram.Equaliser
  open import Cat.Diagram.Pullback
  open import Cat.Diagram.Product

  right-adjoint→product
    : ∀ {A B} → Product D A B → Product C (R.₀ A) (R.₀ B)
  right-adjoint→product {A = A} {B} prod =
    Lim→Prod C (fixup (right-adjoint-limit (Prod→Lim D prod)))
    where
      fixup : Limit (R F∘ 2-object-diagram D {iss = Bool-is-set} A B)
            → Limit (2-object-diagram C {iss = Bool-is-set} (R.₀ A) (R.₀ B))
      fixup = subst Limit (canonical-functors _ _)

  right-adjoint→pullback
    : ∀ {A B c} {f : D.Hom A c} {g : D.Hom B c}
    → Pullback D f g → Pullback C (R.₁ f) (R.₁ g)
  right-adjoint→pullback {f = f} {g} pb =
    Limit→Pullback C {x = lzero} {y = lzero}
      (right-adjoint-limit (Pullback→Limit D pb))

  right-adjoint→equaliser
    : ∀ {A B} {f g : D.Hom A B}
    → Equaliser D f g → Equaliser C (R.₁ f) (R.₁ g)
  right-adjoint→equaliser {f = f} {g} eq =
    Limit→Equaliser C (right-adjoint-limit
      (Equaliser→Limit D {F = par-arrows→par-diagram f g} eq))

  right-adjoint→terminal
    : ∀ {X} → is-terminal D X → is-terminal C (R.₀ X)
  right-adjoint→terminal term x = contr fin uniq where
    fin = L-adjunct L⊣R (term (L.₀ x) .centre)
    uniq : ∀ x → fin ≡ x
    uniq x = ap fst $ is-contr→is-prop (R-adjunct-is-equiv L⊣R .is-eqv _)
      (_ , equiv→section (R-adjunct-is-equiv L⊣R) _)
      (x , is-contr→is-prop (term _) _ _)

  right-adjoint→lex : is-lex R
  right-adjoint→lex .is-lex.pres-⊤ = right-adjoint→terminal
  right-adjoint→lex .is-lex.pres-pullback {f = f} {g = g} pb =
    right-adjoint→pullback (record { p₁ = _ ; p₂ = _ ; has-is-pb = pb }) .Pullback.has-is-pb
```

<!--
```agda
module _
    {o o′ ℓ ℓ′} {C : Precategory o ℓ} {D : Precategory o′ ℓ′}
    {L : Functor C D} {R : Functor D C}
    (L⊣R : L ⊣ R)
  where

  private
    adj′ : Functor.op R ⊣ Functor.op L
    adj′ = opposite-adjunction L⊣R

  module _ {od ℓd} {J : Precategory od ℓd} {F : Functor J C} where
    left-adjoint-colimit : Colimit F → Colimit (L F∘ F)
    left-adjoint-colimit colim = colim′′ where
      lim : Limit (Functor.op F)
      lim = Colimit→Co-limit _ colim

      lim′ : Limit (Functor.op L F∘ Functor.op F)
      lim′ = right-adjoint-limit adj′ lim

      colim′ : Colimit (Functor.op (Functor.op L F∘ Functor.op F))
      colim′ = Co-limit→Colimit _ (subst Limit (sym F^op^op≡F) lim′)

      colim′′ : Colimit (L F∘ F)
      colim′′ = subst Colimit (Functor-path (λ x → refl) λ x → refl) colim′

```

TODO [Amy 2022-04-05]
cocontinuity
-->
