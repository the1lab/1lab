```agda
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Terminal
open import Cat.Diagram.Initial
open import Cat.Functor.Base
open import Cat.Morphism
open import Cat.Prelude hiding (J)

import Cat.Reasoning

module Cat.Functor.Conservative where
```

<!--
```agda
private variable
  o h o₁ h₁ : Level
  C D J : Precategory o h
open Precategory
open Functor
```
-->

# Conservative Functors

We say a functor is _conservative_ if it reflects isomorphisms. More concretely,
if $f : A \to B$ is some morphism $\ca{C}$, and if $F(f)$ is an iso in $\ca{D}$,
then $f$ must have already been an iso in $\ca{C}$!

```agda
is-conservative : Functor C D → Type _
is-conservative {C = C} {D = D} F =
  ∀ {A B} {f : C .Hom A B}
  → is-invertible D (F .F₁ f) → is-invertible C f
```

As a general fact, conservative functors reflect limits that they preserve
(given those limits exist in the first place!).

The rough proof sketch is as follows: Let $K$ be some cone in $C$ such that
$F(K)$ is a limit in $D$, and $L$ a limit in $C$ of the same diagram.
By the universal property of $L$, there exists a map $\eta$ from the apex of $K$
to the apex of $L$ in $C$. Furthermore, as $F(K)$ is a limit in $D$, $F(\eta)$
becomes an isomorphism in $D$. However, $F$ is conservative, which implies that
$\eta$ was an isomorphism in $C$ all along! This means that $K$ must be a limit
in $C$ as well (see `apex-iso→is-limit`{.Agda}).

```agda
module _ {F : Functor C D} (conservative : is-conservative F) where
  private
    module D = Cat.Reasoning D
    module C = Cat.Reasoning C
    module Cocones {o h o′ h′} {J : Precategory o h} {C : Precategory o′ h′} {Dia : Functor J C} = Cat.Reasoning (Cocones Dia)

  conservative-reflects-limits
    : ∀ {Dia : Functor J C} → (L : Limit Dia)
    → (∀ (K : Cone Dia) → Preserves-limit F K)
    → (∀ (K : Cone Dia) → Reflects-limit F K)
  conservative-reflects-limits {Dia = Dia} L-lim preserves K limits =
    apex-iso→is-limit Dia K L-lim $ conservative invert
    where
      F∘L-lim : Limit (F F∘ Dia)
      F∘L-lim .Terminal.top = F-map-cone F (Terminal.top L-lim)
      F∘L-lim .Terminal.has⊤ = preserves (Terminal.top L-lim) (Terminal.has⊤ L-lim)

      K-lim : Limit (F F∘ Dia)
      K-lim .Terminal.top = F-map-cone F K
      K-lim .Terminal.has⊤ = limits

      module L-lim = Terminal L-lim
      module F∘L-lim = Terminal F∘L-lim
      open Cone-hom

      F-preserves-universal
        : F∘L-lim.! .hom ≡ F .F₁ (L-lim.! {x = K} .hom)
      F-preserves-universal =
        F∘L-lim.! .hom                           ≡⟨ ap hom (F∘L-lim.!-unique (F-map-cone-hom F L-lim.!)) ⟩
        F-map-cone-hom F (Terminal.! L-lim) .hom ≡⟨⟩
        F .F₁ (L-lim.! .hom)                     ∎

      open is-invertible
      open Inverses
      inverse = !-invertible (Cones (F F∘ Dia)) F∘L-lim K-lim

      invert : D.is-invertible (F .F₁ (L-lim.! .hom))
      invert .inv = inverse .inv .hom
      invert .inverses .invl =
        F .F₁ (L-lim.! .hom) D.∘ invert .inv ≡˘⟨ F-preserves-universal D.⟩∘⟨refl ⟩
        F∘L-lim.! .hom D.∘ invert .inv       ≡⟨ ap hom (inverse .inverses .invl) ⟩
        D.id                                 ∎
      invert .inverses .invr =
        invert .inv D.∘ F .F₁ (L-lim.! .hom) ≡˘⟨ D.refl⟩∘⟨ F-preserves-universal ⟩
        invert .inv D.∘ F∘L-lim.! .hom       ≡⟨ ap hom (inverse .inverses .invr) ⟩
        D.id                                 ∎
```

We also have a dual theorem for colimits.

```agda
  conservative-reflects-colimits
    : ∀ {Dia : Functor J C} → (L : Colimit Dia)
    → (∀ (K : Cocone Dia) → Preserves-colimit F K)
    → (∀ (K : Cocone Dia) → Reflects-colimit F K)
  conservative-reflects-colimits
    {Dia = Dia} L-colim preserves K F∘K-colimits =
    coapex-iso→is-colimit Dia K L-colim
    $ conservative
    invert
    where

      F∘K-colim : Colimit (F F∘ Dia)
      F∘K-colim .Initial.bot = F-map-cocone F K
      F∘K-colim .Initial.has⊥ = F∘K-colimits

      F∘L-colim : Colimit (F F∘ Dia)
      F∘L-colim = F-map-colimit F L-colim (preserves (Colimit-cocone Dia L-colim))

      module L-colim = Initial L-colim
      module F∘L-colim = Initial F∘L-colim
      module F∘K-colim = Initial F∘K-colim
      open Cocone-hom

      L : Cocone Dia
      L = L-colim.bot

      F∘L : Cocone (F F∘ Dia)
      F∘L = F-map-cocone F L-colim.bot

      F∘K : Cocone (F F∘ Dia)
      F∘K = F-map-cocone F K

      L-universal : (K′ : Cocone Dia) → Cocone-hom Dia L K′
      L-universal K′ = L-colim.¡ {K′}

      F∘L-universal : (K′ : Cocone (F F∘ Dia)) → Cocone-hom (F F∘ Dia) F∘L K′
      F∘L-universal K′ =  F∘L-colim.¡ {K′}

      F∘K-universal : (K′ : Cocone (F F∘ Dia)) → Cocone-hom (F F∘ Dia) F∘K K′
      F∘K-universal K′ =  F∘K-colim.¡ {K′}

      module F∘L-universal K′ = Cocone-hom (F∘L-universal K′)
      module L-universal K′ = Cocone-hom (L-universal K′)
      module F∘K-universal K′ = Cocone-hom (F∘K-universal K′)

      F-preserves-universal
        : ∀ {K′} → F∘L-universal.hom (F-map-cocone F K′) ≡ F. F₁ (L-universal.hom K′)
      F-preserves-universal {K′} =
        F∘L-universal.hom (F-map-cocone F K′)     ≡⟨ ap hom (F∘L-colim.¡-unique (F-map-cocone-hom F (L-universal K′))) ⟩
        hom (F-map-cocone-hom F (L-universal K′)) ≡⟨⟩
        F .F₁ (L-universal.hom K′) ∎

      invert : is-invertible D (F .F₁ (Colimit-universal Dia L-colim K))
      invert .is-invertible.inv = F∘K-universal.hom F∘L
      invert .is-invertible.inverses .Inverses.invl =
        F .F₁ (L-universal.hom K) D.∘ F∘K-universal.hom F∘L ≡˘⟨ ap (D._∘ F∘K-universal.hom F∘L) F-preserves-universal ⟩
        F∘L-universal.hom F∘K D.∘ F∘K-universal.hom F∘L     ≡⟨⟩
        hom (F∘L-universal F∘K Cocones.∘ F∘K-universal F∘L) ≡⟨ ap hom (F∘K-colim.¡-unique₂ (F∘L-universal F∘K Cocones.∘ F∘K-universal F∘L) Cocones.id) ⟩
        D.id ∎
      invert .is-invertible.inverses .Inverses.invr =
        F∘K-universal.hom F∘L D.∘ F .F₁ (L-universal.hom K) ≡˘⟨ ap (F∘K-universal.hom F∘L D.∘_) F-preserves-universal ⟩
        F∘K-universal.hom F∘L D.∘ F∘L-universal.hom F∘K     ≡⟨⟩
        hom (F∘K-universal F∘L Cocones.∘ F∘L-universal F∘K) ≡⟨ ap hom (F∘L-colim.¡-unique₂ (F∘K-universal F∘L Cocones.∘ F∘L-universal F∘K) Cocones.id) ⟩
        D.id ∎
```
