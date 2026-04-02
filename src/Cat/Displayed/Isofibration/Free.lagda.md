---
description: |

---

<!--
```agda
open import Cat.Displayed.Instances.Lifting
open import Cat.Displayed.Isofibration
open import Cat.Functor.Properties
open import Cat.Displayed.Functor
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Displayed.Morphism
import Cat.Functor.Reasoning
import Cat.Reasoning
import Cat.Morphism

open Cat.Displayed.Morphism using (module _≅[_]_)
open Cat.Morphism._≅_
open _≅[_]_
open ∫Hom
```
-->

```agda
module Cat.Displayed.Isofibration.Free where
```

<!--
```agda
module _
  {ob ℓb oe ℓe}
  {B : Precategory ob ℓb}
  {E : Precategory oe ℓe}
  (P : Functor E B)
  where
  private
    module P = Cat.Functor.Reasoning P
    module B = Cat.Reasoning B
    module E = Cat.Reasoning E

  open Displayed
  open Functor
```
-->

```agda
  Free-isofibration : Displayed B (ℓb ⊔ oe) (ℓb ⊔ ℓe)
  Free-isofibration .Ob[_] x = Σ[ u ∈ E ] (P.₀ u B.≅ x)
```

~~~{.quiver .attach-around}
\[\begin{tikzcd}
  u \\
  {P(u)} & {x\text{,}}
  \arrow[lies over, from=1-1, to=2-1]
  \arrow["\phi"', from=2-1, to=2-2]
\end{tikzcd}\]
~~~

```agda
  Free-isofibration .Hom[_] f (u , φ) (v , ψ) = Σ[ h ∈ E.Hom u v ]
    B.to ψ B.∘ P.₁ h ≡ f B.∘ B.to φ
```

~~~{.quiver}
\[\begin{tikzcd}
  & u && v \\
  & {P(u)} && {P(v)} \\
  x &&&& y
  \arrow[lies over, from=1-2, to=2-2]
  \arrow[lies over, from=1-4, to=2-4]
  \arrow["{P(h)}"', from=2-2, to=2-4]
  \arrow["h"{description}, from=1-2, to=1-4]
  \arrow["\phi"', from=2-2, to=3-1]
  \arrow["\psi"', from=2-4, to=3-5]
  \arrow["f"', curve={height=12pt}, from=3-1, to=3-5]
\end{tikzcd}\]
~~~

<details>
<summary>The rest of the data needed to make a displayed category
(identities, composition, and the laws) are evidently inherited from
those in $\cE$.
</summary>

```agda
  Free-isofibration .Hom[_]-set f a b = hlevel 2

  Free-isofibration .id' = record where
    fst = E.id
    snd = B.elimr P.F-id ∙ B.introl refl

  Free-isofibration ._∘'_ (f , φ) (g , ψ) = record where
    fst = f E.∘ g
    snd = B.cdr (P.F-∘ f g) ∙ B.pulll φ ∙ B.pullr ψ ∙ B.assoc _ _ _

  Free-isofibration .idr' f' = Σ-prop-pathp! (E.idr _)
  Free-isofibration .idl' f' = Σ-prop-pathp! (E.idl _)
  Free-isofibration .assoc' f' g' h' = Σ-prop-pathp! (E.assoc _ _ _)
  Free-isofibration .hom[_] p f = record
    { fst = f .fst
    ; snd = f .snd ∙ B.car p
    }
  Free-isofibration .coh[_] p f = Σ-prop-pathp! refl
```

</details>

<!--
```agda
module _
  {ob ℓb oe ℓe}
  {B : Precategory ob ℓb}
  {E : Precategory oe ℓe}
  {P : Functor E B}
  where
  private
    module Iso[P] = Cat.Displayed.Morphism (Free-isofibration P)
    module P = Cat.Functor.Reasoning P
    module B = Cat.Reasoning B
    module E = Cat.Reasoning E

  open Displayed-functor
  open Isofibration
  open Functor
  open Lifting
```
-->

```agda
  Free-isofibration-iso
    : ∀ {a b} {u : a B.≅ b} {x y : E.Ob} {φ : P.₀ x B.≅ a} {ψ : P.₀ y B.≅ b}
        (θ : x E.≅ y)
    → ψ .to B.∘ P.₁ (θ .to) ≡ u .to B.∘ φ .to
    → (x , φ) Iso[P].≅[ u ] (y , ψ)
  Free-isofibration-iso {u = u} {φ = φ} {ψ = ψ} θ p =
    Iso[P].make-iso[ u ]
      (θ .to   , p)
      (θ .from , q)
      (Σ-prop-pathp! (θ .invl))
      (Σ-prop-pathp! (θ .invr))
    where abstract
      q : φ .to B.∘ P.₁ (θ .from) ≡ u .from B.∘ ψ .to
      q = flip Equiv.from refl $
        φ .to B.∘ P.₁ (θ .from) ≡ u .from B.∘ ψ .to     ≃⟨ B.post-invl (B.iso→invertible u) ⟩
        u .to B.∘ φ .to B.∘ P.₁ (θ .from) ≡ ψ .to       ≃⟨ ∙-pre-equiv (B.extendl p) ⟩
        ψ .to B.∘ P.₁ (θ .to) B.∘ P.₁ (θ .from) ≡ ψ .to ≃⟨ ∙-pre-equiv (B.intror (P.annihilate (θ .invl))) ⟩
        ψ .to ≡ ψ .to                                   ≃∎

  Free-isofibration-is-isofibration : Isofibration (Free-isofibration P)
  Free-isofibration-is-isofibration ._^*_     ψ (x , φ) = x , ψ B.∘Iso φ
  Free-isofibration-is-isofibration .^*-lifts ψ (x , φ) = Free-isofibration-iso
    E.id-iso
    (P.elimr refl)
```

```agda
  Free-isofibration-lifting : Lifting (Free-isofibration P) P
  Free-isofibration-lifting .F₀'  x   = x , B.id-iso
  Free-isofibration-lifting .F₁'  f   = f , B.id-comm-sym
  Free-isofibration-lifting .F-id'    = Σ-prop-pathp! refl
  Free-isofibration-lifting .F-∘' f g = Σ-prop-pathp! refl

  private
    E→∫ : Functor E (∫ (Free-isofibration P))
    E→∫ = Lifting→Functor _ Free-isofibration-lifting

  Free-isofibration-lifting-split-eso : is-split-eso E→∫
  Free-isofibration-lifting-is-ff     : is-fully-faithful E→∫

  Free-isofibration-lifting-split-eso (b , x , φ) = record where
    fst = x
    snd = total-iso-from-isos _ φ $ Free-isofibration-iso E.id-iso $ B.cdr P.F-id

  Free-isofibration-lifting-is-ff = is-iso→is-equiv λ where
    .is-iso.from h → h .snd .fst
    .is-iso.rinv h → ∫Hom-path _
      (B.introl refl ∙∙ h .snd .snd ∙∙ B.elimr refl)
      (Σ-prop-pathp! refl)
    .is-iso.linv h → refl
```

```agda
  Free-isofibration-factor
    : ∀ {oh ℓh} {H : Displayed B oh ℓh}
    → Isofibration H → Lifting H P
    → Vertical-functor (Free-isofibration P) H
  Free-isofibration-factor {H = H} H-isofib F = F† where
```

<!--
```agda
    open Cat.Displayed.Reasoning H
    module H = Isofibration H-isofib
    module F = Lifting F renaming (F₀' to ₀' ; F₁' to ₁')
```
-->

```agda
    F† : Vertical-functor (Free-isofibration P) H
    F† .F₀' (x , φ) = φ H.^* F.₀' x
    F† .F₁' {a' = x , φ} {b' = y , ψ} (h , p) =
      hom[ B.pulll p ∙ B.cancelr (φ .invl) ] (H.π* ∘' F.₁' h ∘' H.ι!)
```

<details>
<summary>Verifying that this assignment is functorial boils down to a
straightforward calculation, using functoriality of the lifting
$F$.</summary>

```agda
    F† .F-id' {x' = x , φ} = begin[]
      hom[] (H.π* ∘' F.₁' E.id ∘' H.ι!) ≡[]⟨ unwrap _ ⟩
      H.π* ∘' F.₁' E.id ∘' H.ι!         ≡[]⟨ refl⟩∘'⟨ eliml[] _ F.F-id' ⟩
      H.π* ∘' H.ι!                      ≡[]⟨ H.^*-lifts _ _ .invl' ⟩
      id'                               ∎[]

    F† .F-∘' {a' = x , φ} {b' = y , ψ} {c' = z , θ} {f' = f , p} {g' = g , q} =
      let
        open _≅[_]_ (H.^*-lifts φ (F.₀' x)) renaming (from' to φ^*→; to' to φ^*←)
        open _≅[_]_ (H.^*-lifts ψ (F.₀' y)) renaming (from' to ψ^*→; to' to ψ^*←)
        open _≅[_]_ (H.^*-lifts θ (F.₀' z)) renaming (from' to θ^*→; to' to θ^*←)
      in begin[]
        hom[] (θ^*← ∘' F.₁' (f E.∘ g) ∘' φ^*→)                           ≡[]⟨ unwrap _ ⟩
        θ^*← ∘' F.₁' (f E.∘ g) ∘' φ^*→                                   ≡[]⟨ refl⟩∘'⟨ (pushl[] _ (F.F-∘' f g)) ⟩
        θ^*← ∘' F.₁' f ∘' F.₁' g ∘' H.ι!                                 ≡[]⟨ refl⟩∘'⟨ refl⟩∘'⟨ (introl[] _ (H.^*-lifts _ _ .invr')) ⟩
        θ^*← ∘' F.₁' f ∘' (ψ^*→ ∘' ψ^*←) ∘' F.₁' g ∘' H.ι!               ≡[]⟨ refl⟩∘'⟨ refl⟩∘'⟨ pullr[] _ (wrap _) ⟩
        θ^*← ∘' F.₁' f ∘' ψ^*→ ∘' hom[] (ψ^*← ∘' F.₁' g ∘' φ^*→)         ≡[]⟨ pushr[] _ (assoc' _ _ _) ∙[] wrapl _ ⟩
        hom[] (θ^*← ∘' F.₁' f ∘' ψ^*→) ∘' hom[] (ψ^*← ∘' F.₁' g ∘' φ^*→) ∎[]
```

</details>
