<!--
```agda
open import Cat.Displayed.Instances.Lifting
open import Cat.Displayed.Isofibration.Free
open import Cat.Displayed.Cartesian
open import Cat.Functor.Properties
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning
import Cat.Morphism

open Cat.Morphism._≅_
open is-cartesian
```
-->

```agda
module Cat.Displayed.Cartesian.Street where
```

<!--
```agda
private variable
  o ℓ o' ℓ' : Level
  E B : Precategory o ℓ

module _ (P : Functor E B) where
  private
    module B = Cat.Reasoning B
    module E = Cat.Reasoning E
    module P = Functor P

    P[] = Free-isofibration P

    open Lifting (Free-isofibration-lifting P) using ()
      renaming (F₀' to inc₀ ; F₁' to inc₁)
```
-->

# Street fibrations {defines=street-fibration}

```agda
  is-street-cartesian : ∀ {x y} → E.Hom x y → Type _
  is-street-cartesian {x} {y} f =
    ∀ {x'} (h : E.Hom x' y) (u : B.Hom (P · x') (P · x))
    → P.₁ h ≡ P.₁ f B.∘ u
    → is-contr (Σ[ v ∈ E.Hom x' x ] (f E.∘ v ≡ h) × (P.₁ v ≡ u))

  is-street-fibration : Type _
  is-street-fibration =
    ∀ {a b} (f : B.Hom a b) (b' : P[] ʻ b) →
    Σ[ a' ∈ P[] ʻ a ]
    Σ[ f' ∈ E.Hom (a' .fst) (b' .fst) ]
        is-street-cartesian f'
      × b' .snd .to B.∘ P.₁ f' ≡ f B.∘ a' .snd .to

  is-street-cartesian→is-cartesian
    : ∀ {x y} (f : E.Hom x y)
    → is-street-cartesian f
    → is-cartesian P[] {a' = inc₀ _} {inc₀ _} (P.₁ f) (inc₁ f)
  is-street-cartesian→is-cartesian f cart = record where
    universal {u' = u' , ui} m (g , α) =
      let
        contr (m , _ , c) _ = cart g (m B.∘ ui .to) $
          B.introl refl ∙∙ α ∙∙ B.pullr refl
       in m , B.eliml refl ∙ c
    commutes {u' = u' , ui} m (g , α) = Σ-prop-path! $ cart _ _ _ .centre .snd .fst
    unique {u' = u' , ui} {m} (m' , α) β = Σ-prop-path! $ ap fst $ sym $
      cart _ _ _ .paths (m' , ap fst β , B.introl refl ∙ α)
```

<details>
<summary>The short calculation above shows that a $P$-cartesian map $f :
\cE(x, y)$ generates a Cartesian map over $P(f)$ *only* when its domain
and codomain in $P_\bull$ are *lifted* from $x$ and $y$.

However, to show that $P_\bull$ is a Cartesian fibration, we will
require a technical lemma extending this result to the case where $f$ is
considered as a map $x' \to y'$, with $x' \liesover x$ (resp. $y'
\liesover y$), given an external witness that $f$ commutes with the maps
$P(x') \cong x$ (resp. $P(y') \cong y$).
</summary>

```agda
  private
    adjust-cartesian'
      : ∀ {x y x' y'} {f : B.Hom x y} {f' : E.Hom (x' .fst) (y' .fst)}
      → is-cartesian P[] {a' = inc₀ _} {inc₀ _} (P.₁ f') (inc₁ f')
      → (α : y' .snd .to B.∘ P.₁ f' ≡ f B.∘ x' .snd .to)
      → is-cartesian P[] {a' = x'} {y'} f (f' , α)
    adjust-cartesian' {x' = x' , xi} {y' , yi} {f' = f} cart α = mk where
      module cart = is-cartesian cart
      mk : is-cartesian P[] {a' = x' , xi} {y' , yi} _ _
      mk .universal {u' = u'@(_ , ui)} m (g , β) = m' , q where
        abstract
          p : B.id B.∘ P.₁ g ≡ (P.₁ f B.∘ xi .from B.∘ m) B.∘ ui .to
          p = B.eliml refl ∙ B.iso→monic yi _ _
            (β ∙ sym (B.pulll (B.extendl α) ∙ B.cdar (B.cancell (xi .invl))))

        open Σ (cart.universal {u' = u'} (xi .from B.∘ m) (g , p))
          renaming (fst to m' ; snd to γ)

        abstract
          q : xi .to B.∘ P.₁ m' ≡ m B.∘ ui .to
          q = B.pushr (B.introl refl ∙ γ) ∙ B.car (B.cancell (xi .invl))

      mk .commutes {u' = u'} m (g , β) =
        Σ-prop-path! $ ap fst $ cart.commutes {u' = u'} _ _

      mk .unique {u' = u' , ui} {m} (m' , β) γ =
        Σ-prop-path! $ ap fst $ cart.unique (m' , p) (Σ-prop-path! (ap fst γ))
        where
          p : B.id B.∘ P.₁ m' ≡ (xi .from B.∘ m) B.∘ ui .to
          p = B.eliml refl ∙ B.iso→monic xi _ _
            (β ∙ sym (B.pulll (B.cancell (xi .invl))))
```

</details>

```agda
  Cartesian-street-fibration : is-street-fibration → Cartesian-fibration P[]
  Cartesian-street-fibration lifts f y' =
    let (a' , f' , f'c , α) = lifts f y' in record where
      x'        = a'
      lifting   = f' , α
      cartesian = adjust-cartesian' (is-street-cartesian→is-cartesian f' f'c) α
```
