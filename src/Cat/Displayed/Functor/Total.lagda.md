<!--
```agda
open import Cat.Displayed.Functor
open import Cat.Displayed.Total
open import Cat.Functor.Compose
open import Cat.Displayed.Base
open import Cat.Functor.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Displayed.Functor.Total where
```

# Total functor {defines="total-functor"}

Given [[displayed categories]] $\cE \liesover \cA$ and $\cF \liesover
\cB$, and a [[displayed functor]] $F' : \cE \to \cF$ over $F : \cA \to
\cB$, we can recover an ordinary [[functor]] $\int F : \int \cE \to \int
\cF$ between [[total categories]].

<!--
```agda
module _
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  {F : Functor A B} (F' : Displayed-functor F ℰ ℱ)
  where
```
-->

```agda
  ∫ᶠ : Functor (∫ ℰ) (∫ ℱ)
  ∫ᶠ = record where
    open Functor F
    open Displayed-functor F'

    F₀ (x , x') = F₀ x , F₀' x'
    F₁ (∫hom f f') = ∫hom (F₁ f) (F₁' f')
    F-id = ∫Hom-path ℱ F-id F-id'
    F-∘ (∫hom f f') (∫hom g g') = ∫Hom-path ℱ (F-∘ f g) F-∘'
```

The total functor respects the projection `πᶠ`{.Agda} to the base
category so that

~~~{.quiver .attach-around}
\begin{tikzcd}
	{\int \cE} && {\int \cF} \\
	\\
	\cA && \cB
	\arrow["{\int F'}", from=1-1, to=1-3]
	\arrow["{\pi_{\cE}}"', from=1-1, to=3-1]
	\arrow["{\pi_\cF}", from=1-3, to=3-3]
	\arrow["F"', from=3-1, to=3-3]
\end{tikzcd}
~~~

commutes.

```agda
  ∫ᶠ-preserves-base : F F∘ (πᶠ ℰ) ≡ (πᶠ ℱ) F∘ ∫ᶠ
  ∫ᶠ-preserves-base = Functor-path (λ x → refl) (λ f → refl)
```

Indeed, a displayed functor $F'$ over $F$ can be thought of as a
repackaging of the data of a functor $\int F'$ for which this diagram
commutes.

## Total natural transformations {defines="total-natural-transformation"}

Suppose we have an additional [[displayed functor]] $G' : \cE \to \cF$
over $G : \cA \to \cB$, and a [[displayed natural transformation]]
$\eta' : F' \To G'$ over $\eta : F \To G$. We can then similarly recover
an ordinary [[natural transformation]] $\int \eta : \int F \To \int G$
between [[total functor|total functors]]:

<!--
```agda
module _
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  {F G : Functor A B} {ηⁿ : F => G}
  {F' : Displayed-functor F ℰ ℱ}
  {G' : Displayed-functor G ℰ ℱ}
  (η'ⁿ : F' =[ ηⁿ ]=> G')
  where

  open _=>_ ηⁿ
  open _=[_]=>_ η'ⁿ
```
-->

```agda
  ∫ⁿ : ∫ᶠ F' => ∫ᶠ G'
  ∫ⁿ = record where
    η (x , x') = ∫hom (η x) (η' x')
    is-natural (x , x') (y , y') (∫hom f f') = ∫Hom-path ℱ
      (is-natural x y f) (is-natural' x' y' f')
```

Applying the projection `πᶠ`{.Agda} to the total natural transformation
$\int\eta'$ gives back $\eta$ in the following sense:

```agda
  ∫ⁿ-preserves-base : PathP
    (λ i → ∫ᶠ-preserves-base F' i => ∫ᶠ-preserves-base G' i)
    (ηⁿ ◂ πᶠ ℰ) (πᶠ ℱ ▸ ∫ⁿ)
  ∫ⁿ-preserves-base = Nat-pathp
    (∫ᶠ-preserves-base F') (∫ᶠ-preserves-base G') λ x → refl
```
