<!--
```agda
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Diagram.Coend
open import Cat.Prelude

open import Data.Set.Coequaliser
```
-->

```agda
module Cat.Diagram.Coend.Sets where
```

# Coends in Sets {defines="coends-in-sets"}

We can give an explicit construction of [coends] in the category of sets
by taking a [coequaliser]. Intuitively, the coend should be the
"sum of the diagonal" of a functor $\cC\op \times \cC \to \Sets$,
which translates directly to the sigma type `Σ[ X ∈ Ob ] ∣ F₀ (X , X) ∣`.
However, trying to use this without some sort of quotient is going to
be immediately problematic. For starters, this isn't even a set!
More importantly, we run into an immediate issue when we try to prove
that this is extranatural; we need to show that
`F₁ (f , id) Fyx ≡ F₁ (id , f) Fyx` for all `f : Hom Y X` and
`∣ Fyx : F₀ (X , Y) ∣`.

[coends]: Cat.Diagram.Coend.html

However, if we take a [coequaliser] of `Σ[ X ∈ Ob ] ∣ F₀ (X , X) ∣` both
of these problems immediately disappear. In particular, we want to take
the coequaliser of the following pair of functions:

[coequaliser]: Data.Set.Coequaliser.html

~~~{.quiver .short-2}
\begin{tikzcd}
	{F(X,Y)} && {F(X,X)}
	\arrow["{F(f,id)}"', shift right=2, from=1-1, to=1-3]
	\arrow["{F(id,f)}", shift left=3, from=1-1, to=1-3]
\end{tikzcd}
~~~

This allows us to prove the troublesome extranaturality condition
directly with `glue`{.Agda}. With that motivation out of the way, let's
continue with the construction!

```agda
module _ {o ℓ} {C : Precategory o ℓ} (F : Functor (C ^op ×ᶜ C) (Sets (o ⊔ ℓ))) where

  open Precategory C
  open Functor F
  open Coend
  open Cowedge
```

We start by defining the two maps we will coequalise along. Quite a
bit of bundling is required to make things well typed, but this is
exactly the same pair of maps in the diagram above.

```agda
  dimapl : Σ[ X ∈ Ob ] Σ[ Y ∈ Ob ] Σ[ f ∈ Hom Y X ] ∣ F₀ (X , Y) ∣
         → Σ[ X ∈ Ob ] ∣ F₀ (X , X) ∣
  dimapl (X , Y , f , Fxy) = X , (F₁ (id , f) Fxy)

  dimapr : Σ[ X ∈ Ob ] Σ[ Y ∈ Ob ] Σ[ f ∈ Hom Y X ] ∣ F₀ (X , Y) ∣
         → Σ[ X ∈ Ob ] ∣ F₀ (X , X) ∣
  dimapr (X , Y , f , Fxy) = Y , (F₁ (f , id) Fxy)
```

Constructing the universal `Cowedge`{.Agda} is easy now that we've
taken the right coequaliser.

```agda
  Set-coend : Coend F
  Set-coend = coend where
    universal-cowedge : Cowedge F
    universal-cowedge .nadir = el! (Coeq dimapl dimapr)
    universal-cowedge .ψ X Fxx = inc (X , Fxx)
    universal-cowedge .extranatural {X} {Y} f =
     funext λ Fyx → glue (Y , X , f , Fyx)
```

To show that the `Cowedge` is universal, we can essentially just
project out the bundled up object from the coend and feed that
to the family associated to the cowedge `W`.

```agda
    factoring : (W : Cowedge F) → Coeq dimapl dimapr → ⌞ W .nadir ⌟
    factoring W (inc (o , x)) = W .ψ o x
    factoring W (glue (X , Y , f , Fxy) i) = W .extranatural f i Fxy
    factoring W (squash x y p q i j) = W .nadir .is-tr (factoring W x) (factoring W y) (λ i → factoring W (p i)) (λ i → factoring W (q i)) i j

    coend : Coend F
    coend .cowedge = universal-cowedge
    coend .factor W = factoring W
    coend .commutes = refl
    coend .unique {W = W} p = ext λ X x → p #ₚ x
```

This construction is actually functorial! Given any functor
$\cC\op \times \cC \to \Sets$, we can naturally construct its
Coend in $\Sets$. This ends up assembling into a functor from the
functor category $[ \cC\op \times \cC , \Sets ]$ into $\Sets$.

```agda
module _ {o ℓ} {𝒞 : Precategory o ℓ} where
  open Precategory 𝒞
  open Functor
  open _=>_

  Coends : Functor Cat[ 𝒞 ^op ×ᶜ 𝒞 , Sets (o ⊔ ℓ) ] (Sets (o ⊔ ℓ))
  Coends .F₀ F = el! (Coeq (dimapl F) (dimapr F))
  Coends .F₁ α =
    Coeq-rec squash (λ ∫F → inc ((∫F .fst) , α .η _ (∫F .snd))) λ where
      (X , Y , f , Fxy) →
        (ap (λ ϕ → inc (X , ϕ)) $ happly (α .is-natural (X , Y) (X , X) (id , f)) Fxy) ··
        glue (X , Y , f , α .η (X , Y) Fxy) ··
        (sym $ ap (λ ϕ → inc (Y , ϕ)) $ happly (α .is-natural (X , Y) (Y , Y) (f , id)) Fxy)
  Coends .F-id = trivial!
  Coends .F-∘ f g = trivial!
```
