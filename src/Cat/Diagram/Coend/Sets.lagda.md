```agda
open import Cat.Diagram.Coend
open import Cat.Instances.Product
open import Cat.Instances.Sets
open import Cat.Prelude

open import Data.Set.Coequaliser

module Cat.Diagram.Coend.Sets where
```

# Coends in Sets

We can give an explicit construction of [coends] in the category of sets
by taking a [coequaliser]. Intuitively, the coend should be the
"sum of the diagonal" of a functor $\ca{C}\op \times \ca{C} \to \sets$,
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

[coequaliser] Data.Set.Coequaliser.html

~~~{.quiver}
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
module _ {o ℓ κ} {C : Precategory o ℓ} (F : Functor (C ^op ×ᶜ C) (Sets (o ⊔ ℓ ⊔ κ))) where

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
    coend : Coend F
    coend .cowedge = universal-cowedge
    coend .factor W =
      Coeq-rec hlevel! (λ ∫F → W .ψ (∫F .fst) (∫F .snd)) λ where
        (X , Y , f , Fxy) → happly (W .extranatural f) Fxy
    coend .commutes = refl
    coend .unique {W = W} p =
      funext $ Coeq-elim hlevel! (λ ∫F → happly p (∫F .snd)) λ where
        (X , Y , f , Fxy) → is-set→squarep (λ _ _ → is-tr (W .nadir)) _ _ _ _
```

