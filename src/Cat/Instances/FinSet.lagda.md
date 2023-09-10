<!--
```agda
open import Cat.Functor.Properties.FullyFaithful
open import Cat.Instances.Sets.Cocomplete
open import Cat.Instances.Sets.Complete
open import Cat.Diagram.Colimit.Finite
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Coequaliser
open import Cat.Functor.Properties
open import Cat.Diagram.Coproduct
open import Cat.Diagram.Equaliser
open import Cat.Diagram.Terminal
open import Cat.Diagram.Initial
open import Cat.Diagram.Product
open import Cat.Instances.Sets
open import Cat.Prelude

open import Data.Fin.Closure
open import Data.Fin

open Functor
```
-->

```agda
module Cat.Instances.FinSet where
```

# The category of finite sets

Throughout this page, let $n$ be a natural number and $[n]$ denote the
[standard $n$-element ordinal]. The **category of finite sets**,
$\FinSets$, is the category with set of objects $\bb{N}$ the natural
numbers, with set of maps $\hom(j,k)$ the set of functions $[j] \to
[k]$. This category is not [[univalent|univalent category]], but it is
[weakly equivalent] to the full subcategory of $\Sets$ on those objects
which are [[merely]] isomorphic to a finite ordinal. The reason for this
"skeletal" definition is that $\FinSets$ is a small category, so that
presheaves on $\FinSets$ are a [Grothendieck topos].

[standard $n$-element ordinal]: Data.Fin.html
[weakly equivalent]: Cat.Functor.Equivalence.html#between-categories
[Grothendieck topos]: Topoi.Base.html

```agda
FinSets : Precategory lzero lzero
FinSets .Precategory.Ob = Nat
FinSets .Precategory.Hom j k = Fin j → Fin k
FinSets .Precategory.Hom-set x y = hlevel 2
FinSets .Precategory.id x = x
FinSets .Precategory._∘_ f g x = f (g x)
FinSets .Precategory.idr f = refl
FinSets .Precategory.idl f = refl
FinSets .Precategory.assoc f g h = refl
```

The category of finite sets can be seen as a [[full subcategory]] of
the [[category of sets]] via the [[fully faithful]] inclusion functor
that sends $n$ to $[n]$:

```agda
Fin→Sets : Functor FinSets (Sets lzero)
Fin→Sets .F₀ n = el! (Fin n)
Fin→Sets .F₁ f = f
Fin→Sets .F-id = refl
Fin→Sets .F-∘ _ _ = refl

Fin→Sets-is-ff : is-fully-faithful Fin→Sets
Fin→Sets-is-ff = id-equiv
```

## Finite limits and colimits

The nice [[closure properties of finite sets|closure of finite sets]],
along with the fact that [[fully faithful functors reflect (co)limits|ff-reflect-limits]],
imply that the category $\FinSets$ admits finite products and coproducts,
equalisers and coequalisers, making it [[finitely complete]] and [[finitely cocomplete]].

```agda
FinSets-finitely-complete : Finitely-complete FinSets
FinSets-finitely-complete = with-equalisers _ terminal products equalisers where
  terminal : Terminal FinSets
  terminal = ff→reflects-Terminal Fin→Sets Fin→Sets-is-ff
    Sets-terminal
    (equiv→iso (is-contr→≃ (hlevel 0) Finite-one-is-contr))

  products : has-products FinSets
  products a b = ff→reflects-Product Fin→Sets Fin→Sets-is-ff
    (Sets-products _ _)
    (equiv→iso Finite-multiply)

  equalisers : has-equalisers FinSets
  equalisers f g = ff→reflects-Equaliser Fin→Sets Fin→Sets-is-ff
    (Sets-equalisers f g)
    (equiv→iso (Finite-subset (λ x → f x ≡ g x) .snd e⁻¹))

FinSets-finitely-cocomplete : Finitely-cocomplete FinSets
FinSets-finitely-cocomplete = with-coequalisers _ initial coproducts coequalisers where
  initial : Initial FinSets
  initial = ff→reflects-Initial Fin→Sets Fin→Sets-is-ff
    Sets-initial
    (equiv→iso (Lift-≃ ∙e Finite-zero-is-initial e⁻¹))

  coproducts : has-coproducts FinSets
  coproducts a b = ff→reflects-Coproduct Fin→Sets Fin→Sets-is-ff
    (Sets-coproducts _ _)
    (equiv→iso Finite-coproduct)

  coequalisers : has-coequalisers FinSets
  coequalisers f g = ff→reflects-Coequaliser Fin→Sets Fin→Sets-is-ff
    (Sets-coequalisers f g)
    (equiv→iso (Finite-coequaliser f g .snd e⁻¹))
```
