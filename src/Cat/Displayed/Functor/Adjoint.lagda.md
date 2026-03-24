<!--
```agda
open import Cat.Functor.Adjoint.Compose
open import Cat.Functor.Equivalence
open import Cat.Displayed.Functor
open import Cat.Instances.Functor
open import Cat.Functor.Adjoint
open import Cat.Displayed.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Displayed.Functor.Adjoint where
```

# Displayed adjunctions

Following the general theme of defining displayed structure over
1-categorical structure, we can define a notion of displayed
[[adjoint functors]].

:::{.definition #displayed-adjunction alias="displayed-left-adjoint displayed-right-adjoint"}
Let $\cE, \cF$ be [[categories displayed over|displayed category]] $\cA,
\cB$, resp.  Furthermore, let $L : \cA \to \cB$ and $R : \cB \to \cA$ be
a pair of adjoint functors. We say 2 [[displayed functors]] $L', R'$ over
$L$ and $R$ resp. are **displayed adjoint functors** if we have
displayed natural transformations $\eta' : \mathrm{Id} \to R' \circ L'$
and $\eps' : L' \circ R' \to \mathrm{Id}$ displayed over the unit
and counit of the adjunction in the base that satisfy the usual triangle
identities.
:::

~~~{.quiver}
\[\begin{tikzcd}
	{\mathcal E} && {\mathcal F} \\
	\\
	\mathcal A && \mathcal B
	\arrow["{\mathbf{L}}", curve={height=-12pt}, from=1-1, to=1-3]
	\arrow["{\mathbf R}", curve={height=-12pt}, from=1-3, to=1-1]
	\arrow[category over, from=1-1, to=3-1]
	\arrow[category over, from=1-3, to=3-3]
        	\arrow["{L}", curve={height=-12pt}, from=3-1, to=3-3]
	\arrow["{R}", curve={height=-12pt}, from=3-3, to=3-1]
\end{tikzcd}\]
~~~

<!--
```agda
adj-level' 
  : ∀ {oa ℓa ob ℓb oe ℓe of ℓf}
    {A : Precategory oa ℓa} {B : Precategory ob ℓb}
    (ℰ : Displayed A oe ℓe) (ℱ : Displayed B of ℓf) 
  → Level
adj-level' {oa} {ℓa} {ob} {ℓb} {oe} {ℓe} {of} {ℓf} _ _ =
  oa ⊔ ℓa ⊔ ob ⊔ ℓb ⊔ oe ⊔ ℓe ⊔ of ⊔ ℓf

module _
  {oa ℓa ob ℓb oe ℓe of ℓf}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {ℰ : Displayed A oe ℓe} {ℱ : Displayed B of ℓf}
  {L : Functor A B} {R : Functor B A}
  where
  private
    module ℰ = Displayed ℰ
    module ℱ = Displayed ℱ
    open Displayed-functor

    lvl : Level
    lvl = adj-level' ℰ ℱ

  infix 15 _⊣[_]_
```
-->

```agda
  record _⊣[_]_
    (L' : Displayed-functor L ℰ ℱ)
    (adj : L ⊣ R)
    (R' : Displayed-functor R ℱ ℰ)
    : Type lvl where
    no-eta-equality
    open _⊣_ adj
    field
      unit' : Id' =[ unit ]=> R' F∘' L'
      counit' : L' F∘' R' =[ counit ]=> Id'

    module unit' = _=[_]=>_ unit'
    module counit' = _=[_]=>_ counit' renaming (η' to ε')

    field
      zig' : ∀ {x} {x' : ℰ.Ob[ x ]}
          → (counit'.ε' (L' .F₀' x') ℱ.∘' L' .F₁' (unit'.η' x')) ℱ.≡[ zig ] ℱ.id'
      zag' : ∀ {x} {x' : ℱ.Ob[ x ]}
          → (R' .F₁' (counit'.ε' x') ℰ.∘' unit'.η' (R' .F₀' x')) ℰ.≡[ zag ] ℰ.id'
```

## Fibred adjunctions {defines="fibred-adjunction fibred-left-adjoint fibred-right-adjoint"}

Let $\cE$ and $\cF$ be categories displayed over some $\cB$.  We say
that a pair of vertical [[fibred functors]] $L : \cE \to \cF$, $R : \cF
\to cF$ are **fibred adjoint functors** if they are displayed adjoint
functors, and the unit and counit are vertical natural transformations.

Unlike vertical functors and vertical natural transformations, we have to
define fibred adjunctions as a separate type: general displayed adjunctions
use composition of displayed functors for the unit and counit, whereas fibred
adjunctions use vertical composition instead.

<!--
```agda
module _
  {ob ℓb oe ℓe of ℓf}
  {B : Precategory ob ℓb}
  {ℰ : Displayed B oe ℓe}
  {ℱ : Displayed B of ℓf}
  where
  private
    open Precategory B
    module ℰ = Displayed ℰ
    module ℱ = Displayed ℱ
    open Vertical-functor

    lvl : Level
    lvl = adj-level' ℰ ℱ

  infix 15 _⊣↓_
```
-->

```agda
  record _⊣↓_
    (L : Vertical-functor ℰ ℱ)
    (R : Vertical-functor ℱ ℰ)
    : Type lvl where
    no-eta-equality
    field
      unit' : Id' =>↓ R ∘V L
      counit' : L ∘V R =>↓ Id'

    module unit' = _=>↓_ unit'
    module counit' = _=>↓_ counit' renaming (η' to ε')

    field
      zig' : ∀ {x} {x' : ℰ.Ob[ x ]}
           → counit'.ε' (L .F₀' x') ℱ.∘' L .F₁' (unit'.η' x') ℱ.≡[ idl id ] ℱ.id'
      zag' : ∀ {x} {x' : ℱ.Ob[ x ]}
           → R .F₁' (counit'.ε' x') ℰ.∘' unit'.η' (R .F₀' x') ℰ.≡[ idl id ] ℰ.id'
```
