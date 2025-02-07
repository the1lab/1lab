<!--
```agda
open import Cat.Functor.Equivalence
open import Cat.Displayed.Functor
open import Cat.Instances.Functor
open import Cat.Functor.Adjoint
open import Cat.Displayed.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Displayed.Adjoint where
```

# Displayed adjunctions

Following the general theme of defining displayed structure over
1-categorical structure, we can define a notion of displayed
[[adjoint functors]].

Let $\cE, \cF$ be [[categories displayed over|displayed category]] $\cA,
\cB$, resp.  Furthermore, let $L : \cA \to \cB$ and $R : \cB \to \cB$ be
a pair of adjoint functors. We say 2 [[displayed functors]] $L', R'$ over
$L$ and $R$ resp. are **displayed adjoint functors** if we have
displayed natural transformations $\eta' : \mathrm{Id} \to R' \circ L'$
and $\eps' : L' \circ R' \to \mathrm{Id}$ displayed over the unit
and counit of the adjunction in the base that satisfy the usual triangle
identities.

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
    lvl = oa ⊔ ℓa ⊔ ob ⊔ ℓb ⊔ oe ⊔ ℓe ⊔ of ⊔ ℓf

  infix 15 _⊣[_]_
```
-->

```agda
  record _⊣[_]_
    (L' : Displayed-functor ℰ ℱ L)
    (adj : L ⊣ R)
    (R' : Displayed-functor ℱ ℰ R )
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
    open Vertical-fibred-functor

    lvl : Level
    lvl = ob ⊔ ℓb ⊔ oe ⊔ ℓe ⊔ of ⊔ ℓf

  infix 15 _⊣↓_
```
-->

```agda
  record _⊣↓_
    (L : Vertical-fibred-functor ℰ ℱ)
    (R : Vertical-fibred-functor ℱ ℰ)
    : Type lvl where
    no-eta-equality
    field
      unit' : IdVf =>f↓ R Vf∘ L
      counit' : L Vf∘ R =>f↓ IdVf

    module unit' = _=>↓_ unit'
    module counit' = _=>↓_ counit' renaming (η' to ε')

    field
      zig' : ∀ {x} {x' : ℰ.Ob[ x ]}
           → counit'.ε' (L .F₀' x') ℱ.∘' L .F₁' (unit'.η' x') ℱ.≡[ idl id ] ℱ.id'
      zag' : ∀ {x} {x' : ℱ.Ob[ x ]}
           → R .F₁' (counit'.ε' x') ℰ.∘' unit'.η' (R .F₀' x') ℰ.≡[ idl id ] ℰ.id'
```
