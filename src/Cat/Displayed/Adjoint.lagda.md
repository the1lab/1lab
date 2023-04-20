```agda
open import Cat.Displayed.NaturalTransformation
open import Cat.Functor.Equivalence
open import Cat.Displayed.Functor
open import Cat.Instances.Functor
open import Cat.Functor.Adjoint
open import Cat.Displayed.Base
open import Cat.Prelude

module Cat.Displayed.Adjoint where
```

# Displayed Adjunction

One can adapt the concept of [adjoint functors][adj] and can define
displayed adjoint functors following the same pattern:

[adj]: Cat.Functor.Adjoint.html

Given [displayed categories][disc] $\cE$, $\cF$ over the base
categories $\cA$, resp. $\cB$ and a [displayed functor][disf] $\mathbf{L} : \cE \to \cF$
we call $\mathbf{R} : \cF \to \cE$ a **displayed right adjoint** of $L$

[disc]: Cat.Displayed.Base.html

if we have [displayed natural transformations][disnat]
$\bf{\eta} : \mathrm{id}_\cE \To \mathbf{R} \mathbf{L}$ and
$\bf{\epsilon} : \mathbf{L} \mathbf{R} \To \mathrm{id}_\cF$ 
called unit and counit, satisfying the usual triangular identities
$\mathbf{R} \mathbf{\epsilon} \circ \mathbf{\eta} \mathbf{R} = \mathrm{id}$
and $\mathbf{\epsilon} \mathbf{L} \circ \mathbf{L} \mathbf{\eta} = mathrm{id}$.

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

```agda
module
  _ {o ℓ o₂ ℓ₂ o′ ℓ′ o₂′ ℓ₂′}
    {A : Precategory o ℓ}
    {B : Precategory o₂ ℓ₂}
    {ℰ : Displayed A o′ ℓ′}
    {ℱ : Displayed B o₂′ ℓ₂′}
  where
  private
    lvl : Level
    lvl = o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ o₂ ⊔ ℓ₂ ⊔  o₂′ ⊔ ℓ₂′

  record _⊣[_]_ {L : Functor A B} {R : Functor B A} (L′ : Displayed-functor ℰ ℱ L)
                       (adj : L ⊣ R) (R′ : Displayed-functor ℱ ℰ R ) : Type lvl where
    private
      module ℰ = Displayed ℰ
      module ℱ = Displayed ℱ
      module L′ = Displayed-functor L′
      module R′ = Displayed-functor R′
      module adj = _⊣_ adj
      
    field
      unit′ : Id′ =>[ adj.unit ] (R′ F∘′ L′)
      counit′ : (L′ F∘′ R′) =>[ adj.counit ] Id′

    module unit′ = _=>[_]_ unit′
    module counit′ = _=>[_]_ counit′ renaming (η′ to ε′)

    field
      zig′ : ∀ {x} {x′ : ℰ.Ob[ x ]}
           → PathP (λ i → ℱ.Hom[ adj.zig i ] (L′.₀′ x′) (L′.₀′ x′))
                        (counit′.ε′ (L′.₀′ x′) ℱ.∘′ L′.₁′ (unit′.η′ x′)) ℱ.id′
      zag′ : ∀ {y} {y′ : ℱ.Ob[ y ]}
            → PathP (λ i → ℰ.Hom[ adj.zag i ] (R′.₀′ y′) (R′.₀′ y′))
                         (R′.₁′ (counit′.ε′ y′) ℰ.∘′ unit′.η′ (R′.₀′ y′)) ℰ.id′
```

If $\cE$ and $\cF$ are over the same base category $\cB$
$\mathbf{L} : \cE \to \cF$, we say a pair of fibred functors 
$\mathbf{R} : \cF \to \cE, \mathbf{L} : \cE \to \cF$
form a **fibred adjoint functor pair** if $\mathbf{L}$ and
$\mathbf{R}$ are displayed adjoint
and unit and counit are [vertical natural transformations][disnat].
$\mathbf{L} : \cE \to \cF$ and $\mathbf{R} : \cF \to \cE$
form a **fibred adjoint functor pair** if $\mathbf{L}$ and
$\mathbf{R}$ are [fibred functors][disf], they are displayed adjoint
and unit and counit are [vertical natural transformations][disnat].

[disf]: Cat.Displayed.Functor.html
[disnat]: Cat.Displayed.NaturalTransformation.html

~~~{.quiver}
\[\begin{tikzcd}
	{\mathcal E} && {\mathcal F} \\
	\\
	& \mathcal B
	\arrow["{\mathbf{L}}", curve={height=-12pt}, from=1-1, to=1-3]
	\arrow["{\mathbf R}", curve={height=-12pt}, from=1-3, to=1-1]
	\arrow[category over, from=1-1, to=3-2]
	\arrow[category over, from=1-3, to=3-2]
\end{tikzcd}\]
~~~

```agda
module
  _ {o ℓ o′ ℓ′ o′′ ℓ′′}
    {B : Precategory o ℓ}
    {ℰ : Displayed B o′ ℓ′}
    {ℱ : Displayed B o′′ ℓ′′}
  where
  private
    module B = Precategory B
    module ℰ = Displayed ℰ
    module ℱ = Displayed ℱ

    lvl : Level
    lvl = o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ o′′ ⊔ ℓ′′

  record _⊣′_ (L : Fibred-functor-single-base ℰ ℱ)
                   (R : Fibred-functor-single-base ℱ ℰ) : Type lvl where
    private
      module L = Fibred-functor-single-base L
      module R = Fibred-functor-single-base R

    field
      unit′ : Id′′-is-fibred =>′ (R fibred-F∘′′ L)
      counit′ : (L fibred-F∘′′ R) =>′ Id′′-is-fibred

    module unit′ = _=>′_ unit′
    module counit′ = _=>′_ counit′ renaming (η′ to ε′)

    field
      zig′ : ∀ {x} {x′ : ℰ.Ob[ x ]}
           → PathP (λ i → ℱ.Hom[ B.idl B.id i ] (L.₀′ x′) (L.₀′ x′))
                        (counit′.ε′ (L.₀′ x′) ℱ.∘′ L.₁′ (unit′.η′ x′)) ℱ.id′
      zag′ : ∀ {y} {y′ : ℱ.Ob[ y ]}
            → PathP (λ i → ℰ.Hom[ B.idl B.id i ] (R.₀′ y′) (R.₀′ y′))
                         (R.₁′ (counit′.ε′ y′) ℰ.∘′ unit′.η′ (R.₀′ y′)) ℰ.id′

  infixr 15 _⊣′_
```
