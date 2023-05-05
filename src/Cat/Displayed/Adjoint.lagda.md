<!--
```agda
open import Cat.Displayed.Base
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cocartesian
open import Cat.Displayed.Fibre
open import Cat.Displayed.Functor

open import Cat.Functor.Adjoint
open import Cat.Functor.Equivalence
open import Cat.Instances.Functor
open import Cat.Prelude

import Cat.Reasoning
import Cat.Displayed.Reasoning
import Cat.Displayed.Functor.Vertical.Reasoning
```
-->

```agda
module Cat.Displayed.Adjoint where
```

# Displayed Adjunctions

Following the general theme of defining displayed structure over
1-categorical structure, we can define a notion of displayed
[adjoint functors].

[adjoint functors]: Cat.Functor.Adjoint.html

Let $\cE, \cF$ be categories displayed over $\cA, \cB$, resp.
Furthermore, let $L : \cA \to \cB$ and $R : \cB \to \cB$ be a pair of
adjoint functors. We say 2 displayed functors $L', R'$ over $L$ and $R$
resp. are **displayed adjoint functors** if we have displayed natural
transformations $\eta' : \mathrm{Id} \to R' \circ L'$ and
$\varepsilon' : L' \circ R' \to \mathrm{Id}$ displayed over the unit and
counit of the adjunction in the base that satisfy the usual triangle
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
    (L′ : Displayed-functor ℰ ℱ L)
    (adj : L ⊣ R)
    (R′ : Displayed-functor ℱ ℰ R )
    : Type lvl where
    no-eta-equality
    open _⊣_ adj
    field
      unit′ : Id′ =[ unit ]=> R′ F∘′ L′
      counit′ : L′ F∘′ R′ =[ counit ]=> Id′

    module unit′ = _=[_]=>_ unit′
    module counit′ = _=[_]=>_ counit′ renaming (η′ to ε′)

    field
      zig′ : ∀ {x} {x′ : ℰ.Ob[ x ]}
          → (counit′.ε′ (L′ .F₀′ x′) ℱ.∘′ L′ .F₁′ (unit′.η′ x′)) ℱ.≡[ zig ] ℱ.id′
      zag′ : ∀ {x} {x′ : ℱ.Ob[ x ]}
          → (R′ .F₁′ (counit′.ε′ x′) ℰ.∘′ unit′.η′ (R′ .F₀′ x′)) ℰ.≡[ zag ] ℰ.id′
```

## Fibred Adjunctions

Let $\cE$ and $\cF$ be categories displayed over some $\cB$.
We say that a pair of vertical fibred functors $L : \cE \to \cF$,
$R : \cF \to cF$ are **fibred adjoint functors** if they are displayed
adjoint functors, and the unit and counit are vertical natural
transformations.

<!--
```agda
module _
  {ob ℓb oe ℓe of ℓf}
  {B : Precategory ob ℓb}
  {ℰ : Displayed B oe ℓe}
  {ℱ : Displayed B of ℓf}
  where
  private
    open Cat.Reasoning B
    module ℱ = Cat.Displayed.Reasoning ℱ
    module ℰ = Cat.Displayed.Reasoning ℰ
    open Vertical-functor

    lvl : Level
    lvl = ob ⊔ ℓb ⊔ oe ⊔ ℓe ⊔ of ⊔ ℓf

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
      unit′ : IdV =>↓ R V∘ L
      counit′ : L V∘ R =>↓ IdV

    module unit′ = _=>↓_ unit′
    module counit′ = _=>↓_ counit′ renaming (η′ to ε′)

    field
      zig′ : ∀ {x} {x′ : ℰ.Ob[ x ]}
           → counit′.ε′ (L .F₀′ x′) ℱ.∘′ L .F₁′ (unit′.η′ x′) ℱ.≡[ idl id ] ℱ.id′
      zag′ : ∀ {x} {x′ : ℱ.Ob[ x ]}
           → R .F₁′ (counit′.ε′ x′) ℰ.∘′ unit′.η′ (R .F₀′ x′) ℰ.≡[ idl id ] ℰ.id′

  _⊣f↓_ : Vertical-fibred-functor ℰ ℱ → Vertical-fibred-functor ℱ ℰ → Type _
  L ⊣f↓ R = Vertical-fibred-functor.vert L ⊣↓ Vertical-fibred-functor.vert R
```

## Vertical Adjuncts

If $L \dashv R$ is a vertical adjunction, then we can define displayed
versions of [adjuncts]. The vertical assumption is critical here; it
allows us to keep morphisms displayed over the same base.

[adjuncts]: Cat.Functor.Adjoint.html#adjuncts

<!--
```agda
  module _ {L : Vertical-functor ℰ ℱ} {R : Vertical-functor ℱ ℰ} (adj : L ⊣↓ R) where
    private
      module L = Cat.Displayed.Functor.Vertical.Reasoning L
      module R = Cat.Displayed.Functor.Vertical.Reasoning R
      open _⊣↓_ adj
```
-->

```agda
    L-adjunct′
      : ∀ {x y x′ y′} {f : Hom x y}
      → ℱ.Hom[ f ] (L.₀′ x′) y′ → ℰ.Hom[ f ] x′ (R.₀′ y′)
    L-adjunct′ f′ = ℰ.hom[ idr _ ] (R.₁′ f′ ℰ.∘′ unit′.η′ _)

    R-adjunct′
      : ∀ {x y x′ y′} {f : Hom x y}
      → ℰ.Hom[ f ] x′ (R.₀′ y′) → ℱ.Hom[ f ] (L.₀′ x′) y′
    R-adjunct′ f′ = ℱ.hom[ idl _ ] (counit′.ε′ _ ℱ.∘′ L.₁′ f′)
```

As in the 1-categorical case, we obtain an equivalence between hom-sets
$\hom(La,b)$ and $\hom(a,Rb)$ over $f$.

```agda
    L-R-adjunct′
      : ∀ {x y} {f : Hom x y} {x′ : ℰ.Ob[ x ]} {y′ : ℱ.Ob[ y ]}
      → is-right-inverse (R-adjunct′ {x′ = x′} {y′} {f}) L-adjunct′
    L-R-adjunct′ f′ =
      ℰ.hom[] (R.₁′ (ℱ.hom[] (counit′.ε′ _ ℱ.∘′ L.₁′ f′)) ℰ.∘′ unit′.η′ _)        ≡⟨ ℰ.weave _ _ (idr _) (ap₂ ℰ._∘′_ (R.F-∘[] _ _) refl) ⟩
      ℰ.hom[] (ℰ.hom[] (R.₁′ (counit′.ε′ _) ℰ.∘′ R.₁′ (L.₁′ f′)) ℰ.∘′ unit′.η′ _) ≡⟨ ℰ.smashl _ _ ⟩
      ℰ.hom[] ((R.₁′ (counit′.ε′ _) ℰ.∘′ R.₁′ (L.₁′ f′)) ℰ.∘′ unit′.η′ _)         ≡⟨ ℰ.weave _ _ (eliml (idl _)) (ℰ.extendr[] _ (symP $ unit′.is-natural′ _ _ _)) ⟩
      ℰ.hom[] ((R.₁′ (counit′.ε′ _) ℰ.∘′ unit′.η′ _) ℰ.∘′ f′)                     ≡⟨ ℰ.shiftl _ (ℰ.eliml[] _ zag′) ⟩
      f′ ∎

    R-L-adjunct′
      : ∀ {x y} {f : Hom x y} {x′ : ℰ.Ob[ x ]} {y′ : ℱ.Ob[ y ]}
      → is-left-inverse (R-adjunct′ {x′ = x′} {y′} {f}) L-adjunct′
    R-L-adjunct′ f′ =
      ℱ.hom[] (counit′.ε′ _ ℱ.∘′ L.₁′ (ℰ.hom[] (R.₁′ f′ ℰ.∘′ unit′.η′ _)))        ≡⟨ ℱ.weave _ _ (idl _) (ap₂ ℱ._∘′_ refl (L.F-∘[] _ _)) ⟩
      ℱ.hom[] (counit′.ε′ _ ℱ.∘′ ℱ.hom[] (L.₁′ (R.₁′ f′) ℱ.∘′ L.₁′ (unit′.η′ _))) ≡⟨ ℱ.smashr _ _ ⟩
      ℱ.hom[] (counit′.ε′ _ ℱ.∘′ L.₁′ (R.₁′ f′) ℱ.∘′ L.₁′ (unit′.η′ _))           ≡⟨ ℱ.weave _ _ (elimr (idl _)) (ℱ.extendl[] _ (counit′.is-natural′ _ _ _)) ⟩
      ℱ.hom[] (f′ ℱ.∘′ counit′.ε′ _ ℱ.∘′ L.₁′ (unit′.η′ _))                       ≡⟨ ℱ.shiftl _ (ℱ.elimr[] _ zig′) ⟩
      f′ ∎
```

This equivalence is natural.

```agda
    L-adjunct-naturall′
      : ∀ {x y z} {x′ : ℰ.Ob[ x ]} {y′ : ℰ.Ob[ y ]} {z′ : ℱ.Ob[ z ]}
      → {f : Hom y z} {g : Hom x y}
      → (f′ : ℱ.Hom[ f ] (L.₀′ y′) z′) (g′ : ℰ.Hom[ g ] x′ y′)
      → L-adjunct′ (f′ ℱ.∘′ L.₁′ g′) ≡ L-adjunct′ f′ ℰ.∘′ g′
    L-adjunct-naturall′ {g = g} f′ g′ =
      ℰ.hom[] (R.₁′ (f′ ℱ.∘′ L.₁′ g′) ℰ.∘′ unit′.η′ _)        ≡⟨ ℰ.weave _ _ (idr _) (ap₂ ℰ._∘′_ R.F-∘′ refl) ⟩
      ℰ.hom[] ((R.₁′ f′ ℰ.∘′ R.₁′ (L.₁′ g′)) ℰ.∘′ unit′.η′ _) ≡⟨ ℰ.weave _ _ (ap (_∘ g) (idr _)) (ℰ.extendr[] _ (symP $ unit′.is-natural′ _ _ _)) ⟩
      ℰ.hom[] ((R.₁′ f′ ℰ.∘′ unit′.η′ _) ℰ.∘′ g′)             ≡⟨ ℰ.unwhisker-l _ _ ⟩
      ℰ.hom[] (R.₁′ f′ ℰ.∘′ unit′.η′ _) ℰ.∘′ g′ ∎

    L-adjunct-naturalr′
      : ∀ {x y z} {x′ : ℰ.Ob[ x ]} {y′ : ℱ.Ob[ y ]} {z′ : ℱ.Ob[ z ]}
      → {f : Hom y z} {g : Hom x y}
      → (f′ : ℱ.Hom[ f ] y′ z′) (g′ : ℱ.Hom[ g ] (L.₀′ x′) y′)
      → L-adjunct′ (f′ ℱ.∘′ g′) ≡ R.₁′ f′ ℰ.∘′ L-adjunct′ g′
    L-adjunct-naturalr′ {f = f} f′ g′ =
      ℰ.hom[] (R.₁′ (f′ ℱ.∘′ g′) ℰ.∘′ unit′.η′ _)    ≡⟨ ℰ.weave _ _ (ap (f ∘_) (idr _)) (ℰ.pushl[] _ R.F-∘′) ⟩
      ℰ.hom[] (R.₁′ f′ ℰ.∘′ R.₁′ g′ ℰ.∘′ unit′.η′ _) ≡⟨ ℰ.unwhisker-r _ _ ⟩
      R.₁′ f′ ℰ.∘′ ℰ.hom[] (R.₁′ g′ ℰ.∘′ unit′.η′ _) ∎

    R-adjunct-naturall′
      : ∀ {x y z} {x′ : ℰ.Ob[ x ]} {y′ : ℰ.Ob[ y ]} {z′ : ℱ.Ob[ z ]}
      → {f : Hom y z} {g : Hom x y}
      → (f′ : ℰ.Hom[ f ] y′ (R.₀′ z′)) (g′ : ℰ.Hom[ g ] x′ y′)
      → R-adjunct′ (f′ ℰ.∘′ g′) ≡ R-adjunct′ f′ ℱ.∘′ L.₁′ g′
    R-adjunct-naturall′ {g = g} f′ g′ =
      ℱ.hom[] (counit′.ε′ _ ℱ.∘′ L.₁′ (f′ ℰ.∘′ g′))       ≡⟨ ℱ.weave _ _ (ap (_∘ g) (idl _)) (ℱ.pushr[] _ L.F-∘′) ⟩
      ℱ.hom[] ((counit′.ε′ _ ℱ.∘′ L.₁′ f′) ℱ.∘′ L.F₁′ g′) ≡⟨ ℱ.unwhisker-l _ _ ⟩
      ℱ.hom[] (counit′.ε′ _ ℱ.∘′ L.₁′ f′) ℱ.∘′ L.₁′ g′ ∎

    R-adjunct-naturalr′
      : ∀ {x y z} {x′ : ℰ.Ob[ x ]} {y′ : ℱ.Ob[ y ]} {z′ : ℱ.Ob[ z ]}
      → {f : Hom y z} {g : Hom x y}
      → (f′ : ℱ.Hom[ f ] y′ z′) (g′ : ℰ.Hom[ g ] x′ (R.₀′ y′))
      → R-adjunct′ (R.₁′ f′ ℰ.∘′ g′) ≡ f′ ℱ.∘′ R-adjunct′ g′
    R-adjunct-naturalr′ {f = f} f′ g′ =
      ℱ.hom[] (counit′.ε′ _ ℱ.∘′ L.₁′ (R.₁′ f′ ℰ.∘′ g′))      ≡⟨ ℱ.weave _ _ (idl _) (ap₂ ℱ._∘′_ refl L.F-∘′) ⟩
      ℱ.hom[] (counit′.ε′ _ ℱ.∘′ L.₁′ (R.₁′ f′) ℱ.∘′ L.₁′ g′) ≡⟨ ℱ.weave _ _ (ap (f ∘_) (idl _)) (ℱ.extendl[] _ (counit′.is-natural′ _ _ _)) ⟩
      ℱ.hom[] (f′ ℱ.∘′ counit′.ε′ _ ℱ.∘′ L.₁′ g′)             ≡⟨ ℱ.unwhisker-r _ _ ⟩
      f′ ℱ.∘′ ℱ.hom[] (counit′.ε′ _ ℱ.∘′ L.₁′ g′) ∎
```

## Vertical Right Adjoints are Fibred

If $L \dashv R$ is a vertical adjunction, then $R$ is a fibred functor.

```agda
  Vert-right-adjoint-fibred
    : {L : Vertical-functor ℰ ℱ} {R : Vertical-functor ℱ ℰ}
    → L ⊣↓ R
    → is-vertical-fibred R
  Vert-right-adjoint-fibred {L = L} {R = R} adj {f = f} f′ cart = R-cart where 
    open is-cartesian
    module L = Cat.Displayed.Functor.Vertical.Reasoning L
    module R = Cat.Displayed.Functor.Vertical.Reasoning R 
```

Let $f : \cC(x,y)$ and $f' : \cF(x', y')_{f}$ be a cartesian morphism.
To show that $R$ is fibred, we need to show that $R(f')$ is cartesian.
Let $m : \cC(a, x)$, and $h' : \cE(a', y')_{f \circ m}$; we need to
construct a universal factorization of $h'$ through $R(f')$.

As $f'$ is cartesian, we can perform the following factorization of
the left adjunct $\varepsilon \circ L(h')$ of $h$, yielding a map
$\hat{h} : \cF(a', x')$.

~~~{.quiver}
\begin{tikzcd}
  {a'} \\
  & {x'} && {y'} \\
  a \\
  & y && x
  \arrow["{f'}", from=2-2, to=2-4]
  \arrow["f", from=4-2, to=4-4]
  \arrow[lies over, from=2-2, to=4-2]
  \arrow[lies over, from=2-4, to=4-4]
  \arrow["m", from=3-1, to=4-2]
  \arrow["{\varepsilon \circ L(h')}", curve={height=-12pt}, from=1-1, to=2-4]
  \arrow[lies over, from=1-1, to=3-1]
  \arrow["{f \circ m}", curve={height=-12pt}, from=3-1, to=4-4]
  \arrow["{\exists! \hat{h}}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=2-2]
\end{tikzcd}
~~~

We can then take the right adjunct $R(\hat{h}) \circ \eta$ of $\hat{h}$
to obtain the desired factorization.


```agda
    R-cart : is-cartesian ℰ f (R.F₁′ f′)
    R-cart .universal m h′ =
      L-adjunct′ adj (cart .universal m (R-adjunct′ adj h′))
```

<details>
<summary>Showing that this factorization is universal is a matter of
pushing around the adjuncts.
</summary>

```agda
    R-cart .commutes m h′ =
      R.F₁′ f′ ℰ.∘′ L-adjunct′ adj (cart .universal m (R-adjunct′ adj h′)) ≡˘⟨ L-adjunct-naturalr′ adj _ _ ⟩
      L-adjunct′ adj (f′ ℱ.∘′ cart .universal m (R-adjunct′ adj h′))       ≡⟨ ap (L-adjunct′ adj) (cart .commutes _ _) ⟩
      L-adjunct′ adj (R-adjunct′ adj h′)                                   ≡⟨ L-R-adjunct′ adj h′ ⟩
      h′ ∎
    R-cart .unique {m = m} {h′ = h′} m′ p =
      m′                                                                        ≡˘⟨ L-R-adjunct′ adj m′ ⟩
      L-adjunct′ adj (R-adjunct′ adj m′)                                        ≡⟨ ap (L-adjunct′ adj) (cart .unique _ (sym $ R-adjunct-naturalr′ adj _ _)) ⟩
      L-adjunct′ adj (cart .universal m (R-adjunct′ adj ⌜ R .F₁′ f′ ℰ.∘′ m′ ⌝)) ≡⟨ ap! p ⟩
      L-adjunct′ adj (cart .universal m (R-adjunct′ adj h′))                    ∎
```
</details>

Dually, vertical left adjoints are opfibred.

```agda
  Vert-left-adjoint-opfibred
    : {L : Vertical-functor ℰ ℱ} {R : Vertical-functor ℱ ℰ}
    → L ⊣↓ R
    → is-vertical-opfibred L
```

<details>
<summary>The proof is entirely dual to the one for right adjoints.
</summary>
```agda
  Vert-left-adjoint-opfibred {L = L} {R = R} adj {f = f} f′ cocart = L-cocart where
    open is-cocartesian
    module L = Cat.Displayed.Functor.Vertical.Reasoning L
    module R = Cat.Displayed.Functor.Vertical.Reasoning R

    L-cocart : is-cocartesian ℱ f (L.F₁′ f′)
    L-cocart .universal m h′ =
      R-adjunct′ adj (cocart .universal m (L-adjunct′ adj h′))
    L-cocart .commutes m h′ =
      R-adjunct′ adj (cocart .universal m (L-adjunct′ adj h′)) ℱ.∘′ L.F₁′ f′ ≡˘⟨ R-adjunct-naturall′ adj _ _ ⟩
      R-adjunct′ adj (cocart .universal m (L-adjunct′ adj h′) ℰ.∘′ f′)       ≡⟨ ap (R-adjunct′ adj) (cocart .commutes _ _) ⟩
      R-adjunct′ adj (L-adjunct′ adj h′)                                     ≡⟨ R-L-adjunct′ adj h′ ⟩
      h′ ∎
    L-cocart .unique {m = m} {h′ = h′} m′ p =
      m′ ≡˘⟨ R-L-adjunct′ adj m′ ⟩
      R-adjunct′ adj (L-adjunct′ adj m′)                                          ≡⟨ ap (R-adjunct′ adj) (cocart .unique _ (sym $ L-adjunct-naturall′ adj _ _)) ⟩
      R-adjunct′ adj (cocart .universal m (L-adjunct′ adj ⌜ m′ ℱ.∘′ L .F₁′ f′ ⌝)) ≡⟨ ap! p ⟩
      R-adjunct′ adj (cocart .universal m (L-adjunct′ adj h′))                    ∎
```
</details>


## Adjunctions between Fibre Categories

Vertical adjunctions yield adjunctions between fibre categories.

```agda
  vertical-adjunction→fibre-adjunction
    : ∀ {L : Vertical-functor ℰ ℱ} {R : Vertical-functor ℱ ℰ}
    → L ⊣↓ R
    → ∀ x → Restrict↓ L x ⊣ Restrict↓ R x
  vertical-adjunction→fibre-adjunction {L = L} {R = R} vadj x = adj where
    open _⊣↓_ vadj
    open _⊣_
    open _=>_
    open _=>↓_

    adj : Restrict↓ L x ⊣ Restrict↓ R x
    adj .unit .η x = unit′ .η′ x
    adj .unit .is-natural x′ y′ f′ =
      Vert-nat-restrict {F′ = IdV} {G′ = R V∘ L} unit′ x .is-natural x′ y′ f′ 
    adj .counit .η x = counit′ .η′ x
    adj .counit .is-natural x′ y′ f′ =
      Vert-nat-restrict {F′ = L V∘ R} {G′ = IdV} counit′ x .is-natural x′ y′ f′ 
    adj .zig = from-pathp zig′
    adj .zag = from-pathp zag′
```

