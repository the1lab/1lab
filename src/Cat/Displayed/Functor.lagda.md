<!--
```agda
open import Cat.Instances.Functor
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Displayed.Cartesian
import Cat.Displayed.Reasoning as DR
import Cat.Functor.Reasoning as FR
import Cat.Reasoning as CR
```
-->

```agda
module Cat.Displayed.Functor where
```

# Displayed and fibred functors {defines=displayed-functor}

If you have a pair of categories $\cE, \cF$ [[displayed over|displayed
category]] a common base [[category]] $\cB$, it makes immediate sense to
talk about [[functors]] $F : \cE \to \cF$: you'd have an assignment of
objects $F_x : \cE^*(x) \to \cF^*(x)$ and an assignment of morphisms

$$
F_{a,b,f} : (a' \to_f b') \to (F_a(a') \to_f F_b(b'))\text{,}
$$

which makes sense because $F_a(a')$ lies over $a$, just as $a'$ did,
that a morphism $F_a(a') \to F_b(b')$ is allowed to lie over a morphism
$f : a \to b$. But, in the spirit of relativising category theory, it
makes more sense to consider functors between categories displayed over
_different_ bases, as in

~~~{.quiver}
\[\begin{tikzcd}
  {\mathcal{E}} && {\mathcal{F}} \\
  \\
  {\mathcal{A}} && {\mathcal{B}\text{,}}
  \arrow["{\mathbf{F}}", from=1-1, to=1-3]
  \arrow["{F}"', from=3-1, to=3-3]
  \arrow[category over, from=1-3, to=3-3]
  \arrow[category over, from=1-1, to=3-1]
\end{tikzcd}\]
~~~

with our displayed functor $\bf{F} : \cE \to \cF$ lying over an
ordinary functor $F : \cA \to \cB$ to mediate between the bases.

<!--
```agda
module
  _ {oa ℓa ob ℓb oe ℓe of ℓf}
    {A : Precategory oa ℓa}
    {B : Precategory ob ℓb}
    (F : Functor A B)
    (ℰ : Displayed A oe ℓe)
    (ℱ : Displayed B of ℓf)
  where
  private
    module F = FR F
    module A = CR A
    module B = CR B
    module ℰ where
      open Displayed ℰ public
      open DR ℰ public
    module ℱ where
      open Displayed ℱ public
      open DR ℱ public
```
-->

```agda
  record Displayed-functor : Type (oa ⊔ ℓa ⊔ oe ⊔ ℓe ⊔ of ⊔ ℓf) where
    no-eta-equality
    field
      F₀' : ∀ {x} (x' : ℰ.Ob[ x ]) → ℱ.Ob[ F.₀ x ]
      F₁'
        : ∀ {a b} {f : A.Hom a b} {a' b'}
        → ℰ.Hom[ f ] a' b' → ℱ.Hom[ F.₁ f ] (F₀' a') (F₀' b')
```

In order to state the displayed functoriality laws, we require
functoriality for our mediating functor $F$. Functors between categories
displayed over the same base can be recovered as the "vertical displayed
functors", i.e., those lying over the identity functor.

```agda
      F-id'
        : ∀ {x} {x' : ℰ.Ob[ x ]}
        → F₁' (ℰ.id' {x} {x'}) ℱ.≡[ F.F-id ] (ℱ.id' {F.₀ x} {F₀' x'})
      F-∘'
        : ∀ {a b c} {f : A.Hom b c} {g : A.Hom a b} {a' b' c'}
        → {f' : ℰ.Hom[ f ] b' c'} {g' : ℰ.Hom[ g ] a' b'}
        → F₁' (f' ℰ.∘' g') ℱ.≡[ F.F-∘ f g ] (F₁' f' ℱ.∘' F₁' g')

    ₀' = F₀'
    ₁' = F₁'
```

<!--
```agda
module
  _ {oa ℓa ob ℓb oe ℓe of ℓf}
    {A : Precategory oa ℓa}
    {B : Precategory ob ℓb}
    {ℰ : Displayed A oe ℓe}
    {ℱ : Displayed B of ℓf}
  where
  private
    module A = Precategory A
    module B = Precategory B
    module ℰ = Displayed ℰ
    module ℱ = Displayed ℱ

  open Functor
  open Displayed-functor
  private unquoteDecl eqv = declare-record-iso eqv (quote Displayed-functor)

  Displayed-functor-pathp
    : {F G : Functor A B}
    → {F' : Displayed-functor F ℰ ℱ} {G' : Displayed-functor G ℰ ℱ}
    → (p : F ≡ G)
    → (q0 : ∀ {x} → (x' : ℰ.Ob[ x ]) → PathP (λ i → ℱ.Ob[ p i .F₀ x ]) (F' .F₀' x') (G' .F₀' x'))
    → (q1 : ∀ {x y x' y'} {f : A.Hom x y} → (f' : ℰ.Hom[ f ] x' y')
            → PathP (λ i → ℱ.Hom[ p i .F₁ f ] (q0 x' i) (q0 y' i)) (F' .F₁' f') (G' .F₁' f'))
    → PathP (λ i → Displayed-functor (p i) ℰ ℱ) F' G'
  Displayed-functor-pathp {F = F} {F' = F'} {G' = G'} p q0 q1 = dfn where
    -- We need to define this directly to get nice definitional behavior on the projections
    dfn : PathP (λ i → Displayed-functor (p i) ℰ ℱ) F' G'
    dfn i .F₀' x' = q0 x' i
    dfn i .F₁' f' = q1 f' i
    dfn i .F-id' {x' = x'} j = 
      is-set→squarep (λ i j → ℱ.Hom[ F-id (p i) j ]-set (q0 x' i) (q0 x' i)) 
        (q1 ℰ.id') (F-id' F') (F-id' G') (λ _ → ℱ.id') i j
    dfn i .F-∘' {f = f} {g = g} {a' = a'} {c' = c'} {f' = f'} {g' = g'} j = 
      is-set→squarep (λ i j → ℱ.Hom[ F-∘ (p i) f g j ]-set (q0 a' i) (q0 c' i))
        (q1 (f' ℰ.∘' g')) (F-∘' F') (F-∘' G') (λ k → q1 f' k ℱ.∘' q1 g' k) i j

  Displayed-functor-is-set : {F : Functor A B} → (∀ x → is-set ℱ.Ob[ x ]) → is-set (Displayed-functor F ℰ ℱ)
  Displayed-functor-is-set fibre-set = Iso→is-hlevel! 2 eqv where instance
    ℱOb[] : ∀ {x} → H-Level (ℱ.Ob[ x ]) 2
    ℱOb[] = hlevel-instance (fibre-set _)

  instance
    Funlike-displayed-functor : ∀ {F : Functor A B} {x} → Funlike (Displayed-functor F ℰ ℱ) (⌞ ℰ.Ob[ x ] ⌟) λ _ → ⌞ ℱ.Ob[ F .F₀ x ] ⌟
    Funlike-displayed-functor = record { _·_ = λ F x → F .F₀' x }
```
-->

:::{.definition #fibred-functor}
Note that, if $\cE$ and $\cF$ are [[fibred categories]] over their bases
(rather than just _displayed_ categories), then the appropriate notion
of 1-cell are displayed functors that take [[cartesian morphisms]] to
cartesian morphisms.
:::

<!--
```agda
module
  _ {oa ℓa ob ℓb oe ℓe of ℓf}
    {A : Precategory oa ℓa}
    {B : Precategory ob ℓb}
    {ℰ : Displayed A oe ℓe}
    {ℱ : Displayed B of ℓf}
    {F : Functor A B}
  where
  private
    module F = Functor F
    module A = CR A
    module B = CR B
    module ℰ where
      open Displayed ℰ public
      open Cat.Displayed.Cartesian ℰ public
    module ℱ where
      open Displayed ℱ public
      open Cat.Displayed.Cartesian ℱ public

    lvl : Level
    lvl = oa ⊔ ℓa ⊔ ob ⊔ ℓb ⊔ oe ⊔ ℓe ⊔ of ⊔ ℓf
```
-->

```agda
  record is-fibred-functor (F' : Displayed-functor F ℰ ℱ) : Type lvl where
    no-eta-equality
    open Displayed-functor F'
    field
      F-cartesian
        : ∀ {a b a' b'} {f : A.Hom a b} {f' : ℰ.Hom[ f ] a' b'}
        → ℰ.is-cartesian f f'
        → ℱ.is-cartesian (F.₁ f) (F₁' f')
```

<!--
```agda
  instance
    H-Level-is-fibred-functor
      : ∀ {F' : Displayed-functor F ℰ ℱ}
      → {n : Nat}
      → H-Level (is-fibred-functor F') (suc n)
    H-Level-is-fibred-functor {n = n} =
      hlevel-instance (Iso→is-hlevel (suc n) eqv (hlevel (suc n)))
      where
        unquoteDecl eqv = declare-record-iso eqv (quote is-fibred-functor)
        open ℱ -- Needed for the is-cartesian H-Level instances.
```
-->

One can also define the composition of displayed functors,
which lies over the composition of the underlying functors.

<!--
```agda
module
  _ {oa ℓa ob ℓb oc ℓc oe ℓe of ℓf oh ℓh}
    {A : Precategory oa ℓa}
    {B : Precategory ob ℓb}
    {C : Precategory oc ℓc}
    {ℰ : Displayed A oe ℓe}
    {ℱ : Displayed B of ℓf}
    {ℋ : Displayed C oh ℓh}
    {F : Functor B C} {G : Functor A B}
  where
  private
    module A = Precategory A
    module B = Precategory B
    module ℰ = Displayed ℰ
    module ℱ = Displayed ℱ
    module ℋ where
      open Displayed ℋ public
      open DR ℋ public
    module F = Functor F
    module G = Functor G

    open DR ℋ
    open Displayed-functor
    open is-fibred-functor

  infixr 30 _F∘'_
```
-->

```agda
  _F∘'_
    : Displayed-functor F ℱ ℋ
    → Displayed-functor G ℰ ℱ
    → Displayed-functor (F F∘ G) ℰ ℋ
  (F' F∘' G') .F₀' x = F' .F₀' (G' .F₀' x)
  (F' F∘' G') .F₁' f = F' .F₁' (G' .F₁' f)
  (F' F∘' G') .F-id' =
    ℋ.cast[] $
      F' .F₁' (G' .F₁' ℰ.id') ℋ.≡[]⟨ apd (λ i → F' .F₁') (G' .F-id') ⟩
      F' .F₁' ℱ.id'            ℋ.≡[]⟨ F' .F-id' ⟩
      ℋ.id'                   ∎
  (F' F∘' G') .F-∘' {f = f} {g = g} {f' = f'} {g' = g'} =
    ℋ.cast[] $
      F' .F₁' (G' .F₁' (f' ℰ.∘' g'))                   ℋ.≡[]⟨ apd (λ i → F' .F₁') (G' .F-∘') ⟩
      F₁' F' (G' .F₁' f' ℱ.∘' G' .F₁' g')              ℋ.≡[]⟨ F' .F-∘' ⟩
      (F' .F₁' (G' .F₁' f') ℋ.∘' F' .F₁' (G' .F₁' g')) ∎
```

The composite of two fibred functors is a fibred functor.

```agda
  F∘'-fibred
    : ∀ {F' : Displayed-functor F ℱ ℋ} {G' : Displayed-functor G ℰ ℱ}
    → is-fibred-functor F' → is-fibred-functor G'
    → is-fibred-functor (F' F∘' G')
  F∘'-fibred F'-fibred G'-fibred .F-cartesian f'-cart =
    F'-fibred .F-cartesian (G'-fibred .F-cartesian f'-cart)
```

Furthermore, there is a displayed identity functor that lies over
the identity functor.

<!--
```agda
module _
  {ob ℓb oe ℓe}
  {B : Precategory ob ℓb}
  {ℰ : Displayed B oe ℓe}
  where
  open Displayed-functor
  open is-fibred-functor
```
-->

```agda
  Id' : Displayed-functor Id ℰ ℰ
  Id' .F₀' x = x
  Id' .F₁' f = f
  Id' .F-id' = refl
  Id' .F-∘'  = refl
```

The identity functor is obviously fibred.

```agda
  Id'-fibred : is-fibred-functor Id'
  Id'-fibred .F-cartesian f'-cart = f'-cart
```

## Vertical functors {defines="vertical-functor"}

Functors displayed over the identity functor are of particular interest.
Such functors are known as **vertical functors**, and are commonly used
to define fibrewise structure. However, they are somewhat difficult to
work with if we define them directly as such, as the composite of two
identity functors is not **definitionally** equal to the identity functor!
To avoid this problem, we provide the following specialized definition.

<!--
```agda
module
  _ {o ℓ o' ℓ' o'' ℓ''}
    {B : Precategory o ℓ}
    (ℰ : Displayed B o' ℓ')
    (ℱ : Displayed B o'' ℓ'')
  where
  private
    module B = Precategory B
    module ℰ = Displayed ℰ
    module ℱ = Displayed ℱ
    module F = DR ℱ using (hom[])
    module ℰ↓ {x} = Precategory (Fibre ℰ x) using (_∘_)
    module ℱ↓ {x} = Precategory (Fibre ℱ x) using (_∘_)
```
-->

```agda
  Vertical-functor : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ' ⊔ o'' ⊔ ℓ'')
  Vertical-functor = Displayed-functor Id ℰ ℱ
```

As promised, composition of vertical functors is much simpler.

<!--
```agda
module _
  {ob ℓb oe ℓe of ℓf oh ℓh}
  {B : Precategory ob ℓb}
  {ℰ : Displayed B oe ℓe}
  {ℱ : Displayed B of ℓf}
  {ℋ : Displayed B oh ℓh}
  where
  open Displayed-functor
  open is-fibred-functor

  infixr 30 _∘V_
```
-->

```agda
  _∘V_ : Vertical-functor ℱ ℋ → Vertical-functor ℰ ℱ → Vertical-functor ℰ ℋ
  (F' ∘V G') .F₀' x' = F' .F₀' (G' .F₀' x')
  (F' ∘V G') .F₁' f' = F' .F₁' (G' .F₁' f')
  (F' ∘V G') .F-id' = ap (F' .F₁') (G' .F-id') ∙ F' .F-id'
  (F' ∘V G') .F-∘' = ap (F' .F₁') (G' .F-∘') ∙ (F' .F-∘')
```

General and vertical composition of vertical functors definitionnally agree on
both the actions on objects and morphisms: the only difference is in how the
result is indexed.

```agda
  F∘'-∘V-pathp
    : ∀ {F' : Vertical-functor ℱ ℋ} {G' : Vertical-functor ℰ ℱ}
    → PathP (λ i → Displayed-functor (F∘-id2 i) ℰ ℋ) (F' F∘' G') (F' ∘V G')
  F∘'-∘V-pathp =
    Displayed-functor-pathp (λ i → F∘-id2 i)
      (λ x' → refl)
      (λ f' → refl)
```

As such, the composite of vertical fibred functors is also fibred.

```agda
  ∘V-fibred
    : ∀ {F' : Vertical-functor ℱ ℋ} {G' : Vertical-functor ℰ ℱ}
    → is-fibred-functor F' → is-fibred-functor G' → is-fibred-functor (F' ∘V G')
  ∘V-fibred F'-fib G'-fib .F-cartesian cart =
    F'-fib .F-cartesian (G'-fib .F-cartesian cart)
```

<!--
```agda
module
  _ {o ℓ o' ℓ' o'' ℓ''}
    {B : Precategory o ℓ}
    {ℰ : Displayed B o' ℓ'}
    {ℱ : Displayed B o'' ℓ''}
  where
  private
    module B = Precategory B
    module ℰ where
      open Displayed ℰ public
      open DR ℰ public
    module ℱ where
      open Displayed ℱ public
      open DR ℱ public

    module ℰ↓ {x} = Precategory (Fibre ℰ x) using (_∘_)
    module ℱ↓ {x} = Precategory (Fibre ℱ x) using (_∘_)

  module Vertical-functor (F : Vertical-functor ℰ ℱ) where
    open Displayed-functor F public

    abstract
      F-∘↓
        : ∀ {x} {a b c : ℰ.Ob[ x ]} {f : ℰ.Hom[ B.id ] b c} {g : ℰ.Hom[ B.id ] a b}
        → F₁' (f ℰ↓.∘ g) ≡ F₁' f ℱ↓.∘ F₁' g
      F-∘↓ = ℱ.cast[] (apd (λ i → F₁') (ℰ.unwrap _) ℱ.∙[] F-∘' ℱ.∙[] ℱ.wrap _)

  open Vertical-functor

  Vertical-functor-path
    : {F G : Vertical-functor ℰ ℱ}
    → (p0 : ∀ {x} → (x' : ℰ.Ob[ x ]) → F .F₀' x' ≡ G .F₀' x')
    → (p1 : ∀ {x y x' y'} {f : B.Hom x y} → (f' : ℰ.Hom[ f ] x' y')
            → PathP (λ i → ℱ.Hom[ f ] (p0 x' i) (p0 y' i)) (F .F₁' f') (G .F₁' f'))
    → F ≡ G
  Vertical-functor-path = Displayed-functor-pathp refl

  Vertical-functor-path-prop
    : {F G : Vertical-functor ℰ ℱ}
    → (∀ {x y x' y'} {f : B.Hom x y} → is-prop (ℱ.Hom[ f ] x' y'))
    → (p0 : ∀ {x} → (x' : ℰ.Ob[ x ]) → F .F₀' x' ≡ G .F₀' x')
    → F ≡ G
  Vertical-functor-path-prop prop p0 = Vertical-functor-path p0 (λ _ → is-prop→pathp (λ _ → prop) _ _)

  Vertical-functor-path-prop! 
    : {F G : Vertical-functor ℰ ℱ}
    → ⦃ _ : ∀ {x y x' y'} {f : B.Hom x y} → H-Level (ℱ.Hom[ f ] x' y') 1 ⦄ 
    → (p0 : ∀ {x} → (x' : ℰ.Ob[ x ]) → F .F₀' x' ≡ G .F₀' x')
    → F ≡ G
  Vertical-functor-path-prop! = Vertical-functor-path-prop (hlevel 1)
  
  Vertical-functor-is-set : (∀ x → is-set ℱ.Ob[ x ]) → is-set (Vertical-functor ℰ ℱ)
  Vertical-functor-is-set fibre-set = Displayed-functor-is-set fibre-set
```
-->

## Displayed natural transformations

Just like we have defined a displayed functor
$\bf{F} : \cE \to \cF$ lying over an ordinary functor $F : \cA \to \cB$
we can define a displayed natural transformation.
Assume $\bf{F}, \bf{G} : \cE \to \cF$ are displayed functors
over $F : \cA \to \cB$ resp. $G : \cA \to \cB$ and we have a
natural transformation $\eta : F \To G$. Than one can define a
**displayed natural transformation** $\bf{\eta} : \bf{F} \To \bf{G}$
lying over $\eta$.

~~~{.quiver}
\[\begin{tikzcd}
	{\mathcal E} && {\mathcal F} \\
	\\
	\mathcal A && \mathcal B
	\arrow[""{name=0, anchor=center, inner sep=0}, "{\mathbf{F}}", curve={height=-12pt}, from=1-1, to=1-3]
	\arrow[""{name=1, anchor=center, inner sep=0}, "{\mathbf{G}}"', curve={height=12pt}, from=1-1, to=1-3]
	\arrow[""{name=2, anchor=center, inner sep=0}, "F", curve={height=-12pt}, from=3-1, to=3-3]
	\arrow[""{name=3, anchor=center, inner sep=0}, "G"', curve={height=12pt}, from=3-1, to=3-3]
  \arrow[category over, from=1-1, to=3-1]
	\arrow[category over, from=1-3, to=3-3]
	\arrow["\eta", shorten <=3pt, shorten >=3pt, Rightarrow, from=2, to=3]
	\arrow["{\eta^\prime}", shorten <=3pt, shorten >=3pt, Rightarrow, from=0, to=1]
\end{tikzcd}\]
~~~

<!--
```agda
module
  _ {o ℓ o' ℓ' o₂ ℓ₂ o₂' ℓ₂'}
    {A : Precategory o ℓ}
    {B : Precategory o₂ ℓ₂}
    {ℰ : Displayed A o' ℓ'}
    {ℱ : Displayed B o₂' ℓ₂'}
  where
  private
    module A = CR A
    module ℰ = Displayed ℰ
    module ℱ = Displayed ℱ
    module ℰ↓ {x} = Precategory (Fibre ℰ x) using (_∘_)
    module ℱ↓ {x} = Precategory (Fibre ℱ x) using (_∘_)

    open Displayed-functor
    open _=>_

    lvl : Level
    lvl = o ⊔ o' ⊔ ℓ ⊔ ℓ' ⊔ ℓ₂'
  infix 20 _=[_]=>_
```
-->

```agda
  record _=[_]=>_
    {F : Functor A B} {G : Functor A B}
    (F' : Displayed-functor F ℰ ℱ)
    (α : F => G)
    (G' : Displayed-functor G ℰ ℱ)
    : Type lvl
    where
    constructor NT'
    no-eta-equality

    field
      η' : ∀ {x} (x' : ℰ.Ob[ x ]) → ℱ.Hom[ α .η x ] (F' .F₀' x') (G' .F₀' x')
      is-natural'
        : ∀ {x y f} (x' : ℰ.Ob[ x ]) (y' : ℰ.Ob[ y ]) (f' : ℰ.Hom[ f ] x' y')
        → η' y' ℱ.∘' F' .F₁' f' ℱ.≡[ α .is-natural x y f ] G' .F₁' f' ℱ.∘' η' x'
```

<!--
```agda
{-# INLINE NT' #-}

module _
  {oa ℓa ob ℓb od ℓd oe ℓe}
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {D : Displayed A od ℓd} {E : Displayed B oe ℓe}
  where
  private 
    module A = Precategory A
    module B = Precategory B
    module D = Displayed D
    module E where
      open Displayed E public
      open DR E public

  open _=>_
  open _=[_]=>_
  open Displayed-functor

  Nat'-pathp : {F₁ F₂ G₁ G₂ : Functor A B} 
             → {F₁' : Displayed-functor F₁ D E} 
             → {G₁' : Displayed-functor G₁ D E}
             → {F₂' : Displayed-functor F₂ D E}
             → {G₂' : Displayed-functor G₂ D E}
             → {α : F₁ => G₁} {β : F₂ => G₂}
             → {α' : F₁' =[ α ]=> G₁'} {β' : F₂' =[ β ]=> G₂'}
             → (p : F₁ ≡ F₂) (q : G₁ ≡ G₂) 
             → (r : PathP (λ i → p i => q i) α β)
             → (p' : PathP (λ i → Displayed-functor (p i) D E) F₁' F₂')
             → (q' : PathP (λ i → Displayed-functor (q i) D E) G₁' G₂')
             → (∀ {x} (x' : D.Ob[ x ]) → PathP (λ i → E.Hom[ (r i .η x) ] (p' i .F₀' x') (q' i .F₀' x')) (α' .η' x') (β' .η' x'))
             → PathP (λ i → (p' i) =[ r i ]=> (q' i)) α' β'
  Nat'-pathp p q r p' q' w i .η' x' = w x' i
  Nat'-pathp {α' = α'} {β' = β'} p q r p' q' w i .is-natural' {x = x} {y} {f} x' y' f' j = 
    is-set→squarep {A = λ i j → E.Hom[ r i .is-natural x y f j ] (F₀' (p' i) x') (F₀' (q' i) y')} (λ _ _ → hlevel 2)
      (λ i → w y' i E.∘' F₁' (p' i) f') (λ j → is-natural' α' x' y' f' j) (λ j → is-natural' β' x' y' f' j) (λ i → F₁' (q' i) f' E.∘' w x' i) i j

  Nat'-path : {F G : Functor A B} {F' : Displayed-functor F D E} {G' : Displayed-functor G D E}
           → {α β : F => G} {α' : F' =[ α ]=> G'} {β' : F' =[ β ]=> G'} 
           → {p : α ≡ β}
           → (∀ {x} (x' : D.Ob[ x ]) → α' .η' x' E.≡[ p ηₚ x ] β' .η' x')
           → PathP (λ i → F' =[ p i ]=> G') α' β'
  Nat'-path = Nat'-pathp refl refl _ refl refl
```
-->
We can define displayed versions of the indentity natural transformation and 
composition of natural transformations.
```agda 
  idnt' : ∀ {F : Functor A B} {F' : Displayed-functor F D E} → F' =[ idnt ]=> F'
  idnt' .η' x' = E.id'
  idnt' .is-natural' x' y' f' = E.id-comm-sym[]

  _∘nt'_ : ∀ {F G H : Functor A B} 
          → {F' : Displayed-functor F D E} 
          → {G' : Displayed-functor G D E} 
          → {H' : Displayed-functor H D E} 
          → {β : G => H} {α : F => G}
          → G' =[ β ]=> H' → F' =[ α ]=> G' → F' =[ β ∘nt α ]=> H'
  (β' ∘nt' α') .η' x' = β' .η' x' E.∘' α' .η' x'
  _∘nt'_ {F' = F'} {G'} {H'} β' α' .is-natural' x' y' f' = E.cast[] $ 
    (β'.η' y' E.∘' α'.η' y') E.∘' F'.F₁' f'  E.≡[]⟨ E.pullr[] _ (α'.is-natural' _ _ _) ⟩
      β'.η' y' E.∘' G'.F₁' f' E.∘' α'.η' x'  E.≡[]⟨ E.pulll[] _ (β'.is-natural' _ _ _) ⟩
    (H'.F₁' f' E.∘' β'.η' x') E.∘' α'.η' x'  E.≡[]˘⟨ E.assoc' _ _ _ ⟩
      H'.F₁' f' E.∘' β'.η' x' E.∘' α'.η' x'   ∎
    where
      module β' = _=[_]=>_ β'
      module α' = _=[_]=>_ α'
      module F' = Displayed-functor F'
      module G' = Displayed-functor G'
      module H' = Displayed-functor H'
```
-->
::: {.definition #vertical-natural-transformation}
Let $F, G : \cE \to \cF$ be two vertical functors. A displayed natural
transformation between $F$ and $G$ is called a **vertical natural
transformation** if all components of the natural transformation are
vertical.
:::

<!--
```agda
module _
  {ob ℓb oe ℓe of ℓf}
  {B : Precategory ob ℓb}
  {ℰ : Displayed B oe ℓe}
  {ℱ : Displayed B of ℓf}
  where
  private
    open CR B
    module ℰ = Displayed ℰ
    module ℱ where
      open Displayed ℱ public
      open DR ℱ public
    module ℱ↓ {x} = CR (Fibre ℱ x)

    open Displayed-functor

  infix 20 _=>↓_
```
-->

```agda
  _=>↓_  : Vertical-functor ℰ ℱ → Vertical-functor ℰ ℱ → Type _
  F' =>↓ G' = F' =[ idnt ]=> G'
```

<!--
```agda
  module _=>↓_ {F' G' : Vertical-functor ℰ ℱ} (α : F' =>↓ G') where
    open _=[_]=>_ α public

    abstract
      is-natural↓
        : ∀ {x} (x' y' : ℰ.Ob[ x ]) (f' : ℰ.Hom[ id ] x' y')
        → η' y' ℱ↓.∘ F' .F₁' f' ≡ G' .F₁' f' ℱ↓.∘ η' x'
      is-natural↓ x y f =
        ap ℱ.hom[] (from-pathp⁻ (is-natural' x y f))
        ∙ sym (ℱ.duplicate _ _ _)

  private unquoteDecl eqv = declare-record-iso eqv (quote _=[_]=>_)

  instance
    Extensional-=>↓
      : ∀ {ℓr F' G'}
      → ⦃ _ : Extensional (∀ {x} (x' : ℰ.Ob[ x ]) → ℱ.Hom[ id ] (F' .F₀' x') (G' .F₀' x')) ℓr ⦄
      → Extensional (F' =>↓ G') ℓr
    Extensional-=>↓ {F' = F'} {G' = G'}  ⦃ e ⦄  = injection→extensional! {f = _=>↓_.η'}
      (λ p → Iso.injective eqv (Σ-prop-path! p)) e

    H-Level-=>↓ : ∀ {F' G'} {n} → H-Level (F' =>↓ G') (2 + n)
    H-Level-=>↓ = basic-instance 2 (Iso→is-hlevel 2 eqv (hlevel 2))

  open _=>↓_

  idnt↓ : ∀ {F} → F =>↓ F
  idnt↓ .η' x' = ℱ.id'
  idnt↓ .is-natural' x' y' f' = DR.id-comm-sym[] ℱ

  _∘nt↓_ : ∀ {F G H} → G =>↓ H → F =>↓ G → F =>↓ H
  (f ∘nt↓ g) .η' x' = f .η' _ ℱ↓.∘ g .η' x'
  _∘nt↓_ {F = F} {G = G} {H = H} f g .is-natural' {f = b} x' y' f' =
    let open DR ℱ using (hom[] ; whisker-l ; duplicate ; pullr' ; extendl' ; unwhisker-r) in to-pathp (
        ap hom[] (whisker-l (idl id))
    ∙∙ sym (duplicate (ap (_∘ b) (idl id) ∙ id-comm-sym) _ _)
    ∙∙ ap hom[] (from-pathp⁻ (pullr' id-comm-sym (g .is-natural' _ _ _)
          {q = ap (_∘ b) (idl id) ∙ id-comm-sym ∙ introl refl}))
    ∙∙ sym (duplicate (eliml refl) _ _)
    ∙∙ ap hom[] (from-pathp⁻ (extendl' id-comm-sym (f .is-natural' x' y' f') {q = extendl id-comm-sym}))
    ∙∙ sym (duplicate (ap (b ∘_) (idl id)) (eliml refl) _)
    ∙∙ unwhisker-r _ _)

module _
  {ob ℓb oc ℓc od ℓd oe ℓe}
  {B : Precategory ob ℓb}
  {𝒞 : Displayed B oc ℓc}
  {𝒟 : Displayed B od ℓd}
  {ℰ : Displayed B oe ℓe}
  {F G : Vertical-functor 𝒟 ℰ} {H K : Vertical-functor 𝒞 𝒟}
  (α : F =>↓ G) (β : H =>↓ K) where

  open Displayed-functor
  open _=>↓_
  open CR B
  private module E {x} = CR (Fibre ℰ x) using (_∘_)

  _◆↓_ : (F ∘V H) =>↓ (G ∘V K)
  _◆↓_ .η' x' = G .F₁' (β .η' _) E.∘ α .η' _
  _◆↓_ .is-natural' x' y' f' = to-pathp (
      ap hom[] (whisker-l (idl id))
      ∙∙ sym (duplicate (ap (_∘ _) (idl id) ∙ id-comm-sym) _ _)
      ∙∙ ap hom[] (from-pathp⁻ (pullr' _ (α .is-natural' _ _ _) {q = pullr id-comm-sym}))
      ∙∙ sym (duplicate (eliml refl) _ _)
      ∙∙ ap hom[] (from-pathp⁻
        (extendl' _ (symP (G .F-∘') ∙[] (apd (λ i → G .F₁') (β .is-natural' _ _ _) ∙[] G .F-∘'))
          {q = extendl id-comm-sym}))
      ∙∙ sym (duplicate (ap (_ ∘_) (idl id)) _ _) ∙∙ unwhisker-r _ _)
    where
      open DR ℰ using (hom[] ; whisker-l ; duplicate ; pullr' ; extendl' ; unwhisker-r)
      open Displayed ℰ using (_∙[]_)
```
-->
