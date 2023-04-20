```agda
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning as CR
import Cat.Displayed.Reasoning as DR

module Cat.Displayed.Functor where
```

# Displayed and fibred functors

If you have a pair of categories $\cE, \cF$ \r{displayed over} a
common base \r{category} $\cB$, it makes immediate sense to talk
about \r{functors} $F : \cE \to \cF$: you'd have an assignment of
objects $F_x : \cE^*(x) \to \cF^*(x)$ and an assignment of
morphisms

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
  _ {o ℓ o′ ℓ′ o₂ ℓ₂ o₂′ ℓ₂′}
    {A : Precategory o ℓ}
    {B : Precategory o₂ ℓ₂}
    (ℰ : Displayed A o′ ℓ′)
    (ℱ : Displayed B o₂′ ℓ₂′)
    (F : Functor A B)
  where
  private
    module F = Functor F
    module A = CR A
    module B = CR B
    module ℰ = Displayed ℰ
    module ℱ = Displayed ℱ
    lvl : Level
    lvl = o ⊔ o′ ⊔ o₂′ ⊔ ℓ ⊔ ℓ′ ⊔ ℓ₂′
```
-->

```agda
  record Displayed-functor : Type lvl where
    no-eta-equality
    field
      F₀′ : ∀ {x} (o : ℰ.Ob[ x ]) → ℱ.Ob[ F.₀ x ]
      F₁′ : ∀ {a b} {f : A.Hom a b} {a′ b′}
          → ℰ.Hom[ f ] a′ b′ → ℱ.Hom[ F.₁ f ] (F₀′ a′) (F₀′ b′)
```

In order to state the displayed functoriality laws, we require
functoriality for our mediating functor $F$. Functors between categories
displayed over the same base can be recovered as the "vertical displayed
functors", i.e., those lying over the identity functor.

```agda
      F-id′ : ∀ {x} {o : ℰ.Ob[ x ]}
            → PathP (λ i → ℱ.Hom[ F.F-id i ] (F₀′ o) (F₀′ o))
                    (F₁′ ℰ.id′) ℱ.id′
      F-∘′ : ∀ {a b c} {f : A.Hom b c} {g : A.Hom a b} {a′ b′ c′}
               {f′ : ℰ.Hom[ f ] b′ c′} {g′ : ℰ.Hom[ g ] a′ b′}
           → PathP (λ i → ℱ.Hom[ F.F-∘ f g i ] (F₀′ a′) (F₀′ c′))
                   (F₁′ (f′ ℰ.∘′ g′))
                   (F₁′ f′ ℱ.∘′ F₁′ g′)
    ₀′ = F₀′
    ₁′ = F₁′
```

Note that, if $\cE$ and $\cF$ are \r{fibred categories} over their
bases (rather than just _displayed_ categories), then the appropriate
notion of 1-cell are displayed functors that take Cartesian morphisms to
Cartesian morphisms:

<!--
```agda
module
  _ {o ℓ o′ ℓ′ o₂ ℓ₂ o₂′ ℓ₂′}
    {A : Precategory o ℓ}
    {B : Precategory o₂ ℓ₂}
    {ℰ : Displayed A o′ ℓ′}
    {ℱ : Displayed B o₂′ ℓ₂′}
    {F : Functor A B}
  where
  private
    module F = Functor F
    module A = CR A
    module B = CR B
    module ℰ = Displayed ℰ
    module ℱ = Displayed ℱ
    lvl : Level
    lvl = o ⊔ o′ ⊔ o₂′ ⊔ ℓ ⊔ ℓ′ ⊔ ℓ₂′
```
-->

```agda
  is-fibred-functor : Displayed-functor ℰ ℱ F → Type _
  is-fibred-functor F′ = 
    ∀ {a b a′ b′} {f : A.Hom a b} (f′ : ℰ.Hom[ f ] a′ b′)
    → is-cartesian ℰ f f′ → is-cartesian ℱ (F.₁ f) (F₁′ f′)
    where open Displayed-functor F′
```

<!--
```agda
module
  _ {o ℓ o′ ℓ′ o₂ ℓ₂ o₂′ ℓ₂′}
    {A : Precategory o ℓ}
    {B : Precategory o₂ ℓ₂}
    (ℰ : Displayed A o′ ℓ′)
    (ℱ : Displayed B o₂′ ℓ₂′)
    (F : Functor A B)
  where
  private
    module F = Functor F
    module A = CR A
    module B = CR B
    module ℰ = Displayed ℰ
    module ℱ = Displayed ℱ
    lvl : Level
    lvl = o ⊔ o′ ⊔ o₂′ ⊔ ℓ ⊔ ℓ′ ⊔ ℓ₂′
```
-->

```agda
  record Fibred-functor : Type (lvl ⊔ o₂ ⊔ ℓ₂) where
    no-eta-equality
    field
      disp : Displayed-functor ℰ ℱ F
      F-cartesian : is-fibred-functor disp

    open Displayed-functor disp public
```

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
    module ℋ = Displayed ℋ
    module F = Functor F
    module G = Functor G

    open DR ℋ
    open Displayed-functor

  infixr 30 _F∘′_
```
-->

```agda
  _F∘′_
    : Displayed-functor ℱ ℋ F
    → Displayed-functor ℰ ℱ G
    → Displayed-functor ℰ ℋ (F F∘ G)
  (F′ F∘′ G′) .F₀′ x = F′ .F₀′ (G′ .F₀′ x)
  (F′ F∘′ G′) .F₁′ f = F′ .F₁′ (G′ .F₁′ f)
  (F′ F∘′ G′) .F-id′ = to-pathp $
    hom[] (F′ .F₁′ (G′ .F₁′ ℰ.id′))         ≡⟨ reindex _ _ ∙ sym (hom[]-∙ (ap F.F₁ G.F-id) F.F-id) ⟩
    hom[] (hom[] (F′ .F₁′ (G′ .F₁′ ℰ.id′))) ≡⟨ ap hom[] (shiftl _ λ i → F′ .F₁′ (G′ .F-id′ i)) ⟩
    hom[] (F′ .F₁′ ℱ.id′)                   ≡⟨ from-pathp (F′ .F-id′) ⟩
    ℋ.id′                                   ∎
  (F′ F∘′ G′) .F-∘′ {f = f} {g = g} {f′ = f′} {g′ = g′} = to-pathp $
    hom[] (F′ .F₁′ (G′ .F₁′ (f′ ℰ.∘′ g′)))           ≡⟨ reindex _ _ ∙ sym (hom[]-∙ (ap F.F₁ (G.F-∘ f g)) (F.F-∘ (G.₁ f) (G.₁ g))) ⟩
    hom[] (hom[] (F′ .F₁′ (G′ .F₁′ (f′ ℰ.∘′ g′))))   ≡⟨ ap hom[] (shiftl _ λ i → F′ .F₁′ (G′ .F-∘′ {f′ = f′} {g′ = g′} i)) ⟩
    hom[] (F′ .F₁′ ((G′ .F₁′ f′) ℱ.∘′ (G′ .F₁′ g′))) ≡⟨ from-pathp (F′ .F-∘′) ⟩
    F′ .F₁′ (G′ .F₁′ f′) ℋ.∘′ F′ .F₁′ (G′ .F₁′ g′)   ∎
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
```
-->

```agda
  Id′ : Displayed-functor ℰ ℰ Id
  Id′ .F₀′ x = x
  Id′ .F₁′ f = f
  Id′ .F-id′ = refl
  Id′ .F-∘′  = refl
```

The identity functor is obviously fibred.

```agda
  Id′-fibred : is-fibred-functor Id′
  Id′-fibred f cart = cart

  Idf′ : Fibred-functor ℰ ℰ Id
  Idf′ .Fibred-functor.disp = Id′
  Idf′ .Fibred-functor.F-cartesian = Id′-fibred
```


## Vertical Functors

Functors displayed over the identity functor are of particular interest.
Such functors are known as **vertical functors**, and are commonly used
to define fibrewise structure. However, they are somewhat difficult to
work with if we define them directly as such, as the composite of two
identity functors is not **definitionally** equal to the identity functor!
To avoid this problem, we provide the following specialized definition.

```agda
module
  _ {o ℓ o′ ℓ′ o′′ ℓ′′}
    {B : Precategory o ℓ}
    (ℰ : Displayed B o′ ℓ′)
    (ℱ : Displayed B o′′ ℓ′′)
  where
  private
    module B = Precategory B
    module ℰ = Displayed ℰ
    module ℱ = Displayed ℱ

  record Vertical-functor : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ o′′ ⊔ ℓ′′) where
    no-eta-equality
    field
      F₀′ : ∀ {x} (o : ℰ.Ob[ x ]) → ℱ.Ob[ x ]
      F₁′ : ∀ {a b} {f : B.Hom a b} {a′ b′}
          → ℰ.Hom[ f ] a′ b′ → ℱ.Hom[ f ] (F₀′ a′) (F₀′ b′)
      F-id′ : ∀ {x} {o : ℰ.Ob[ x ]}
            → PathP ( λ _ →  ℱ.Hom[ B.id ] (F₀′ o) (F₀′ o))
                         (F₁′ ℰ.id′) ℱ.id′ 
      F-∘′ : ∀ {a b c} {f : B.Hom b c} {g : B.Hom a b} {a′ b′ c′}
                 {f′ : ℰ.Hom[ f ] b′ c′} {g′ : ℰ.Hom[ g ] a′ b′} 
            → PathP (λ _ → ℱ.Hom[ f B.∘ g ] (F₀′ a′) (F₀′ c′)) (F₁′ (f′ ℰ.∘′ g′))
                         (F₁′ f′ ℱ.∘′ F₁′ g′)
    ₀′ = F₀′
    ₁′ = F₁′
```

This definition is equivalent to a displayed functor over the identity
functor.

<!--
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
```
-->

```agda
  Displayed-functor→Vertical-functor
    : Displayed-functor ℰ ℱ Id → Vertical-functor ℰ ℱ
  Displayed-functor→Vertical-functor F′ = V where
    module F′ = Displayed-functor F′
    open Vertical-functor

    V : Vertical-functor ℰ ℱ
    V .F₀′ = F′.₀′
    V .F₁′ = F′.₁′
    V .F-id′ = F′.F-id′
    V .F-∘′ = F′.F-∘′

  Vertical-functor→Displayed-functor
    : Vertical-functor ℰ ℱ → Displayed-functor ℰ ℱ Id
  Vertical-functor→Displayed-functor V = F′ where
    module V = Vertical-functor V
    open Displayed-functor

    F′ : Displayed-functor ℰ ℱ Id
    F′ .F₀′ = V.₀′
    F′ .F₁′ = V.₁′
    F′ .F-id′ = V.F-id′
    F′ .F-∘′ = V.F-∘′
```

We also provide a specialized definition for vertical fibred functors.

```agda
  is-vertical-fibred : Vertical-functor ℰ ℱ → Type _
  is-vertical-fibred F′ =
    ∀ {a b a′ b′} {f : B.Hom a b} (f′ : ℰ.Hom[ f ] a′ b′)
    → is-cartesian ℰ f f′ → is-cartesian ℱ f (F₁′ f′)
    where open Vertical-functor F′
```


<!--
```agda
module
  _ {o ℓ o′ ℓ′ o′′ ℓ′′}
    {B : Precategory o ℓ}
    (ℰ : Displayed B o′ ℓ′)
    (ℱ : Displayed B o′′ ℓ′′)
  where
  private
    module B = Precategory B
    module ℰ = Displayed ℰ
    module ℱ = Displayed ℱ
    lvl : Level
    lvl = o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ o′′ ⊔ ℓ′′
```
-->

```agda
  record Vertical-fibred-functor : Type lvl where
    no-eta-equality
    field
      vert : Vertical-functor ℰ ℱ
      F-cartesian : is-vertical-fibred vert
    open Vertical-functor vert public
```

<!--
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
```
-->


A functor displayed over the identity functor is fibred if and only if
it is a vertical fibred functor.

```agda
  is-fibred→is-vertical-fibred
    : ∀ (F' : Displayed-functor ℰ ℱ Id)
    → is-fibred-functor F'
    → is-vertical-fibred (Displayed-functor→Vertical-functor F')
  is-fibred→is-vertical-fibred F' F-fib = F-fib

  is-vertical-fibred→is-fibred
    : ∀ (F' : Vertical-functor ℰ ℱ)
    → is-vertical-fibred F'
    → is-fibred-functor (Vertical-functor→Displayed-functor F')
  is-vertical-fibred→is-fibred F' F-fib = F-fib

  Fibred→Vertical-fibred
    : Fibred-functor ℰ ℱ Id → Vertical-fibred-functor ℰ ℱ
  Fibred→Vertical-fibred F' .Vertical-fibred-functor.vert =
    Displayed-functor→Vertical-functor (Fibred-functor.disp F')
  Fibred→Vertical-fibred F' .Vertical-fibred-functor.F-cartesian =
    is-fibred→is-vertical-fibred
      (Fibred-functor.disp F')
      (Fibred-functor.F-cartesian F')

  Vertical-Fibred→Vertical
    : Vertical-fibred-functor ℰ ℱ → Fibred-functor ℰ ℱ Id
  Vertical-Fibred→Vertical F' .Fibred-functor.disp =
    Vertical-functor→Displayed-functor (Vertical-fibred-functor.vert F')
  Vertical-Fibred→Vertical F' .Fibred-functor.F-cartesian =
    is-vertical-fibred→is-fibred
      (Vertical-fibred-functor.vert F')
      (Vertical-fibred-functor.F-cartesian F')
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
  open Vertical-functor

  infixr 30 _V∘_
  infixr 30 _Vf∘_
```
-->

```agda
  _V∘_ : Vertical-functor ℱ ℋ → Vertical-functor ℰ ℱ → Vertical-functor ℰ ℋ
  (F′ V∘ G′) .F₀′ x′ = F′ .F₀′ (G′ .F₀′ x′)
  (F′ V∘ G′) .F₁′ f′ = F′ .F₁′ (G′ .F₁′ f′)
  (F′ V∘ G′) .F-id′ = ap (F′ .F₁′) (G′ .F-id′) ∙ F′ .F-id′
  (F′ V∘ G′) .F-∘′ = ap (F′ .F₁′) (G′ .F-∘′) ∙ (F′ .F-∘′)
```

Furthermore, the composite of vertical fibred functors is also fibred.

```agda
  V∘-fibred
    : ∀ (F′ : Vertical-functor ℱ ℋ) (G′ : Vertical-functor ℰ ℱ)
    → is-vertical-fibred F′ → is-vertical-fibred G′ → is-vertical-fibred (F′ V∘ G′)
  V∘-fibred F′ G′ F′-fib G′-fib f′ cart = F′-fib (G′ .F₁′ f′) (G′-fib f′ cart)

  _Vf∘_
    : Vertical-fibred-functor ℱ ℋ
    → Vertical-fibred-functor ℰ ℱ
    → Vertical-fibred-functor ℰ ℋ
  (F′ Vf∘ G′) .Vertical-fibred-functor.vert =
    Vertical-fibred-functor.vert F′ V∘ Vertical-fibred-functor.vert G′
  (F′ Vf∘ G′) .Vertical-fibred-functor.F-cartesian =
    V∘-fibred
      (Vertical-fibred-functor.vert F′)
      (Vertical-fibred-functor.vert G′)
      (Vertical-fibred-functor.F-cartesian F′)
      (Vertical-fibred-functor.F-cartesian G′)
```

The identity functor is obviously fibred vertical.

<!--
```agda
module _
  {ob ℓb oe ℓe}
  {B : Precategory ob ℓb}
  {ℰ : Displayed B oe ℓe}
  where
```
-->

```agda
  IdV : Vertical-functor ℰ ℰ
  IdV = Displayed-functor→Vertical-functor Id′

  IdV-fibred : is-vertical-fibred IdV
  IdV-fibred = is-fibred→is-vertical-fibred Id′ Id′-fibred

  IdVf : Vertical-fibred-functor ℰ ℰ
  IdVf = Fibred→Vertical-fibred Idf′
```
