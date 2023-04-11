```agda
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning as CR

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

```agda
  record Fibred-functor : Type (lvl ⊔ o₂ ⊔ ℓ₂) where
    field
      disp : Displayed-functor

    open Displayed-functor disp public

    field
      F-cartesian
        : ∀ {a b a′ b′} {f : A.Hom a b} (f′ : ℰ.Hom[ f ] a′ b′)
        → is-cartesian ℰ f f′ → is-cartesian ℱ (F.₁ f) (F₁′ f′)
```

Of course one can also define the composition of displayed functors
which lies over the composition of the underlying functors. 
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
    module A = Precategory A
    module B = Precategory B
    module ℰ = Displayed ℰ
    module ℱ = Displayed ℱ
    module F = Functor F

  ap′ : ∀ {a b a′ b′} {f g : A.Hom a b} {f′ : ℰ.Hom[ f ] a′ b′} {g′ : ℰ.Hom[ g ] a′ b′}
            {p : f ≡ g} (F′ : Displayed-functor ℰ ℱ F) → f′ ℰ.≡[ p ] g′
       →  (F′ .Displayed-functor.F₁′ f′) ℱ.≡[ ap F.₁ p ] (F′ .Displayed-functor.F₁′) g′
  ap′ F′ p′ i =  (F′ .Displayed-functor.F₁′) (p′ i)
```
-->

```agda
_F∘′_ : ∀ {o ℓ o′ ℓ′ o₂ ℓ₂ o₂′ ℓ₂′ o₃ ℓ₃ o₃′ ℓ₃′} {A : Precategory o ℓ}
             {B : Precategory o₂ ℓ₂} {C : Precategory o₃ ℓ₃} {ℰ : Displayed A o′ ℓ′}
             {ℱ : Displayed B o₂′ ℓ₂′} {ℋ : Displayed C o₃′ ℓ₃′} {G : Functor B C}
             {F : Functor A B} → Displayed-functor ℱ ℋ G → Displayed-functor ℰ ℱ F
        → Displayed-functor ℰ ℋ (G F∘ F)
_F∘′_ {ℰ = ℰ} {ℱ = ℱ} {ℋ = ℋ} {G = G} {F = F} G′ F′ = comps where
  module ℰ = Displayed ℰ
  module ℱ = Displayed ℱ
  module ℋ = Displayed ℋ
  module F = Functor F
  module G = Functor G
  module F′ = Displayed-functor F′
  module G′ = Displayed-functor G′
  open import Cat.Displayed.Reasoning ℋ
  comps : Displayed-functor ℰ ℋ (G F∘ F)
  comps .Displayed-functor.F₀′ x′ = G′.₀′ (F′.₀′ x′)
  comps .Displayed-functor.F₁′ f′ = G′.₁′ (F′.₁′ f′)
  comps .Displayed-functor.F-id′ = to-pathp $
    hom[ (G F∘ F).Functor.F-id ] (G′.₁′ (F′.₁′ ℰ.id′)) ≡⟨ reindex _ _ ⟩
    hom[ (ap G.₁ F.F-id) ∙ G.F-id ] (G′.₁′ (F′.₁′ ℰ.id′)) ≡˘⟨ hom[]-∙ _ _ ⟩
    hom[ G.F-id ] (hom[ (ap G.₁ F.F-id) ] (G′.₁′ (F′.₁′ ℰ.id′))) ≡⟨ hom[]⟩⟨ shiftl _ (ap′ G′ F′.F-id′) ⟩
    hom[ G.F-id ] (G′.₁′ ℱ.id′) ≡⟨ from-pathp G′.F-id′ ⟩
    ℋ.id′ ∎
  comps .Displayed-functor.F-∘′ {f = f} {g = g} {f′ = f′} {g′ = g′} = to-pathp $
    hom[ (G F∘ F).Functor.F-∘ _ _ ] (G′.₁′ (F′.₁′ (f′ ℰ.∘′ g′))) ≡⟨ reindex _ _ ⟩
    hom[ (ap G.₁ (F.F-∘ f g)) ∙ (G.F-∘ _ _) ] (G′.₁′ (F′.₁′ (f′ ℰ.∘′ g′))) ≡˘⟨ hom[]-∙ _ _ ⟩
    hom[ G.F-∘ _ _ ] (hom[ ap G.₁ (F.F-∘ f g) ] (G′.₁′ (F′.₁′ (f′ ℰ.∘′ g′)))) ≡⟨ hom[]⟩⟨ shiftl _ (ap′ G′ F′.F-∘′) ⟩
    hom[ G.F-∘ _ _ ] (G′.₁′ ((F′.₁′ f′) ℱ.∘′ (F′.₁′ g′))) ≡⟨ from-pathp G′.F-∘′ ⟩
    G′.₁′ (F′.₁′ f′) ℋ.∘′ G′.₁′ (F′.₁′ g′) ∎
```

```agda
Id′ : ∀ {o ℓ o′ ℓ′} {A : Precategory o ℓ} {ℰ : Displayed A o′ ℓ′}
    → Displayed-functor ℰ ℰ Id
Id′ .Displayed-functor.F₀′ x = x
Id′ .Displayed-functor.F₁′ f = f
Id′ .Displayed-functor.F-id′ = refl
Id′ .Displayed-functor.F-∘′  = refl
```

Sometimes it is useful to have an own definition for the special case
that the displayed functor $\bf{F} : \cE \to \cF$ is between $\cE, \cF$
\r{displayed over} a common base \r{category} $\cB$. 
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

  record Displayed-functor-single-base : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ o′′ ⊔ ℓ′′) where
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

```agda
  record Fibred-functor-single-base : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ o′′ ⊔ ℓ′′) where
    field
      disp : Displayed-functor-single-base

    open Displayed-functor-single-base disp public

    field
      F-cartesian
        : ∀ {a b a′ b′} {f : B.Hom a b} (f′ : ℰ.Hom[ f ] a′ b′)
        → is-cartesian ℰ f f′ → is-cartesian ℱ f (F₁′ f′)
```

In fact this is equivalent to a displayed functor over the identity of $\cB$. 
```agda
Displayed-functor-over-id→over-single-base
  : ∀ {o ℓ o′ ℓ′ o′′ ℓ′′} {B : Precategory o ℓ}
       {ℰ : Displayed B o′ ℓ′} {ℱ : Displayed B o′′ ℓ′′}
  → Displayed-functor ℰ ℱ Id → Displayed-functor-single-base ℰ ℱ
Displayed-functor-over-id→over-single-base {ℰ = ℰ} {ℱ = ℱ} F′ = G′ where
  module F′ = Displayed-functor F′
  G′ : Displayed-functor-single-base ℰ ℱ
  G′ .Displayed-functor-single-base.F₀′ x′ = F′.₀′ x′
  G′ .Displayed-functor-single-base.F₁′ f′ = F′.₁′ f′
  G′ .Displayed-functor-single-base.F-id′ = F′.F-id′
  G′ .Displayed-functor-single-base.F-∘′ = F′.F-∘′

Displayed-functor-over-single-base→over-id
  : ∀ {o ℓ o′ ℓ′ o′′ ℓ′′} {B : Precategory o ℓ}
       {ℰ : Displayed B o′ ℓ′} {ℱ : Displayed B o′′ ℓ′′}
  → Displayed-functor-single-base ℰ ℱ → Displayed-functor ℰ ℱ Id
Displayed-functor-over-single-base→over-id {ℰ = ℰ} {ℱ = ℱ} F′ = G′ where
  module F′ = Displayed-functor-single-base F′
  G′ : Displayed-functor ℰ ℱ Id
  G′ .Displayed-functor.F₀′ x′ = F′.₀′ x′
  G′ .Displayed-functor.F₁′ f′ = F′.₁′ f′
  G′ .Displayed-functor.F-id′ = F′.F-id′
  G′ .Displayed-functor.F-∘′ = F′.F-∘′
```

And a fibred functor over a single base category is equivalent to a
fibred functor over the identity.
```agda
Fibred-functor-over-id→over-single-base
  : ∀ {o ℓ o′ ℓ′ o′′ ℓ′′} {B : Precategory o ℓ}
       {ℰ : Displayed B o′ ℓ′} {ℱ : Displayed B o′′ ℓ′′}
  → Fibred-functor ℰ ℱ Id → Fibred-functor-single-base ℰ ℱ
Fibred-functor-over-id→over-single-base F′ .Fibred-functor-single-base.disp
  = Displayed-functor-over-id→over-single-base (F′ .Fibred-functor.disp)
Fibred-functor-over-id→over-single-base F′ .Fibred-functor-single-base.F-cartesian
  = F′ .Fibred-functor.F-cartesian

Fibred-functor-over-single-base→over-id
  : ∀ {o ℓ o′ ℓ′ o′′ ℓ′′} {B : Precategory o ℓ}
       {ℰ : Displayed B o′ ℓ′} {ℱ : Displayed B o′′ ℓ′′}
  → Fibred-functor-single-base ℰ ℱ → Fibred-functor ℰ ℱ Id
Fibred-functor-over-single-base→over-id F′ .Fibred-functor.disp
  = Displayed-functor-over-single-base→over-id (F′ .Fibred-functor-single-base.disp)
Fibred-functor-over-single-base→over-id F′ .Fibred-functor.F-cartesian
  = F′ .Fibred-functor-single-base.F-cartesian
```

Defining the composition for displayed functors over a fixed
base category is much easier: 
```agda
_F∘′′_ : ∀ {o ℓ o′ ℓ′ o₂′ ℓ₂′ o₃′ ℓ₃′} {B : Precategory o ℓ} {ℰ : Displayed B o′ ℓ′}
              {ℱ : Displayed B o₂′ ℓ₂′} {ℋ : Displayed B o₃′ ℓ₃′}
        → Displayed-functor-single-base ℱ ℋ → Displayed-functor-single-base ℰ ℱ
        → Displayed-functor-single-base ℰ ℋ
_F∘′′_ {ℰ = ℰ} {ℱ = ℱ} {ℋ = ℋ} G′ F′ = comps where
  module F′ = Displayed-functor-single-base F′
  module G′ = Displayed-functor-single-base G′
  open import Cat.Displayed.Reasoning ℋ
  comps : Displayed-functor-single-base ℰ ℋ
  comps .Displayed-functor-single-base.F₀′ x′ = G′.₀′ (F′.₀′ x′)
  comps .Displayed-functor-single-base.F₁′ f′ = G′.₁′ (F′.₁′ f′)
  comps .Displayed-functor-single-base.F-id′ = ap G′.₁′ F′.F-id′ ∙ G′.F-id′
  comps .Displayed-functor-single-base.F-∘′ = ap G′.₁′ F′.F-∘′ ∙ G′.F-∘′
```

```agda
_fibred-F∘′′_ : ∀ {o ℓ o′ ℓ′ o₂′ ℓ₂′ o₃′ ℓ₃′} {B : Precategory o ℓ}
                    {ℰ : Displayed B o′ ℓ′} {ℱ : Displayed B o₂′ ℓ₂′}
                    {ℋ : Displayed B o₃′ ℓ₃′} → Fibred-functor-single-base ℱ ℋ
               → Fibred-functor-single-base ℰ ℱ → Fibred-functor-single-base ℰ ℋ
_fibred-F∘′′_ G′ F′ = comps where
  module F′ = Fibred-functor-single-base F′
  module G′ = Fibred-functor-single-base G′
  comps : Fibred-functor-single-base _ _
  comps .Fibred-functor-single-base.disp = G′.disp F∘′′ F′.disp
  comps .Fibred-functor-single-base.F-cartesian f′ f′-cart = G′.F-cartesian (F′.₁′ f′) (F′.F-cartesian f′ f′-cart)
```

One can define an displayed identity functor over a single base as the
regular displayed identity functor lies over the identity of the base
category.
```agda
Id′′ : ∀ {o ℓ o′ ℓ′} {B : Precategory o ℓ} {ℰ : Displayed B o′ ℓ′}
    → Displayed-functor-single-base ℰ ℰ
Id′′ .Displayed-functor-single-base.F₀′ x = x 
Id′′ .Displayed-functor-single-base.F₁′ f = f 
Id′′ .Displayed-functor-single-base.F-id′ = refl 
Id′′ .Displayed-functor-single-base.F-∘′ = refl 
```

which is obviously  also fibred. 
```agda
Id′′-is-fibred : ∀ {o ℓ o′ ℓ′} {B : Precategory o ℓ} {ℰ : Displayed B o′ ℓ′}
                 → Fibred-functor-single-base ℰ ℰ
Id′′-is-fibred .Fibred-functor-single-base.disp =  Id′′
Id′′-is-fibred .Fibred-functor-single-base.F-cartesian f′ f′-cart = f′-cart
```
