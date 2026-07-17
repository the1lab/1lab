<!--
```agda
open import Cat.Instances.Product
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Coproduct where
```

<!--
```agda
module _ {o h} (C : Precategory o h) where
  open Cat.Reasoning C
  private variable
    A B : Ob
```
-->

# Coproducts {defines="coproduct"}

The **coproduct** $P$ of two objects $A$ and $B$ (if it exists), is the
smallest object equipped with "injection" maps $A \to P$, $B \to P$.  It
is dual to the [[product]].

We witness this notion of "smallest object" with a universal property;
Given any other $Q$ that also admits injection maps from $A$ and $B$,
we must have a *unique* map $P \to Q$ that factors the injections into
$Q$. This is best explained by a commutative diagram:

~~~{.quiver}
\[\begin{tikzcd}
  A & P & B \\
  & Q \\
  & {}
  \arrow[from=1-1, to=1-2]
  \arrow[from=1-3, to=1-2]
  \arrow[from=1-1, to=2-2]
  \arrow[from=1-3, to=2-2]
  \arrow["{\exists!}"', dashed, from=1-2, to=2-2]
\end{tikzcd}\]
~~~

```agda
  record is-coproduct {A B P} (ι₁ : Hom A P) (ι₂ : Hom B P) : Type (o ⊔ h) where
    field
      [_,_] : ∀ {Q} (inj0 : Hom A Q) (inj1 : Hom B Q) → Hom P Q
      []∘ι₁ : ∀ {Q} {inj0 : Hom A Q} {inj1} → [ inj0 , inj1 ] ∘ ι₁ ≡ inj0
      []∘ι₂ : ∀ {Q} {inj0 : Hom A Q} {inj1} → [ inj0 , inj1 ] ∘ ι₂ ≡ inj1

      unique
        : ∀ {Q} {inj0 : Hom A Q} {inj1} {other : Hom P Q}
        → other ∘ ι₁ ≡ inj0 → other ∘ ι₂ ≡ inj1
        → [ inj0 , inj1 ] ≡ other

    unique₂
      : ∀ {Q} {inj0 : Hom A Q} {inj1}
      → ∀ {o1} (p1 : o1 ∘ ι₁ ≡ inj0) (q1 : o1 ∘ ι₂ ≡ inj1)
      → ∀ {o2} (p2 : o2 ∘ ι₁ ≡ inj0) (q2 : o2 ∘ ι₂ ≡ inj1)
      → o1 ≡ o2
    unique₂ p1 q1 p2 q2 = sym (unique p1 q1) ∙ unique p2 q2
```

A coproduct of $A$ and $B$ is an explicit choice of coproduct diagram:

```agda
  record Coproduct (A B : Ob) : Type (o ⊔ h) where
    field
      coapex : Ob
      ι₁ : Hom A coapex
      ι₂ : Hom B coapex
      has-is-coproduct : is-coproduct ι₁ ι₂

    open is-coproduct has-is-coproduct public
```

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C
  private variable
    A B a b c d : Ob

  is-coproduct-is-prop : ∀ {X Y P} {i₁ : Hom X P} {i₂ : Hom Y P} → is-prop (is-coproduct C i₁ i₂)
  is-coproduct-is-prop {X = X} {Y = Y} {i₁ = i₁} {i₂} x y = q where
    open is-coproduct
    p : Path (∀ {P'} → Hom X P' → Hom Y P' → _) (x .[_,_]) (y .[_,_])
    p i inj0 inj1 = y .unique {inj0 = inj0} {inj1} (x .[]∘ι₁) (x .[]∘ι₂) (~ i)
    q : x ≡ y
    q i .[_,_] = p i
    q i .[]∘ι₁ {inj0 = inj0} {inj1} = is-prop→pathp (λ i → Hom-set _ _ (p i inj0 inj1 ∘ i₁) inj0) (x .[]∘ι₁) (y .[]∘ι₁) i
    q i .[]∘ι₂ {inj0 = inj0} {inj1} = is-prop→pathp (λ i → Hom-set _ _ (p i inj0 inj1 ∘ i₂) inj1) (x .[]∘ι₂) (y .[]∘ι₂) i
    q i .unique {inj0 = inj0} {inj1} {other} c₁ c₂ = is-prop→pathp
      (λ i → Hom-set _ _ (p i inj0 inj1) other)
      (x .unique c₁ c₂)
      (y .unique c₁ c₂) i

  instance
    H-Level-is-coproduct : ∀ {X Y P} {i₁ : Hom X P} {i₂ : Hom Y P} {n} → H-Level (is-coproduct C i₁ i₂) (suc n)
    H-Level-is-coproduct = prop-instance is-coproduct-is-prop

unquoteDecl Coproduct-path = declare-record-path Coproduct-path (quote Coproduct)
```
-->

## Uniqueness

The uniqueness argument presented here is dual to the argument
for the [[product|uniqueness of products]].

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C
  private variable
    A B a b c d : Ob
  open Coproduct
```
-->

```agda
  +-Unique : (c1 c2 : Coproduct C A B) → coapex c1 ≅ coapex c2
  +-Unique c1 c2 = make-iso c1→c2 c2→c1 c1→c2→c1 c2→c1→c2 where
    module c1 = Coproduct c1
    module c2 = Coproduct c2

    c1→c2 : Hom (coapex c1) (coapex c2)
    c1→c2 = c1.[ c2.ι₁ , c2.ι₂ ]

    c2→c1 : Hom (coapex c2) (coapex c1)
    c2→c1 = c2.[ c1.ι₁ , c1.ι₂ ]
```

```agda
    c1→c2→c1 : c1→c2 ∘ c2→c1 ≡ id
    c1→c2→c1 = c2.unique₂
      (pullr c2.[]∘ι₁ ∙ c1.[]∘ι₁)
      (pullr c2.[]∘ι₂ ∙ c1.[]∘ι₂)
      (idl _) (idl _)

    c2→c1→c2 : c2→c1 ∘ c1→c2 ≡ id
    c2→c1→c2 = c1.unique₂
      (pullr c1.[]∘ι₁ ∙ c2.[]∘ι₁)
      (pullr c1.[]∘ι₂ ∙ c2.[]∘ι₂)
      (idl _) (idl _)
```

<!--
```agda
  is-coproduct-iso
    : ∀ {A A' B B' P} {ι₁ : Hom A P} {ι₂ : Hom B P}
        {f : Hom A' A} {g : Hom B' B}
    → is-invertible f
    → is-invertible g
    → is-coproduct C ι₁ ι₂
    → is-coproduct C (ι₁ ∘ f) (ι₂ ∘ g)
  is-coproduct-iso f-iso g-iso coprod = coprod' where
    module fi = is-invertible f-iso
    module gi = is-invertible g-iso

    open is-coproduct
    coprod' : is-coproduct C _ _
    coprod' .[_,_] qa qb = coprod .[_,_] (qa ∘ fi.inv) (qb ∘ gi.inv)
    coprod' .[]∘ι₁ = pulll (coprod .[]∘ι₁) ∙ cancelr fi.invr
    coprod' .[]∘ι₂ = pulll (coprod .[]∘ι₂) ∙ cancelr gi.invr
    coprod' .unique p q = coprod .unique
      (sym (rswizzle (sym p ∙ assoc _ _ _) fi.invl))
      (sym (rswizzle (sym q ∙ assoc _ _ _) gi.invl))

  is-coproduct-iso-coapex
    : ∀ {A B P P'} {ι₁ : Hom A P} {ι₂ : Hom B P}
        {ι₁' : Hom A P'} {ι₂' : Hom B P'}
        {f : Hom P P'}
    → is-invertible f
    → f ∘ ι₁ ≡ ι₁'
    → f ∘ ι₂ ≡ ι₂'
    → is-coproduct C ι₁ ι₂
    → is-coproduct C ι₁' ι₂'
  is-coproduct-iso-coapex {f = f} f-iso f-ι₁ f-ι₂ coprod = coprod' where
    module fi = is-invertible f-iso

    open is-coproduct
    coprod' : is-coproduct C _ _
    coprod' .[_,_] qa qb = coprod .[_,_] qa qb ∘ fi.inv
    coprod' .[]∘ι₁ = pullr (lswizzle (sym f-ι₁) fi.invr) ∙ coprod .[]∘ι₁
    coprod' .[]∘ι₂ = pullr (lswizzle (sym f-ι₂) fi.invr) ∙ coprod .[]∘ι₂
    coprod' .unique p q = rswizzle
      (coprod .unique (pullr f-ι₁ ∙ p) (pullr f-ι₂ ∙ q)) fi.invl

  Coproduct-is-prop
    : ∀ {A B}
    → is-category C
    → is-prop (Coproduct C A B)
  Coproduct-is-prop cat inj1 inj2 = Coproduct-path
    (cat .to-path (+-Unique inj1 inj2))
    (Univalent.Hom-pathp-reflr-iso cat (inj1 .[]∘ι₁))
    (Univalent.Hom-pathp-reflr-iso cat (inj1 .[]∘ι₂))
```
-->

# Categories with all binary coproducts

Categories with all binary coproducts are quite common, so we define
a module for working with them.

```agda
has-coproducts : ∀ {o ℓ} → Precategory o ℓ → Type _
has-coproducts C = ∀ a b → Coproduct C a b

module Binary-coproducts
  {o ℓ} (C : Precategory o ℓ) (all-coproducts : has-coproducts C) where

  open Cat.Reasoning C

  module _ {a b} where open Coproduct (all-coproducts a b) renaming (unique to []-unique) hiding (coapex) public
  module _ a b where open Coproduct (all-coproducts a b) renaming (coapex to infixr 7 _⊕₀_) using () public
  open Functor

  infix 50 _⊕₁_

  _⊕₁_ : ∀ {a b x y} → Hom a x → Hom b y → Hom (a ⊕₀ b) (x ⊕₀ y)
  f ⊕₁ g = [ ι₁ ∘ f , ι₂ ∘ g ]

  ⊕-functor : Functor (C ×ᶜ C) C
  ⊕-functor .F₀ (a , b) = a ⊕₀ b
  ⊕-functor .F₁ (f , g) = f ⊕₁ g
  ⊕-functor .F-id = []-unique id-comm-sym id-comm-sym
  ⊕-functor .F-∘ (f , g) (h , i) = []-unique
    (pullr []∘ι₁ ∙ extendl []∘ι₁)
    (pullr []∘ι₂ ∙ extendl []∘ι₂)

  ∇ : ∀ {a} → Hom (a ⊕₀ a) a
  ∇ = [ id , id ]

  coswap : ∀ {a b} → Hom (a ⊕₀ b) (b ⊕₀ a)
  coswap = [ ι₂ , ι₁ ]

  ⊕-assoc : ∀ {a b c} → Hom (a ⊕₀ (b ⊕₀ c)) ((a ⊕₀ b) ⊕₀ c)
  ⊕-assoc = [ ι₁ ∘ ι₁ , [ ι₁ ∘ ι₂ , ι₂ ] ]
```

<!--
```agda
  ∇-natural : is-natural-transformation (⊕-functor F∘ Cat⟨ Id , Id ⟩) Id λ _ → ∇
  ∇-natural x y f = unique₂
    (pullr []∘ι₁ ∙ cancell []∘ι₁) (pullr []∘ι₂ ∙ cancell []∘ι₂)
    (cancelr []∘ι₁) (cancelr []∘ι₂)

  ∇-coswap : ∀ {a} → ∇ ∘ coswap ≡ ∇ {a}
  ∇-coswap = sym $ []-unique (pullr []∘ι₁ ∙ []∘ι₂) (pullr []∘ι₂ ∙ []∘ι₁)

  ∇-assoc : ∀ {a} → ∇ {a} ∘ (∇ {a} ⊕₁ id) ∘ ⊕-assoc ≡ ∇ ∘ (id ⊕₁ ∇)
  ∇-assoc = unique₂
    (pullr (pullr []∘ι₁) ∙ (refl⟩∘⟨ pulll []∘ι₁) ∙ pulll (pulll []∘ι₁) ∙ pullr []∘ι₁)
    (pullr (pullr []∘ι₂) ∙ sym ([]-unique
      (pullr (pullr []∘ι₁) ∙ extend-inner []∘ι₁ ∙ cancell []∘ι₁ ∙ []∘ι₂)
      (pullr (pullr []∘ι₂) ∙ (refl⟩∘⟨ []∘ι₂) ∙ cancell []∘ι₂)))
    (pullr []∘ι₁ ∙ pulll []∘ι₁)
    (pullr []∘ι₂ ∙ cancell []∘ι₂)
```
-->
