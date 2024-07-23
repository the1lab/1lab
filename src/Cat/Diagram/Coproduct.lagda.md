<!--
```agda
open import Cat.Instances.Product
open import Cat.Prelude
```
-->

```agda
module Cat.Diagram.Coproduct {o h} (C : Precategory o h) where
```

<!--
```agda
open import Cat.Reasoning C
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

    unique : ∀ {Q} {inj0 : Hom A Q} {inj1}
           → {other : Hom P Q}
           → other ∘ ι₁ ≡ inj0
           → other ∘ ι₂ ≡ inj1
           → other ≡ [ inj0 , inj1 ]

  unique₂ : ∀ {Q} {inj0 : Hom A Q} {inj1}
          → ∀ {o1} (p1 : o1 ∘ ι₁ ≡ inj0) (q1 : o1 ∘ ι₂ ≡ inj1)
          → ∀ {o2} (p2 : o2 ∘ ι₁ ≡ inj0) (q2 : o2 ∘ ι₂ ≡ inj1)
          → o1 ≡ o2
  unique₂ p1 q1 p2 q2 = unique p1 q1 ∙ sym (unique p2 q2)
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

## Uniqueness

The uniqueness argument presented here is dual to the argument
for the [[product|uniqueness of products]].

<!--
```agda
module _ where
  open Coproduct
```
-->

```agda
  +-Unique : (c1 c2 : Coproduct A B) → coapex c1 ≅ coapex c2
  +-Unique c1 c2 = make-iso c1→c2 c2→c1 c1→c2→c1 c2→c1→c2
    where
      module c1 = Coproduct c1
      module c2 = Coproduct c2

      c1→c2 : Hom (coapex c1) (coapex c2)
      c1→c2 = c1.[ c2.ι₁ , c2.ι₂ ]

      c2→c1 : Hom (coapex c2) (coapex c1)
      c2→c1 = c2.[ c1.ι₁ , c1.ι₂ ]
```

```agda
      c1→c2→c1 : c1→c2 ∘ c2→c1 ≡ id
      c1→c2→c1 =
        c2.unique₂
          (pullr c2.[]∘ι₁ ∙ c1.[]∘ι₁)
          (pullr c2.[]∘ι₂ ∙ c1.[]∘ι₂)
          (idl _) (idl _)

      c2→c1→c2 : c2→c1 ∘ c1→c2 ≡ id
      c2→c1→c2 =
        c1.unique₂
          (pullr c1.[]∘ι₁ ∙ c2.[]∘ι₁)
          (pullr c1.[]∘ι₂ ∙ c2.[]∘ι₂)
          (idl _) (idl _)
```

# Categories with all binary coproducts

Categories with all binary coproducts are quite common, so we define
a module for working with them.

```agda
has-coproducts : Type _
has-coproducts = ∀ a b → Coproduct a b

module Binary-coproducts (all-coproducts : has-coproducts) where

  module coproduct {a} {b} = Coproduct (all-coproducts a b)

  open coproduct renaming
    (unique to []-unique) public
  open Functor

  infixr 7 _⊕₀_
  infix 50 _⊕₁_

  _⊕₀_ : Ob → Ob → Ob
  a ⊕₀ b = coproduct.coapex {a} {b}

  _⊕₁_ : ∀ {a b x y} → Hom a x → Hom b y → Hom (a ⊕₀ b) (x ⊕₀ y)
  f ⊕₁ g = [ ι₁ ∘ f , ι₂ ∘ g ]

  ⊕-functor : Functor (C ×ᶜ C) C
  ⊕-functor .F₀ (a , b) = a ⊕₀ b
  ⊕-functor .F₁ (f , g) = f ⊕₁ g
  ⊕-functor .F-id = sym $ []-unique id-comm-sym id-comm-sym
  ⊕-functor .F-∘ (f , g) (h , i) =
    sym $ []-unique
      (pullr []∘ι₁ ∙ extendl []∘ι₁)
      (pullr []∘ι₂ ∙ extendl []∘ι₂)

  ∇ : ∀ {a} → Hom (a ⊕₀ a) a
  ∇ = [ id , id ]

  coswap : ∀ {a b} → Hom (a ⊕₀ b) (b ⊕₀ a)
  coswap = [ ι₂ , ι₁ ]

  ⊕-assoc : ∀ {a b c} → Hom (a ⊕₀ (b ⊕₀ c)) ((a ⊕₀ b) ⊕₀ c)
  ⊕-assoc = [ ι₁ ∘ ι₁ , [ ι₁ ∘ ι₂ , ι₂ ] ]

  ∇-coswap : ∀ {a} → ∇ ∘ coswap ≡ ∇ {a}
  ∇-coswap = []-unique (pullr []∘ι₁ ∙ []∘ι₂) (pullr []∘ι₂ ∙ []∘ι₁)

  ∇-assoc : ∀ {a} → ∇ {a} ∘ (∇ {a} ⊕₁ id) ∘ ⊕-assoc ≡ ∇ ∘ (id ⊕₁ ∇)
  ∇-assoc = unique₂
    (pullr (pullr []∘ι₁) ∙ (refl⟩∘⟨ pulll []∘ι₁) ∙ pulll (pulll []∘ι₁) ∙ pullr []∘ι₁)
    (pullr (pullr []∘ι₂) ∙ []-unique
      (pullr (pullr []∘ι₁) ∙ extend-inner []∘ι₁ ∙ cancell []∘ι₁ ∙ []∘ι₂)
      (pullr (pullr []∘ι₂) ∙ (refl⟩∘⟨ []∘ι₂) ∙ pulll []∘ι₂ ∙ idl _))
    (pullr []∘ι₁ ∙ pulll []∘ι₁)
    (pullr []∘ι₂ ∙ pulll []∘ι₂ ∙ idl _)

  ∇-natural : is-natural-transformation (⊕-functor F∘ Cat⟨ Id , Id ⟩) Id λ _ → ∇
  ∇-natural x y f = unique₂
    (pullr []∘ι₁ ∙ cancell []∘ι₁) (pullr []∘ι₂ ∙ cancell []∘ι₂)
    (cancelr []∘ι₁) (cancelr []∘ι₂)
```
