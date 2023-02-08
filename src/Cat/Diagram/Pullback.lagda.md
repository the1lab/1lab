```agda
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Shape.Cospan
open import Cat.Prelude

import Cat.Reasoning

module Cat.Diagram.Pullback {o ℓ} (C : Precategory o ℓ) where
```

# Pullbacks

<!--
```agda
open import Cat.Reasoning C
private variable
  p p' x y z : Ob
  h p₁' p₂' f g : Hom x y

open Functor
open _=>_
```
-->

A **pullback** $X \times_Z Y$ of $f : X \to Z$ and $g : Y \to Z$ is the
[product] of $f$ and $g$ in the category $\cC/Z$, the category of
objects fibred over $Z$. We note that the fibre of $X \times_Z Y$ over
some element $x$ of $Z$ is the product of the fibres of $f$ and $g$ over
$x$; Hence the pullback is also called the **fibred product**.

[product]: Cat.Diagram.Product.html

We can define equalisers as [limits] of [cospans].

[cospans]: Cat.Instances.Shape.Cospan.html

```agda
is-pullback
  : ∀ {p₁ : Hom p x} {f : Hom x z} {p₂ : Hom p y} {g : Hom y z}
  → f ∘ p₁ ≡ g ∘ p₂
  → Type _
is-pullback {p = p} {f = f} {g = g} square =
  is-limit {C = C} (Cospan lzero lzero f g) p (cospan-cone lzero lzero square)

Pullback : Hom x z → Hom y z → Type _
Pullback f g = Limit {C = C} (Cospan lzero lzero f g)
```

## Concretely

The concrete incarnation of the abstract nonsense above is that a
pullback turns out to be a universal square like the one below. Since it
is a product, it comes equipped with projections $\pi_1$ and $\pi_2$
onto its factors; Since isn't merely a product of $X$ and $Y$, but
rather of $X$ and $Y$ considered as objects over $Z$ in a specified way,
overall square has to commute.

~~~{.quiver}
\[\begin{tikzcd}
  P && Y \\
  \\
  X && Z
  \arrow["g", from=1-3, to=3-3]
  \arrow["f"', from=3-1, to=3-3]
  \arrow["{\pi_1}"', from=1-1, to=3-1]
  \arrow["{\pi_2}", from=1-1, to=1-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

```agda
record make-is-pullback
  (p₁ : Hom p x) (f : Hom x z) (p₂ : Hom p y) (g : Hom y z)
  : Type (o ⊔ ℓ)
  where
  no-eta-equality
  field
    square    : f ∘ p₁ ≡ g ∘ p₂
    universal
      : ∀ {p'} {p₁' : Hom p' x}  {p₂' : Hom p' y}
      → f ∘ p₁' ≡ g ∘ p₂' → Hom p' p
    p₁∘universal : ∀ {q : f ∘ p₁' ≡ g ∘ p₂'} → p₁ ∘ universal q ≡ p₁'
    p₂∘universal : ∀ {q : f ∘ p₁' ≡ g ∘ p₂'} → p₂ ∘ universal q ≡ p₂'
    unique
      : ∀ {q : f ∘ p₁' ≡ g ∘ p₂'} {other : Hom p' p}
      → p₁ ∘ other ≡ p₁'
      → p₂ ∘ other ≡ p₂'
      → other ≡ universal q

  unique₂ 
    : ∀ {o1 o2 : Hom p' p}
      → f ∘ p₁' ≡ g ∘ p₂'
      → p₁ ∘ o1 ≡ p₁' → p₂ ∘ o1 ≡ p₂'
      → p₁ ∘ o2 ≡ p₁' → p₂ ∘ o2 ≡ p₂'
      → o1 ≡ o2
  unique₂ p q r s t = unique {q = p} q r ∙ sym (unique s t)
```

By universal, we mean that any other "square" (here the second "square"
has corners $P'$, $X$, $Y$, $Z$ --- it's a bit bent) admits a unique
factorisation that passes through $P$; We can draw the whole situation
as in the diagram below. Note the little corner on $P$, indicating that
the square is a pullback.

~~~{.quiver .tall-2}
\[\begin{tikzcd}
  {P'} \\
  & P && Y \\
  \\
  & X && Z
  \arrow["g", from=2-4, to=4-4]
  \arrow["f"', from=4-2, to=4-4]
  \arrow["{\pi_1}"', from=2-2, to=4-2]
  \arrow["{\pi_2}", from=2-2, to=2-4]
  \arrow["{\exists! }", dashed, from=1-1, to=2-2]
  \arrow["{p_2}", curve={height=-12pt}, from=1-1, to=2-4]
  \arrow["{p_1}", curve={height=12pt}, from=1-1, to=4-2]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=2-2, to=4-4]
\end{tikzcd}\]
~~~

If we have an element of `make-is-pullback`{.Agda}, we can then construct
an element of `is-pullback`{.Agda}.

```agda
to-is-pullback
  : ∀ {p₁ : Hom p x} {f : Hom x z} {p₂ : Hom p y} {g : Hom y z}
  → (mkpb : make-is-pullback p₁ f p₂ g)
  → is-pullback (make-is-pullback.square mkpb)
to-is-pullback {p = p} {p₁ = p₁} {f} {p₂} {g} mkpb =
  to-is-limitp ml λ where
    {cs-a} → refl
    {cs-b} → refl
    {cs-c} → refl
  where
    module mkpb = make-is-pullback mkpb
    open make-is-limit

    ml : make-is-limit (Cospan lzero lzero f g) p
    ml .ψ cs-a = p₁
    ml .ψ cs-b = p₂
    ml .ψ cs-c = f ∘ p₁
    ml .commutes {cs-a} {cs-a} f = idl _
    ml .commutes {cs-a} {cs-c} f = refl
    ml .commutes {cs-b} {cs-b} f = idl _
    ml .commutes {cs-b} {cs-c} f = sym mkpb.square
    ml .commutes {cs-c} {cs-c} f = idl _
    ml .universal eta p =
      mkpb.universal (p {cs-a} {cs-c} _ ∙ sym (p {cs-b} {cs-c} _))
    ml .factors {j = cs-a} eta p =
      mkpb.p₁∘universal
    ml .factors {j = cs-b} eta p =
      mkpb.p₂∘universal
    ml .factors {j = cs-c} eta p =
      pullr mkpb.p₁∘universal ∙ p {cs-a} {cs-c} _
    ml .unique eta p other q =
       mkpb.unique (q cs-a) (q cs-b)
```

To use the data of `is-pullback`{.Agda}, we provide a function for
*un*making a pullback.

```agda
unmake-is-pullback
  : ∀ {p₁ : Hom p x} {f : Hom x z} {p₂ : Hom p y} {g : Hom y z}
  → {square : f ∘ p₁ ≡ g ∘ p₂}
  → is-pullback square
  → make-is-pullback p₁ f p₂ g
unmake-is-pullback {p = p} {x = x} {y = y} {p₁ = p₁} {f} {p₂} {g} {comm} lim = pb
  module unmake-pullback where
    open make-is-pullback
    module lim = is-limit lim

    cospan
      : ∀ {p} → Hom p x → Hom p y
      → (j : Cospan-ob lzero)
      → Hom p (Cospan lzero lzero {C = C} f g .F₀ j)
    cospan p₁' p₂' cs-a = p₁'
    cospan p₁' p₂' cs-b = p₂'
    cospan p₁' p₂' cs-c = f ∘ p₁'

    pb : make-is-pullback p₁ f p₂ g
    pb .square = comm
    pb .universal {p₁' = p₁'} {p₂' = p₂'} p =
      lim.universal (cospan p₁' p₂') λ where
        {cs-a} {cs-a} f → idl _
        {cs-a} {cs-c} f → refl
        {cs-b} {cs-b} f → idl _
        {cs-b} {cs-c} f → sym p
        {cs-c} {cs-c} f → idl _
    pb .p₁∘universal =
      lim.factors {j = cs-a} (cospan _ _) _
    pb .p₂∘universal =
      lim.factors {j = cs-b} (cospan _ _) _
    pb .unique p1 p2 =
      lim.unique (cospan _ _) _ _ λ where
        cs-a → p1
        cs-b → p2
        cs-c → pullr p1
```

<!--
```agda
module is-pullback
  {p₁ : Hom p x} {f : Hom x z} {p₂ : Hom p y} {g : Hom y z}
  {square : f ∘ p₁ ≡ g ∘ p₂}
  (pb : is-pullback square)
  where

  open make-is-pullback (unmake-is-pullback pb) public
```
-->

We perform a similar construction for the bundled form of pullbacks.

```agda
record make-pullback (f : Hom x z) (g : Hom y z) : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    apex : Ob
    p₁ : Hom apex x
    p₂ : Hom apex y
    has-is-pullback : make-is-pullback p₁ f p₂ g

  open make-is-pullback public
```

<!--
```agda
to-pullback : make-pullback f g → Pullback f g
to-pullback mpb = to-limit (to-is-pullback has-is-pullback)
  where open make-pullback mpb


module Pullback {f : Hom x z} {g : Hom y z} (pb : Pullback f g) where
  open Limit pb renaming (apex to L-apex)

  apex : Ob
  apex = L-apex

  p₁ : Hom apex x
  p₁ = ψ cs-a

  p₂ : Hom apex y
  p₂ = ψ cs-b

  square : f ∘ p₁ ≡ g ∘ p₂
  square = commutes {y = cs-c} (lift tt) ∙ sym (commutes {y = cs-c} (lift tt))

  has-is-pullback : is-pullback square
  has-is-pullback =
    to-is-limitp (unmake-limit has-limit) λ where
      {cs-a} → refl
      {cs-b} → refl
      {cs-c} → sym (commutes (lift tt))
```
-->
