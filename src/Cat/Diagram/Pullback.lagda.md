```agda
open import Cat.Prelude

module Cat.Diagram.Pullback {ℓ ℓ′} (C : Precategory ℓ ℓ′) where
```

# Pullbacks

<!--
```agda
open import Cat.Reasoning C
private variable
  P′ X Y Z : Ob
  h p₁' p₂' : Hom X Y
```
-->

A **pullback** $X \times_Z Y$ of $f : X \to Z$ and $g : Y \to Z$ is the
[product] of $f$ and $g$ in the category $\ca{C}/Z$, the category of
objects fibred over $Z$. We note that the fibre of $X \times_Z Y$ over
some element $x$ of $Z$ is the product of the fibres of $f$ and $g$ over
$x$; Hence the pullback is also called the **fibred product**.

[product]: Cat.Diagram.Product.html

```agda
record is-pullback {P} (p₁ : Hom P X) (f : Hom X Z) (p₂ : Hom P Y) (g : Hom Y Z)
  : Type (ℓ ⊔ ℓ′) where

  field
    square   : f ∘ p₁ ≡ g ∘ p₂
```

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
    limiting : ∀ {P′} {p₁' : Hom P′ X} {p₂' : Hom P′ Y}
             → f ∘ p₁' ≡ g ∘ p₂' → Hom P′ P
    p₁∘limiting : {p : f ∘ p₁' ≡ g ∘ p₂'} → p₁ ∘ limiting p ≡ p₁'
    p₂∘limiting : {p : f ∘ p₁' ≡ g ∘ p₂'} → p₂ ∘ limiting p ≡ p₂'

    unique : {p : f ∘ p₁' ≡ g ∘ p₂'} {lim' : Hom P′ P}
           → p₁ ∘ lim' ≡ p₁'
           → p₂ ∘ lim' ≡ p₂'
           → lim' ≡ limiting p

  unique₂
    : {p : f ∘ p₁' ≡ g ∘ p₂'} {lim' lim'' : Hom P′ P}
    → p₁ ∘ lim' ≡ p₁' → p₂ ∘ lim' ≡ p₂'
    → p₁ ∘ lim'' ≡ p₁' → p₂ ∘ lim'' ≡ p₂'
    → lim' ≡ lim''
  unique₂ {p = o} p q r s = unique {p = o} p q ∙ sym (unique r s)
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

We provide a convenient packaging of the pullback and the projection
maps:

```agda
record Pullback {X Y Z} (f : Hom X Z) (g : Hom Y Z) : Type (ℓ ⊔ ℓ′) where
  field
    {apex} : Ob
    p₁ : Hom apex X
    p₂ : Hom apex Y
    has-is-pb : is-pullback p₁ f p₂ g

  open is-pullback has-is-pb public
```
