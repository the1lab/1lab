---
description: |
  Injective objects.
---
<!--
```agda
open import Cat.Diagram.Pullback.Properties
open import Cat.Diagram.Product.Indexed
open import Cat.Diagram.Pullback.Along
open import Cat.Diagram.Pullback
open import Cat.Functor.Morphism
open import Cat.Diagram.Product
open import Cat.Diagram.Omega
open import Cat.Functor.Hom
open import Cat.Prelude hiding (Ω; true)

open import Data.Set.Projective
open import Data.Set.Surjection

import Cat.Displayed.Instances.Subobjects.Reasoning as Subr
import Cat.Displayed.Instances.Subobjects as Subobjs
import Cat.Reasoning
```
-->
```agda
module Cat.Diagram.Injective
  {o ℓ}
  (C : Precategory o ℓ)
  where
```

<!--
```agda
open Cat.Reasoning C
open Subobjs C

private variable
  A X Y : Ob
```
-->

# Injective objects

:::{.definition #injective-object}
Let $\cC$ be a precategory. An object $A : \cC$ is **injective**
if for every morphism $i : X \to A$ and [[monomorphism]] $e : X \epi Y$,
there merely exists an extension $r : Y \to A$ such that $r \circ m = i$, as in the
following diagram:

~~~{.quiver}
\begin{tikzcd}
  X && A \\
  \\
  Y
  \arrow["i", from=1-1, to=1-3]
  \arrow["m"', tail, from=1-1, to=3-1]
  \arrow["{\exists r}"', dashed, from=3-1, to=1-3]
\end{tikzcd}
~~~

More concisely, $A$ is injective if it has the right-lifting property
relative to monomorphisms in $\cC$.
:::


```agda
is-injective : (A : Ob) → Type _
is-injective A =
  ∀ {X Y} (i : Hom X A) (m : X ↪ Y)
  → ∃[ r ∈ Hom Y A ] (r ∘ m .mor ≡ i)
```

## A functorial definition

Some authors prefer to define injective objects via a functorial
approach. In particular, an object $A : \cC$ is injective if and only
if the $\hom$-functor $\cC(-,A) : \cC\op \to \Sets$ preserves [[epimorphisms]].

For the forward direction, recall that in $\Sets$, [[epis are surjective]].
Moreover, epimorphisms in $\cC\op$ are monomorphisms in $\cC$. This means that if
$m : X \mono Y$ is a mono in $\cC$, then $- \circ m : \cC(Y,A) \to \cC(X,A)$
is surjective, as $\cC(-,A)$ preserves
epis. This directly gives us the factorization we need!

```agda
preserves-epis→injective
  : preserves-epis (Hom-into C A)
  → is-injective A
preserves-epis→injective {A = A} hom-epi {X = X} {Y = Y} i m =
  epi→surjective (el! (Hom Y A)) (el! (Hom X A))
    (_∘ m .mor)
    (λ {c} → hom-epi (m .monic) {c = c})
    i
```

For the reverse direction, let $A$ be injective, $m : X \mono Y$ be a
mono, and $g, h : \cC(X, A) \to K$ be a pair of functions into an arbitrary
set $K$ such that $g(r \circ m) = h(r \circ m)$ for any $r : \cC(X, A)$.
To show that $\cC(P,-)$ preserves epis, we must show that $g = h$, which
follows directly from the existence of an extension for every $\cC(X,A)$.

```agda
injective→preserves-epis
  : is-injective A
  → preserves-epis (Hom-into C A)
injective→preserves-epis inj {f = m} m-mono g h p =
  ext λ k →
    rec! (λ r r-retract →
      g k        ≡˘⟨ ap g r-retract ⟩
      g (r ∘ m)  ≡⟨ p $ₚ r ⟩
      h (r ∘ m)  ≡⟨ ap h r-retract ⟩
      h k  ∎)
      (inj k (make-mono m m-mono))
```

## Closure of injectives

Projective objects are equipped with a mapping-in property, so they
tend to interact nicely with other constructions that are also characterised
via mapping-in properties. For instance, f $P$ and $Q$ are both injective,
then their [[product]] $P + Q$ is injective (if it exists).

```agda
product-injective
  : ∀ {A B A×B} {π₁ : Hom A×B A} {π₂ : Hom A×B B}
  → is-injective A
  → is-injective B
  → is-product C π₁ π₂
  → is-injective A×B
```

The proof is a nice extension chase. Our goal is to fill the dashed
line in the following diagram.

~~~{.quiver}
\begin{tikzcd}
  X && {A \times B} \\
  \\
  Y
  \arrow["i"from=1-1, to=1-3]
  \arrow["m"', tail, from=1-1, to=3-1]
  \arrow[dashed, from=3-1, to=1-3]
\end{tikzcd}
~~~

Both $A$ and $B$ are projective, so we can extend $\pi_1 \circ i$ and $\pi_2 \circ i$
along $m$ to get a pair of maps $r_1 : Y \to A$ and $r_2 : Y \to B$.

~~~{.quiver}
\begin{tikzcd}
  A & {A\times B} & X & {A \times B} & B \\
  \\
  && Y
  \arrow["{\pi_1}"', from=1-2, to=1-1]
  \arrow["i"', from=1-3, to=1-2]
  \arrow["i", from=1-3, to=1-4]
  \arrow["m"', tail, from=1-3, to=3-3]
  \arrow["{\pi_2}", from=1-4, to=1-5]
  \arrow["{r_2}", dashed, from=3-3, to=1-1]
  \arrow["{r_1}"', dashed, from=3-3, to=1-5]
\end{tikzcd}
~~~

Finally, we can use the universal property of the product to
combine $r_1$ and $r_2$ into a map $\langle r_1 , r_2 \rangle : Y \to A \times B$.
Moreover, $\pi_1 \circ \langle r_1 , r_2 \rangle \circ m = r_1 \circ m = i$ and
$\pi_2 \circ \langle r_1 , r_2 \rangle \circ m = r_2 \circ m = i$, so $\langle r_1, r_2 \rangle$
is a valid extension.

```agda
product-injective {π₁ = π₁} {π₂ = π₂} A-inj B-inj prod i m = do
  (r₁ , r₁-factor) ← A-inj (π₁ ∘ i) m
  (r₂ , r₂-factor) ← B-inj (π₂ ∘ i) m
  pure (⟨ r₁ , r₂ ⟩ , unique₂ (pulll π₁∘⟨⟩) (pulll π₂∘⟨⟩) (sym r₁-factor) (sym r₂-factor))
  where open is-product prod
```

We can extend this result to [[indexed products]], provided that
the indexing type is [[set projective]].

```agda
indexed-coproduct-projective
  : ∀ {κ} {Idx : Type κ}
  → {Aᵢ : Idx → Ob} {∏Aᵢ : Ob} {π : ∀ i → Hom ∏Aᵢ (Aᵢ i)}
  → is-set-projective Idx ℓ
  → (∀ i → is-injective (Aᵢ i))
  → is-indexed-product C Aᵢ π
  → is-injective ∏Aᵢ
```

The idea of the proof is the same as the non-indexed case. We start with
a diagram of the following shape.

~~~{.quiver}
\begin{tikzcd}
  X && {\prod_{i: I} A_i} \\
  \\
  Y
  \arrow["\iota", from=1-1, to=1-3]
  \arrow["m"', tail, from=1-1, to=3-1]
\end{tikzcd}
~~~

Our plan is to construct componentwise extensions $r_i : \cC(Y, A_i)$ for each
of the components of the product, and then use the universal property to
staple them all together into a single extension $\langle r_i \rangle : \cC(Y, \prod_{i : I} A_i)$.

However, there is a snag in this plan: we only get the mere existence of
each extension $r_i$ for each $i : I$, whereas we need the mere existence of
*all* the extensions simultaneously. In general, this requires the [[axiom of choice]],
but we can avoid this by requiring that $I$ be set-projective.

```agda
indexed-coproduct-projective {Aᵢ = Aᵢ} {π = π} Idx-pro Aᵢ-inj prod {X = X} {Y = Y} ι m = do
  r ← Idx-pro
    (λ i → Σ[ rᵢ ∈ Hom Y (Aᵢ i) ] rᵢ ∘ m .mor ≡ π i ∘ ι)
    (λ _ → hlevel 2)
    (λ i → Aᵢ-inj i (π i ∘ ι) m)
  pure (tuple (λ i → r i .fst) , unique₂ (λ i → pulll commute ∙ r i .snd))
  where open is-indexed-product prod
```

Injectives are also closed under sections. This follows by a straightforward bit of algebra.

```agda
section→injective
  : ∀ {S A}
  → is-injective A
  → (r : Hom A S)
  → has-section r
  → is-injective S
section→injective A-inj r s i m = do
  (t , t-factor) ← A-inj (s .section ∘ i) m
  pure (r ∘ t , pullr t-factor ∙ cancell (s .is-section))
```

If $\cC$ has all [[pullbacks]], then every [[subobject classifier]]
is injective.

```agda
Ω-injective
  : {Ω : Ob} {true : Subobject Ω}
  → has-pullbacks C
  → is-generic-subobject C true
  → is-injective Ω
```

Let $(\Omega, \mathrm{true})$ be a subobject classifier in $\cC$, and
consider the following extension problem.

~~~{.quiver}
\begin{tikzcd}
  X && \Omega \\
  \\
  Y
  \arrow["i", from=1-1, to=1-3]
  \arrow["m"', tail, from=1-1, to=3-1]
  \arrow["{?}"{description}, dashed, from=3-1, to=1-3]
\end{tikzcd}
~~~

```agda
Ω-injective {Ω = Ω} {true = true} pullbacks Ω-subobj {X} {Y} i m =
  pure extension
  where
    open is-generic-subobject Ω-subobj
    open Pullbacks C pullbacks
    open props pullbacks (record { true = true ; generic = Ω-subobj })
```

At first glance, it seems like we might be able to just classify the
subobject $m$ to get an extension $\mathrm{name}(m) : \cC(Y, \Omega)$. Though this map
does have the right type, it is not actually an extension of $i$.
The core of the problem is that $\mathrm{name}(m)$ classifies generalized
elements of $Y$ that lie within $m$, but we need to classify generalized
elements of $Y$ that lie within $i$ instead!

We can this by pulling back $i$ along $\mathrm{true}$ to get a subobject $[i]$ of
$X$, which we can then compose with $m$ to get a subobject of $Y$.

~~~{.quiver}
\begin{tikzcd}
  {\mathrm{dom}(i)} && \top \\
  \\
  X && \Omega \\
  \\
  Y
  \arrow["{!}", from=1-1, to=1-3]
  \arrow["{[i]}"', from=1-1, to=3-1]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
  \arrow["{\mathrm{true}}", from=1-3, to=3-3]
  \arrow["i", from=3-1, to=3-3]
  \arrow["m"', tail, from=3-1, to=5-1]
  \arrow["{?}"{description}, dashed, from=5-1, to=3-3]
\end{tikzcd}
~~~

```agda
    [i] : Subobject X
    [i] = named i

    m∩[i] : Subobject Y
    m∩[i] = cutₛ (∘-is-monic (m .monic) ([i] .monic))
```

We can then classify our subobject $m \circ [i]$ to get a map
$\mathrm{name}(m \circ [i]) : \cC(Y, \Omega)$, which is an
extension of $i$.

To see this, recall that two maps $f, g : \cC(X,\Omega)$ are equal
when $[g] : \cC(\mathrm{dom}(g), X)$ is a pullback of $\mathrm{true}$
along $f$. In our case, this means that we must show that the following
square is a pullback square.

~~~{.quiver}
\begin{tikzcd}
  {\mathrm{dom}(i)} && \top \\
  \\
  X && \Omega
  \arrow["{!}", from=1-1, to=1-3]
  \arrow["{[i]}"', from=1-1, to=3-1]
  \arrow["{\mathrm{true}}", from=1-3, to=3-3]
  \arrow["{\mathrm{name}(m \circ [i]) \circ m}"', from=3-1, to=3-3]
\end{tikzcd}
~~~

We can re-arrange this square a bit to get the following diagram.

~~~{.quiver}
\begin{tikzcd}
  {\mathrm{dom}(i)} && {\mathrm{dom}(i)} && \top \\
  \\
  X && Y && \Omega
  \arrow["\id", from=1-1, to=1-3]
  \arrow["{[i]}"', from=1-1, to=3-1]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
  \arrow["{!}", from=1-3, to=1-5]
  \arrow["{m \circ [i]}"{description}, from=1-3, to=3-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-3, to=3-5]
  \arrow["{\mathrm{true}}", from=1-5, to=3-5]
  \arrow["m"', from=3-1, to=3-3]
  \arrow["{\mathrm{name}(m \circ [i])}"', from=3-3, to=3-5]
\end{tikzcd}
~~~

The right-hand square is a pullback square, as $\mathrm{name}(m \circ [i])$
classifies the subobject $m \circ [i]$. Moreover, the left-hand square
is also a pullback square, as every $f$ is the pullback of $m \circ f$
along $m$ when $m$ is monic. We can paste these two squares together to
get our original square, which must also be a pullback by pasting.
This means that $\mathrm{name}(m \circ [i]) \circ m = i$, which completes
the proof.

```agda
    extension : Σ[ i* ∈ Hom Y Ω ] i* ∘ m .mor ≡ i
    extension .fst = name m∩[i]
    extension .snd =
      Ω-unique₂ $
      paste-is-pullback-along
        (classifies m∩[i])
        (is-pullback-along-monic (m .monic))
        refl
```

## Enough injectives

:::{.definition #enough-injectives}
A category $\cC$ is said to have **enough injectives** if for
every object $X : \cC$ there is some $X \mono A$ with $A$ injective.
We will refer to $A$ as the **injective resolution** of $X$.
:::

Note that there are two variations on this condition: one where
there *merely* exists a injective resolution for every $X$, and
another where those resolutions are provided as structure. We prefer
to work with the latter, as it tends to be less painful to work with.

```agda
record Injectives : Type (o ⊔ ℓ) where
  field
    Inj : Ob → Ob
    inj-resolve : ∀ {X} → X ↪ Inj X
    inj-injective : ∀ {X} → is-injective (Inj X)
```
