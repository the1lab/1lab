<!--
```agda
open import 1Lab.Prelude

open import Homotopy.Space.Suspension
```
-->


```agda
module Homotopy.Pushout where
```

# Pushouts {defines="pushout"}

Given the following span:

~~~{.quiver}
\begin{tikzpicture}
\node[] (c) at (0, 0) {$C$};
\node[] (a) at (0, -2) {$A$};
\node[] (b) at (2, 0) {$B$};
\draw[->] (c) -- (a) node[midway,xshift=-10]{${f}$};
\draw[->] (c) -- (b) node[midway,above]{${g}$};
\end{tikzpicture}
~~~

The `Pushout`{.Agda} of this span is defined as the higher inductive type
presented by:
```agda
data Pushout {ℓ} (C : Type ℓ)
                 (A : Type ℓ) (f : C → A)
                 (B : Type ℓ) (g : C → B)
                 : Type ℓ where
```

Two functions `inl`{.Agda} and `inr`{.Agda}, that "connect" from `A` and `B`:

```agda
  inl : A → Pushout C A f B g
  inr : B → Pushout C A f B g
```

And, for every `c : C`, a path
`commutes : inl (f c) ≡ inr (g c)`{.Agda}:

```agda
  commutes : ∀ c → inl (f c) ≡ inr (g c)
```

These combine to give the following:

~~~{.quiver}
\begin{tikzpicture}
\node[] (c) at (0, 0) {$C$};
\node[] (a) at (0, -2) {$A$};
\node[] (b) at (2, 0) {$B$};
\node[] (d) at (2, -2) {$Push$};
\draw[->] (c) -- (a) node[midway,xshift=-10]{${f}$};
\draw[->] (c) -- (b) node[midway,above]{${g}$};
\draw[->] (a) -- (d) node[midway,below]{$inl$};
\draw[->] (b) -- (d) node[midway,right]{$inr$};

\draw[->,shorten <=0.2cm,shorten >=0.2cm,very thick] (a) -- (b) node[midway,above left]{$h$};
\end{tikzpicture}
~~~
where $h$ is our path `commutes`{.Agda}, and $Push$ our Pushout. [^comm].

[^comm]: Big words, small diagram.

## Suspensions as Pushouts

First, recall the `Susp`{.Agda}, which serves to increase the
connectedness of a space. Suspension can be expressed as a
`Pushout`{.Agda} of some type
$A$, alongside two instaces of $⊤$; i.e., the span `⊤ ← A → ⊤`{.Agda}
or the following:

~~~{.quiver}
\begin{tikzpicture}
\node[] (c) at (0, 0) {$C$};
\node[] (a) at (0, -2) {$\top$};
\node[] (b) at (2, 0) {$\top$};
\draw[->] (c) -- (a) node[midway,xshift=-15]{$\rm{con}$};
\draw[->] (c) -- (b) node[midway,above]{$\rm{con}$};
\end{tikzpicture}
~~~

where 

```agda
to-top : {A : Type} → A → ⊤
to-top _ = tt
```
There is only one element of `⊤`{.Agda}, and hence only one choice
for the function projecting into `⊤`{.Agda}.

If one considers the structure we're creating, it becomes very
obvious that this is equivalent to suspension - we take our
`inl`{.Agda} and `inr`{.Agda} constructors to `N`{.Agda} and
`S`{.Agda}, as the input into them is now `⊤`{.Agda}, which only
has one element anyway. Likewise, we turn `commutes`{.Agda} into
`merid`{.Agda}, as our functions `f`{.Agda} and `g`{.Agda} can only
be `con`{.Agda}, so it reduces (with a suitable element of `C`{.Agda})
from `∀ c → inl (f c) ≡ inr (g c)`{.Agda} to `inl tt ≡ inr tt`{.Agda}, or
by funext, `inl ≡ inr`{.Agda}.

We therefore aim to show:

```agda
Susp≡Pushout-⊤←A→⊤ : ∀ {A} → Susp A ≡ Pushout A ⊤ to-top ⊤ to-top
```

The left and right functions are very simple:

```agda
Susp→Pushout-⊤←A→⊤ : ∀ {A} → Susp A → Pushout A ⊤ to-top ⊤ to-top
Susp→Pushout-⊤←A→⊤ N = inl tt
Susp→Pushout-⊤←A→⊤ S = inr tt
Susp→Pushout-⊤←A→⊤ (merid x i) = commutes x i

Pushout-⊤←A→⊤→Susp : ∀ {A} → Pushout A ⊤ to-top ⊤ to-top → Susp A
Pushout-⊤←A→⊤→Susp (inl x) = N
Pushout-⊤←A→⊤→Susp (inr x) = S
Pushout-⊤←A→⊤→Susp (commutes c i) = merid c i
```

We then have:

```agda
Susp≡Pushout-⊤←A→⊤ = ua (Susp→Pushout-⊤←A→⊤ , is-iso→is-equiv iso-pf) where
```

<details><summary> We then verify that our two functions above are in fact
an equivalence. This is entirely `refl`{.Agda}, due to the noted
similarities in structure.</summary>
```agda
  open is-iso

  iso-pf : is-iso Susp→Pushout-⊤←A→⊤
  iso-pf .inv = Pushout-⊤←A→⊤→Susp
  iso-pf .rinv (inl x) = refl
  iso-pf .rinv (inr x) = refl
  iso-pf .rinv (commutes c i) = refl
  iso-pf .linv N = refl
  iso-pf .linv S = refl
  iso-pf .linv (merid x i) = refl
```
</details>

## The Universal property of a pushout

We can also formulate the universal property of a pushout. We first
do this by introducing the `cocone`{.Adga}. A `cocone`{.Agda},
given a type `D`{.Agda} and a span $\mathcal{D}$:

~~~{.quiver}
\begin{tikzpicture}
\node[] (c) at (2, 0) {$C$};
\node[] (a) at (0, 0) {$A$};
\node[] (b) at (4, 0) {$B$};
\draw[->] (c) -- (a) node[midway,above]{${f}$};
\draw[->] (c) -- (b) node[midway,above]{${g}$};
\end{tikzpicture}
~~~

consists of functions:
<!--
```agda
module _ (A B C D : Type) (f : C → A) (g : C → B)
  (i' : A → D) (j' : B → D) (h' : (c : C) → i' (f c) ≡ j' (g c))
  where
```
-->
```agda
  i : A → D
  j : B → D
``` 
and a homotopy
```agda
  h : (c : C) → i (f c) ≡ j (g c)
```
<!--
```agda
  i = i'
  j = j'
  h = h'
```
-->
forming:

~~~{.quiver}
\begin{tikzpicture}
\node[] (c) at (0, 0) {$C$};
\node[] (a) at (0, -2) {$A$};
\node[] (b) at (2, 0) {$B$};
\node[] (d) at (2, -2) {$D$};
\draw[->] (c) -- (a) node[midway,xshift=-10]{${f}$};
\draw[->] (c) -- (b) node[midway,above]{${g}$};
\draw[->] (a) -- (d) node[midway,below]{$i$};
\draw[->] (b) -- (d) node[midway,right]{$j$};
\draw[->,shorten <=0.2cm,shorten >=0.2cm,very thick] (a) -- (b) node[midway,above left]{$h$};
\end{tikzpicture}
~~~

One can then note the similarities between this definition,
and our previous `Pushout`{.Agda} definition. We denote the type of `cocone`{.Agda}s as:

```agda
cocone : {C A B : Type} → (f : C → A) → (g : C → B) → (D : Type) → Type
cocone {C} {A} {B} f g D =
  Σ[ i ∈ (A → D) ]
    Σ[ j ∈ (B → D) ]
      ((c : C) → i (f c) ≡ j (g c))
```

We can then show that the canonical `cocone`{.Agda} consisting of a `Pushout`{.Agda}
is the universal `cocone`{.Agda}.

```agda
Pushout→E≡coconeE : ∀ {A B C E f g} →
                    (Pushout C A f B g → E) ≡ (cocone f g E)
Pushout→E≡coconeE = ua ( pushout→cocone , is-iso→is-equiv iso-pc ) where
```

<details><summary> Once again we show that the above is an equivalence;
this proof is essentially a transcription of Lemma 6.8.2 in the [HoTT](HoTT.html) book,
and again mostly reduces to `refl`{.Agda}.
</summary>
```agda
  open is-iso

  pushout→cocone : ∀ {A B C E f g} → (Pushout C A f B g → E) → cocone f g E
  cocone→pushout : ∀ {A B C E f g} → cocone f g E → (Pushout C A f B g → E)
  iso-pc : is-iso pushout→cocone

  pushout→cocone t = (λ x → t (inl x)) ,
                     (λ x → t (inr x)) ,
                     (λ c i → ap t (commutes c) i)

  cocone→pushout t (inl x) = fst t x 
  cocone→pushout t (inr x) = fst (snd t) x
  cocone→pushout t (commutes c i) = snd (snd t) c i

  iso-pc .inv = cocone→pushout
  iso-pc .rinv _ = refl
  iso-pc .linv _ = funext (λ { (inl y) → refl;
                                (inr y) → refl;
                                (commutes c i) → refl
                           })
```
</details>
