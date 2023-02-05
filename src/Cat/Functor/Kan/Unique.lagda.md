```agda
open import Cat.Instances.Functor.Compose
open import Cat.Instances.Functor
open import Cat.Functor.Kan.Base
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning

module Cat.Functor.Kan.Unique where
```

# Uniqueness of Kan extensions

[Kan extensions] (both left and [right]) are [universal constructions],
so they are [unique when they exist]. To get a theorem out of this
intuition, we must be careful about how the structure and the properties
are separated: Informally, we refer to the _functor_ as "the Kan
extension", but in reality, the data associated with "the Kan extension
of $F$ along $p$" also includes the natural transformation. For
accuracy, using the setup from the diagram below, we should say “$(G,
\eta)$ is the Kan extension of $F$ along $p$".

[Kan extensions]: Cat.Functor.Kan.Base.html
[right]: Cat.Functor.Kan.Base.html#right-kan-extensions
[universal constructions]: Cat.Functor.Representable.html
[unique when they exist]: 1Lab.HLevel.html#is-prop

~~~{.quiver .tall-15}
\[\begin{tikzcd}
  C && D \\
  \\
  {C'}
  \arrow["F", from=1-1, to=1-3]
  \arrow["p"', from=1-1, to=3-1]
  \arrow[""{name=0, anchor=center, inner sep=0}, "G"', from=3-1, to=1-3]
  \arrow["\eta"', shorten <=6pt, Rightarrow, from=0, to=1-1]
\end{tikzcd}\]
~~~

<!--
```agda
private variable
  o ℓ : Level
  C C′ D : Precategory o ℓ

module
  Lan-unique
    {p : Functor C C′} {F : Functor C D}
    {G₁ G₂ : Functor C′ D} {η₁ η₂}
    (l₁ : is-lan p F G₁ η₁)
    (l₂ : is-lan p F G₂ η₂)
  where

  private
    module l₁ = is-lan l₁
    module l₂ = is-lan l₂
    module D = Cat.Reasoning D
    module C′D = Cat.Reasoning Cat[ C′ , D ]

  open C′D._≅_
  open C′D.Inverses
```
-->

To show uniqueness, suppose that $(G_1, \eta_1)$ and $(G_2, \eta_2)$ and
both left extensions of $F$ along $p$. Diagramming this with both
natural transformations shown is a bit of a nightmare: the option which
doesn't result in awful crossed arrows is to duplicate the span $\cC'
\ot \cC \to \cD$. So, to be clear: The upper triangle and the lower
triangle _are the same_.

~~~{.quiver}
\[\begin{tikzcd}
  && \cC \\
  \\
  {\cC'} &&&& \cD \\
  \\
  && \cC
  \arrow["F", from=1-3, to=3-5]
  \arrow["p"', from=1-3, to=3-1]
  \arrow[""{name=0, anchor=center, inner sep=0}, "{G_1}", curve={height=-12pt}, from=3-1, to=3-5]
  \arrow["p", from=5-3, to=3-1]
  \arrow["F"', from=5-3, to=3-5]
  \arrow[""{name=1, anchor=center, inner sep=0}, "{G_2}"', curve={height=12pt}, from=3-1, to=3-5]
  \arrow["{\eta_1}", shorten <=9pt, Rightarrow, from=0, to=1-3]
  \arrow["{\eta_2}"', shorten <=9pt, Rightarrow, from=1, to=5-3]
\end{tikzcd}\]
~~~

Recall that $(G_1, \eta_1)$ being a left extension means we can
(uniquely) factor natural transformations $F \to Mp$ through
transformations $G_1 \to M$. We want a map $G_1 \to G_2$, for which it
will suffice to find a map $F \to G_2p$ --- but $\eta_2$ is right there!
In the other direction, we can factor $\eta_1$ to get a map $G_2 \to
G_1$. Since these factorisations are unique, we have a natural
isomorphism.

```agda
  functor : natural-iso G₁ G₂
  functor = morp where
    morp : natural-iso G₁ G₂
    morp .to   = l₁.σ η₂
    morp .from = l₂.σ η₁
    morp .inverses .invl = l₂.σ-uniq₂ η₂
      (Nat-path λ x → sym (D.pullr (l₂.σ-comm ηₚ _) ∙ l₁.σ-comm ηₚ _))
      (Nat-path λ x → D.introl refl)
    morp .inverses .invr = l₁.σ-uniq₂ η₁
      (Nat-path λ x → sym (D.pullr (l₁.σ-comm ηₚ _) ∙ l₂.σ-comm ηₚ _))
      (Nat-path λ x → D.introl refl)
  module functor = C′D._≅_ functor
```

It's immediate from the construction that this isomorphism "sends
$\eta_1$ to $\eta_2$".

```agda
  unit : (functor.to ◂ p) ∘nt η₁ ≡ η₂
  unit = l₁.σ-comm
```

## Into univalent categories

As traditional with universal constructions, if $F : \cC \to \cD$ takes
values in a [univalent category], we can sharpen our result: the type of
left extensions of $F$ along $p$ is a proposition.

[univalent category]: Cat.Univalent.html#univalent-categories

```agda
Lan-is-prop
  : ∀ {p : Functor C C′} {F : Functor C D} → is-category D → is-prop (Lan p F)
Lan-is-prop {C = C} {C′ = C′} {D = D} {p = p} {F = F} d-cat L₁ L₂ = path where
```

<!--
```agda
  module L₁ = Lan L₁
  module L₂ = Lan L₂
  module Lu = Lan-unique L₁.has-lan L₂.has-lan

  open Lan

  c′d-cat : is-category Cat[ C′ , D ]
  c′d-cat = Functor-is-category d-cat
```
-->

That's because if $\cD$ is univalent, then [so is $[\cC',
\cD]$][functor-is-category], so our natural isomorphism $i : G_1 \cong
G_2$ is equivalent to an identification $i' : G_1 \equiv G_2$. Then, our
tiny lemma stating that this isomorphism "sends $\eta_1$ to $\eta_2$" is
precisely the data of a dependent identification $\eta_1 \equiv \eta_2$
over $i'$.

[functor-is-category]: Cat.Instances.Functor.html#functor-is-category

```agda
  functor-path : L₁.Ext ≡ L₂.Ext
  functor-path = c′d-cat .to-path Lu.functor

  eta-path : PathP (λ i → F => functor-path i F∘ p) L₁.eta L₂.eta
  eta-path = Nat-pathp _ _ λ x →
    Univalent.Hom-pathp-reflr-iso d-cat (Lu.unit ηₚ _)
```

Since being a left extension is always a proposition when applied to
$(G, \eta)$, even when the categories are not univalent, we can finish
our proof.

```agda
  path : L₁ ≡ L₂
  path i .Ext = functor-path i
  path i .eta = eta-path i
  path i .has-lan =
    is-prop→pathp (λ i → is-lan-is-prop {p = p} {F} {functor-path i} {eta-path i})
      L₁.has-lan L₂.has-lan i
```

<!--
```agda
module
  Ran-unique
    {p : Functor C C′} {F : Functor C D}
    {G₁ G₂ : Functor C′ D} {ε₁ ε₂}
    (r₁ : is-ran p F G₁ ε₁)
    (r₂ : is-ran p F G₂ ε₂)
  where

  private
    module r₁ = is-ran r₁
    module r₂ = is-ran r₂
    module D = Cat.Reasoning D
    module C′D = Cat.Reasoning Cat[ C′ , D ]

  open C′D._≅_
  open C′D.Inverses

  functor : natural-iso G₁ G₂
  functor = morp where
    morp : natural-iso G₁ G₂
    morp .to   = r₂.σ ε₁
    morp .from = r₁.σ ε₂
    morp .inverses .invl = r₂.σ-uniq₂ ε₂
      (Nat-path λ x → sym (D.pulll (r₂.σ-comm ηₚ _) ∙ r₁.σ-comm ηₚ _))
      (Nat-path λ x → D.intror refl)
    morp .inverses .invr = r₁.σ-uniq₂ ε₁
      (Nat-path λ x → sym (D.pulll (r₁.σ-comm ηₚ _) ∙ r₂.σ-comm ηₚ _))
      (Nat-path λ x → D.intror refl)
  module functor = C′D._≅_ functor

  counit : ε₁ ∘nt (functor.from ◂ p) ≡ ε₂
  counit = r₁.σ-comm

Ran-is-prop
  : ∀ {p : Functor C C′} {F : Functor C D} → is-category D → is-prop (Ran p F)
Ran-is-prop {C = C} {C′ = C′} {D = D} {p = p} {F = F} d-cat R₁ R₂ = path where
  module R₁ = Ran R₁
  module R₂ = Ran R₂
  module Ru = Ran-unique R₁.has-ran R₂.has-ran

  open Ran

  c′d-cat : is-category Cat[ C′ , D ]
  c′d-cat = Functor-is-category d-cat

  fp : R₁.Ext ≡ R₂.Ext
  fp = c′d-cat .to-path Ru.functor

  εp : PathP (λ i → fp i F∘ p => F) R₁.eps R₂.eps
  εp = Nat-pathp _ _ λ x → Univalent.Hom-pathp-refll-iso d-cat (Ru.counit ηₚ _)

  path : R₁ ≡ R₂
  path i .Ext = fp i
  path i .eps = εp i
  path i .has-ran =
    is-prop→pathp (λ i → is-ran-is-prop {p = p} {F} {fp i} {εp i})
      R₁.has-ran R₂.has-ran i
```
-->
