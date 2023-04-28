<!--
```agda
open import Cat.Diagram.Product
open import Cat.Diagram.Product.Solver
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Prelude

open import Cat.Internal.Opposite

import Cat.Reasoning
import Cat.Internal.Base
import Cat.Internal.Reasoning
```
-->

```agda
module Cat.Internal.Functor.Outer
  {o ℓ} {C : Precategory o ℓ}
  where
```

<!--
```agda
open import Cat.Reasoning C
open import Cat.Internal.Base C
open Internal-hom
```
-->

# Outer Functors

The category of sets is not strict, so it is not an internal category in
any category of sets, regardless of universes. However, the category of
sets still plays an important role in strict category theory, via functors
$\cC \to \thecat{Sets}$.

We wish to relativize this situation to an arbitrary base category $\cC$,
not just $\thecat{Sets}$. To do this, we use the age-old trick of viewing
a family of sets $X : I \to \set$ as a function *into* $I$. This is
easy to internalize: just replace function with morphism! However,
defining the action of morphisms is a bit more involved, as we shall see
shortly. We shall call these functors from $\ica{C}$ to the base $\cC$
*outer functors*.

```agda
module _ (ℂ : Internal-cat) where
  open Cat.Internal.Reasoning ℂ

  record Outer-functor : Type (o ⊔ ℓ) where
    no-eta-equality
```

The first piece of data we require is some object $P : \cC$ that will act
like the disjoint union of the image of our functor. If the base was
$\thecat{Sets}$, then this would simply be the type
$\Sigma (x : \ica{C}) P(x)$. Next, we require a map that takes a
generalized element of $P$ to a generalized element of the object of
objects; in $\thecat{Sets}$, this is simply the first projection.

```agda
    field
      ∫P : Ob
      P₀ : ∀ {Γ} → Hom Γ ∫P → Hom Γ C₀
```

We proceed by defining the action of morphisms. Intuitively, this just
takes an internal morphism from $x$ to $y$ to an endomap on $P$.
However, we need to ensure that this map takes the fibre of $P$ at
$x$ to the fibre of $P$ at $y$. This is handled via a bit of clever
indexing, along with a proof that ensures that the result lands in the
correct fibre.

```agda
      P₁ : ∀ {Γ} (px : Hom Γ ∫P) {y : Hom Γ C₀} → Homi (P₀ px) y → Hom Γ ∫P
      P₁-tgt : ∀ {Γ} (px : Hom Γ ∫P) {y : Hom Γ C₀}
             → (f : Homi (P₀ px) y) → y ≡ P₀ (P₁ px f)
```

Next, we have the functoriality conditions; nothing here is too surprising.

```agda
      P-id : ∀ {Γ} (px : Hom Γ ∫P) → P₁ px (idi (P₀ px)) ≡ px
      P-∘ : ∀ {Γ} (px : Hom Γ ∫P) {y z : Hom Γ C₀} (f : Homi y z) (g : Homi (P₀ px) y)
          → P₁ px (f ∘i g) ≡ P₁ (P₁ px g) (adjusti (P₁-tgt px g) refl f)
```

Finally, the naturality conditions that allow us to work using
generalized objects.

```agda
      P₀-nat : ∀ {Γ Δ} → (px : Hom Δ ∫P) → (σ : Hom Γ Δ) → P₀ px ∘ σ ≡ P₀ (px ∘ σ)
      P₁-nat : ∀ {Γ Δ} (px : Hom Δ ∫P) {y : Hom Δ C₀} (f : Homi (P₀ px) y) (σ : Hom Γ Δ)
        → P₁ px f ∘ σ ≡ P₁ (px ∘ σ) (adjusti (P₀-nat px σ) refl (f [ σ ]))

open Outer-functor
```

Another perspective on outer functors is that they are internal discrete
opfibrations over $\ica{C}$. The object $P$ is the [total space]
of the discrete opfibration, the mapping $P_0$ plays the role of the
fibration, and the mapping $P_1$ encodes the lifting property.

[total space]: Cat.Displayed.Total.html

We can obtain internal [discrete fibrations] by looking at outer functors
from the [internal opposite category] of $\ica{C}$.

[discrete fibrations]: Cat.Displayed.Cartesian.Discrete.html
[internal opposite category]: Cat.Internal.Opposite.html

<!-- [TODO: Reed M, 28/04/2023]
Link to the page on discrete opfibrations when it is written!
-->

## Internal Hom Functors

The canonical example of an outer functor is the internal analog of the
hom functor $\cC(X,-)$. Let $\cC$ be a finitely complete category,
$\ica{C}$ be an internal category in $\cC$, and let $x : \cC(\top, C_0)$
be a *global* element of the object of objects, which should be thought
of as an "external object" of $\ica{C}$.

```agda
module _ (pb : has-pullbacks C) (term : Terminal C) (ℂ : Internal-cat) where
  open Cat.Internal.Reasoning ℂ
  open Pullbacks C pb
  open Terminal term

  Internal-hom-from : (x : Hom top C₀) → Outer-functor ℂ
  Internal-hom-from x = outf where
```

Recall that defining an outer functor on $\ica{C}$ requires chosing
some $P : \cC$ that will play the role of the total space; for
hom functor, this ought to be the object of all morphisms with domain
$x$. We can encode this internally with the following pullback:

~~~{.quiver}
\begin{tikzcd}
  {C_x} && \top \\
  \\
  {C_1} && {C_0}
  \arrow["src", from=3-1, to=3-3]
  \arrow["x", from=1-3, to=3-3]
  \arrow[from=1-1, to=3-1]
  \arrow[from=1-1, to=1-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
\end{tikzcd}
~~~

The projection from the total space to $C_0$ takes a generalized element
of $C_x$ to it's codomain, and the lifting properties is obtained by
using the fact that $C_x$ is a pullback.

```agda
    open Pullback (pb src x) renaming (apex to Cₓ)

    outf : Outer-functor ℂ
    outf .∫P = Cₓ
    outf .P₀ fₓ = tgt ∘ p₁ ∘ fₓ
    outf .P₁ fₓ {y = y} g = universal coh
      module hom-from-action where abstract
        coh : src ∘ (g ∘i homi (p₁ ∘ fₓ)) .ihom ≡ x ∘ !
        coh =
          src ∘ (g ∘i homi (p₁ ∘ fₓ)) .ihom ≡⟨ (g ∘i homi (p₁ ∘ fₓ)) .has-src ⟩
          src ∘ p₁ ∘ fₓ ≡⟨ pulll square ⟩
          (x ∘ p₂) ∘ fₓ ≡⟨ pullr (sym (!-unique _)) ⟩
          x ∘ ! ∎
```

<details>
<summary>Functoriality follows the same general pattern as the ordinary
hom functor, though it is somewhat obscured by the pullback.
</summary>

```agda
    outf .P₁-tgt fₓ {y = y} g = tgt-coh where abstract
      tgt-coh : y ≡ tgt ∘ p₁ ∘ universal (hom-from-action.coh fₓ g)
      tgt-coh =
        y                                 ≡˘⟨ (g ∘i homi (p₁ ∘ fₓ)) .has-tgt ⟩
        tgt ∘ (g ∘i homi (p₁ ∘ fₓ)) .ihom ≡˘⟨ ap (tgt ∘_) p₁∘universal ⟩
        tgt ∘ p₁ ∘ universal _            ∎
    outf .P-id fₓ =
      sym $ unique (sym (ap ihom (idli _))) (sym (!-unique _))
    outf .P-∘ fₓ g h =
      unique
        (p₁∘universal
        ∙ ap ihom (sym $ associ _ _ _)
        ∙ ∘i-ihom
            (sym (ap (src ∘_) p₁∘universal ∙ (h ∘i homi (p₁ ∘ fₓ)) .has-src))
            (sym (ap (tgt ∘_) p₁∘universal ∙ (h ∘i homi (p₁ ∘ fₓ)) .has-tgt))
            refl refl (sym p₁∘universal))
        p₂∘universal
    outf .P₀-nat fₓ σ =
      sym (assoc _ _ _)
      ∙ ap (tgt ∘_) (sym (assoc _ _ _))
    outf .P₁-nat fₓ g σ =
      unique
        (pulll p₁∘universal
         ∙ ap ihom (∘i-nat g (homi (p₁ ∘ fₓ)) σ)
         ∙ ∘i-ihom
             (sym (assoc _ _ _) ∙ ap (src ∘_) (sym (assoc _ _ _)))
             (sym (assoc _ _ _) ∙ ap (tgt ∘_) (sym (assoc _ _ _)))
             refl refl (sym (assoc _ _ _)))
        (sym (!-unique _))
```
</details>

The contravariant internal hom functor is defined in an almost identical
manner; the only difference is that we pull back along $tgt$ instead of
$src$.

```agda
  Internal-hom-into : (x : Hom top C₀) → Outer-functor (ℂ ^opi)
  Internal-hom-into x = outf where
    open Pullback (pb tgt x) renaming (apex to Cₓ)
```

<details>
<summary>We omit the construction due to it's similarity with the
covariant internal hom functor.
</summary>

```agda
    outf : Outer-functor (ℂ ^opi)
    outf .∫P = Cₓ
    outf .P₀ fₓ = src ∘ p₁ ∘ fₓ
    outf .P₁ fₓ g = universal coh
      module hom-into-action where abstract
        coh : tgt ∘ (homi (p₁ ∘ fₓ) ∘i op-ihom g) .ihom ≡ x ∘ !
        coh =
          tgt ∘ (homi (p₁ ∘ fₓ) ∘i op-ihom g) .ihom ≡⟨ (homi (p₁ ∘ fₓ) ∘i op-ihom g) .has-tgt ⟩
          tgt ∘ p₁ ∘ fₓ ≡⟨ pulll square ⟩
          (x ∘ p₂) ∘ fₓ ≡⟨ pullr (sym (!-unique _)) ⟩
          x ∘ ! ∎
    outf .P₁-tgt fₓ {y} g = src-coh where abstract
      src-coh : y ≡ src ∘ p₁ ∘ universal (hom-into-action.coh fₓ g)
      src-coh =
        sym (ap (src ∘_) p₁∘universal
        ∙ (homi (p₁ ∘ fₓ) ∘i op-ihom g) .has-src)
    outf .P-id fₓ =
      sym $ unique (sym (ap ihom (idri _))) (sym (!-unique _))
    outf .P-∘ fₓ g h =
      unique
        (p₁∘universal
         ∙ ap ihom (associ _ _ _)
         ∙ ∘i-ihom refl
             (sym (ap (src ∘_) p₁∘universal ∙ (homi (p₁ ∘ fₓ) ∘i op-ihom h) .has-src))
             (sym (ap (tgt ∘_) p₁∘universal ∙ (homi (p₁ ∘ fₓ) ∘i op-ihom h) .has-tgt))
             (sym p₁∘universal) refl)
        p₂∘universal
    outf .P₀-nat fₓ σ =
      sym (assoc _ _ _)
      ∙ ap (src ∘_) (sym (assoc _ _ _))
    outf .P₁-nat fₓ g σ =
      unique
        (pulll p₁∘universal
        ∙ ap ihom (∘i-nat _ _ _)
        ∙ ∘i-ihom refl
             (sym (assoc _ _ _) ∙ ap (src ∘_) (sym (assoc _ _ _)))
             (sym (assoc _ _ _) ∙ ap (tgt ∘_) (sym (assoc _ _ _)))
             (sym (assoc _ _ _)) refl)
        (sym (!-unique _))
```
</details>

## Outer Natural Transformations

Let $\cC$ be a category, $\ica{C}$ an internal category in $\cC$, and $P, Q$ be
two outer functors on $\ica{C}$. An outer natural transformation $P \to Q$ is given
by maps between the total spaces of $P$ and $Q$, along with some naturality and
coherence conditions.

```agda
module _ {ℂ : Internal-cat} where
  open Internal-cat ℂ
  record _=>o_ (P Q : Outer-functor ℂ) : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      ηo : ∀ {Γ} → Hom Γ (P .∫P) → Hom Γ (Q .∫P)
```

The first condition ensures that the natural transformation is takes
elements of $P$ in the fibre over $x$ to elements of $Q$ over $x$.

```agda
      ηo-fib : ∀ {Γ} (px : Hom Γ (P .∫P)) → Q .P₀ (ηo px) ≡ P .P₀ px
```

With this little bit of coherence out of the way, we can state the
naturality condition; this is the familiar condition from natural
transformations, just mangled a bit.

```agda
      is-naturalo : ∀ {Γ : Ob} (px : Hom Γ (P .∫P)) (y : Hom Γ C₀)
        → (f : Homi (P .P₀ px) y)
        → ηo (P .P₁ px f) ≡ Q .P₁ (ηo px) (adjusti (sym (ηo-fib px)) refl f)
```

Finally, we require the naturality condition that allows us to work
in the internal language of $\cC$.

```agda
      ηo-nat : ∀ {Γ Δ} (px : Hom Δ (P .∫P)) (σ : Hom Γ Δ) → ηo px ∘ σ ≡ ηo (px ∘ σ)

  open _=>o_
```

<!--
```agda
  Outer-nat-path
    : ∀ {F G : Outer-functor ℂ} {α β : F =>o G}
    → (∀ {Γ} (px : Hom Γ (F .∫P)) → α .ηo px ≡ β .ηo px)
    → α ≡ β
  Outer-nat-path p i .ηo px = p px i
  Outer-nat-path {G = G} {α = α} {β = β} p i .ηo-fib px =
    is-prop→pathp (λ i → Hom-set _ _ (G .P₀ (p px i)) _)
      (α .ηo-fib px)
      (β .ηo-fib px) i
  Outer-nat-path {F = F} {G = G} {α = α} {β = β} p i .is-naturalo px y f j =
    is-set→squarep (λ i j → Hom-set _ _)
      (p (F .P₁ px f))
      (α .is-naturalo px y f)
      (β .is-naturalo px y f)
      (λ i → G .P₁ (p px i)
        (adjusti (sym (Outer-nat-path {α = α} {β = β} p i .ηo-fib px)) refl f))
      i j
  Outer-nat-path {α = α} {β = β} p i .ηo-nat px σ =
    is-prop→pathp (λ i → Hom-set _ _ (p px i ∘ σ) (p (px ∘ σ) i))
      (α .ηo-nat px σ)
      (β .ηo-nat px σ) i

  private unquoteDecl nat-eqv = declare-record-iso nat-eqv (quote _=>o_)

  Outer-nat-is-set
    : ∀ {F G : Outer-functor ℂ} → is-set (F =>o G)
  Outer-nat-is-set = Iso→is-hlevel 2 nat-eqv hlevel!

instance
  H-Level-Outer-nat
    : ∀ {ℂ : Internal-cat} {F G : Outer-functor ℂ} {n}
    → H-Level (F =>o G) (2 + n)
  H-Level-Outer-nat = basic-instance 2 Outer-nat-is-set
```
-->

## Some other outer functors

One important outer functor is the *constant outer functor* on an object
$X : \cC$; this is the internalized version of the [chaotic bifibration].

[chaotic bifibration]: Cat.Displayed.Instances.Chaotic.html

<!--
```agda
module _ (prods : has-products C) {ℂ : Internal-cat} where
  open Binary-products C prods
  open Internal-cat ℂ
  open _=>o_
```
-->

The total space of this functor is the product $X \times C_0$, and the
projection map is simply the second projection.

```agda
  ConstO : (X : Ob) → Outer-functor ℂ
  ConstO X .∫P = X ⊗₀ C₀
  ConstO X .P₀ f = π₂ ∘ f
```

Lifting is given by the universal map into the product.

```agda
  ConstO X .P₁ px {y} f = ⟨ π₁ ∘ px , y ⟩
  ConstO X .P₁-tgt px {y = y} f = sym $ π₂∘⟨⟩
```


<details>
<summary>Functoriality and naturality all follow from basic facts about products.
</summary>

```agda
  ConstO X .P-id px = products! C prods
  ConstO X .P-∘ px f g = products! C prods
  ConstO X .P₀-nat px σ = sym (assoc _ _ _)
  ConstO X .P₁-nat px f σ = products! C prods
```
</details>

Outer natural transformations between constant outer functors are easy
to characterize.

```agda
  const-nato : ∀ {X Y : Ob} → Hom X Y → ConstO X =>o ConstO Y
  const-nato f .ηo g = ⟨ f ∘ π₁ ∘ g , π₂ ∘ g ⟩
  const-nato f .ηo-fib px = products! C prods
  const-nato f .is-naturalo px y g = products! C prods
  const-nato f .ηo-nat px σ = products! C prods
```
