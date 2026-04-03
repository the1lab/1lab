---
description: |

---

<!--
```agda
open import Cat.Displayed.Instances.Lifting
open import Cat.Displayed.Isofibration
open import Cat.Functor.Naturality
open import Cat.Functor.Properties
open import Cat.Displayed.Functor
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Displayed.Morphism
import Cat.Functor.Reasoning
import Cat.Reasoning
import Cat.Morphism

open Cat.Displayed.Morphism using (module _≅[_]_)
open Cat.Morphism._≅_
open _≅[_]_
open ∫Hom
```
-->

```agda
module Cat.Displayed.Isofibration.Free where
```

# Displayed categories from functors

::: source
The construction presented in this page is adapted from [*Foundations of
Relative Category Theory*][frct].

[frct]: https://www.jonmsterling.com/frct-000B/
:::

<!--
```agda
module _
  {ob ℓb oe ℓe}
  {B : Precategory ob ℓb}
  {E : Precategory oe ℓe}
  (P : Functor E B)
  where
  private
    module P = Cat.Functor.Reasoning P
    module E = Precategory E
    open Cat.Reasoning B

  open Displayed
  open Functor
```
-->

This page addresses the problem of comparing notions in the theory of
[[displayed categories]], as we have formalised it, with those in the
traditional study of *relative* category theory, which are stated in
terms of a *projection* functor $P : \cE \to \cB$. Essentially, we want
to replace $\cE$ with the [[total category]] of some displayed category
$P_\bull \liesover \cB$, so as to recover $P$ (up to equivalence) as the
projection functor $\pi^f : \int P_\bull \to \cB$.

Fixing a functor $P : \cE \to \cB$, we define the type of objects over
$x : \cB$ to consist of pairs $(x', p)$ where $x' : \cE$ and $p : P(x')
\cong x$ --- in other words, the objects over $x$ are not the
type-theoretic [[*fibre*]] of $P$ over $x$, but instead the
category-theoretic [[*essential* fibre]] of $P$ over $x$.

```agda
  Free-isofibration : Displayed B (ℓb ⊔ oe) (ℓb ⊔ ℓe)
  Free-isofibration .Ob[_] x = Essential-fibre P x
```

To understand the types of maps in $P_\bull$, we will diagramatically
denote a pair $(x', p) \liesover x$ as a "leg"

~~~{.quiver .attach-above}
\[\begin{tikzcd}
  x' \\
  {P(x')} & {x\text{.}}
  \arrow[lies over, from=1-1, to=2-1]
  \arrow["\phi"', from=2-1, to=2-2]
\end{tikzcd}\]
~~~

A morphism $g : (x', p) \to_f (y', q)$ lying over $f : x \to y$ is a map
$\cE(x', y')$, which, "over" the Isomorphisms $p$ and $q$, gets sent by
$P$ to $f$. Pictorially, we understand the type of $g$ as that of dashed
arrows in the diagram below, where the "leg" $(x', p)$ on the left
(resp. $(y', q)$ on the right) is drawn with $p$ towards the screen.

```agda
  Free-isofibration .Hom[_] f (u , φ) (v , ψ) =
    Σ[ g ∈ E.Hom u v ] ψ .to ∘ P.₁ g ≡ f ∘ φ .to
```

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  \& {x'} \&\& {y'} \& \\
  \& {P(x')} \&\& {P(y')} \\
  x \&\&\&\& y
  \arrow[dashed, "g", from=1-2, to=1-4]
  \arrow[lies over, from=1-2, to=2-2]
  \arrow[lies over, from=1-4, to=2-4]
  \arrow["{P(g)}"', from=2-2, to=2-4]
  \arrow["p"', from=2-2, to=3-1]
  \arrow["q", from=2-4, to=3-5]
  \arrow["f"', from=3-1, to=3-5]
\end{tikzcd}\]
~~~

<details>
<summary>
The operations (identities and composition) necessary to make $P_\bull$
a displayed category are inherited from those in $\cE$. with
commutativity of the diagrams defining them assured by functoriality of
$P$.

The displayed category laws are directly inherited from $\cE$.
</summary>

```agda
  Free-isofibration .Hom[_]-set f a b = hlevel 2

  Free-isofibration .id' = record where
    fst = E.id
    snd = P.elimr refl ∙ introl refl

  Free-isofibration ._∘'_ (f , φ) (g , ψ) = record where
    fst = f E.∘ g
    snd = P.popl φ ∙ extendr ψ

  Free-isofibration .hom[_] p (f , α) = record
    { fst = f
    ; snd = α ∙ car p
    }
  Free-isofibration .coh[_] _ _   = Σ-prop-pathp! refl
  Free-isofibration .idr'   _     = Σ-prop-pathp! (E.idr _)
  Free-isofibration .idl'   _     = Σ-prop-pathp! (E.idl _)
  Free-isofibration .assoc' _ _ _ = Σ-prop-pathp! (E.assoc _ _ _)
```

</details>

<!--
```agda
module _
  {ob ℓb oe ℓe}
  {B : Precategory ob ℓb}
  {E : Precategory oe ℓe}
  (P : Functor E B)
  where
  private
    P∙ = Free-isofibration P

    module Iso[P] = Cat.Displayed.Morphism P∙
    module P = Cat.Functor.Reasoning P
    module B = Cat.Reasoning B
    module E = Cat.Reasoning E


  open Displayed-functor
  open Isofibration
  open Functor
  open Lifting
```
-->

## As an isofibration

The construction of a displayed category from a functor results in an
[[isofibration]], and indeed this is the isofibration over $\cB$
[[freely generated|free object]] by $P$, in a suitable bicategorical
sense.

<details>
<summary>

To show this, we will first need a technical lemma stating that an
isomorphism $\theta : x \cong y$ in $\cE$ whose forward direction
extends to a morphism $(x, \phi) \to_u (y, \psi)$ over the forward
direction of an isomorphism $u : a \cong b$ extends to a complete
isomorphism $(x, \phi) \cong_u (y, \psi)$ in $P_\bull$.

```agda
  Free-isofibration-iso
    : ∀ {a b x y}
    → {u : a B.≅ b} {φ : P.₀ x B.≅ a} {ψ : P.₀ y B.≅ b} (θ : x E.≅ y)
    → ψ .to B.∘ P.₁ (θ .to) ≡ u .to B.∘ φ .to
    → (x , φ) Iso[P].≅[ u ] (y , ψ)
```

The details of the proof are not particularly interesting.

</summary>

```agda
  Free-isofibration-iso {u = u} {φ} {ψ} θ p =
    Iso[P].make-iso[ u ]
      (θ .to   , p)
      (θ .from , q)
      (Σ-prop-pathp! (θ .invl))
      (Σ-prop-pathp! (θ .invr))
    where abstract
      q : φ .to B.∘ P.₁ (θ .from) ≡ u .from B.∘ ψ .to
      q = flip Equiv.from refl $
        φ .to B.∘ P.₁ (θ .from) ≡ u .from B.∘ ψ .to     ≃⟨ B.post-invl (B.iso→invertible u) ⟩
        u .to B.∘ φ .to B.∘ P.₁ (θ .from) ≡ ψ .to       ≃⟨ ∙-pre-equiv (B.extendl p) ⟩
        ψ .to B.∘ P.₁ (θ .to) B.∘ P.₁ (θ .from) ≡ ψ .to ≃⟨ ∙-pre-equiv (B.intror (P.annihilate (θ .invl))) ⟩
        ψ .to ≡ ψ .to                                   ≃∎
```

</details>

With this in hand, showing that $P_\bull$ is an isofibration is
extremely straightforward. Supposing we have an iso $\psi : a \cong b$,
and drawing the object $(x, \phi) \liesover a$ we want to lift as a
"leg", we note that the lifting problem we have to solve involves a
sequence of maps

~~~{.quiver .attach-around}
\[\begin{tikzcd}[ampersand replacement=\&]
  {x} \&\&\&\& \\
  \\
  {P(x)} \&\& a \&\& b
  \arrow[lies over, from=1-1, to=3-1]
  \arrow["{\phi}", from=3-1, to=3-3]
  \arrow["{\psi}", from=3-3, to=3-5]
\end{tikzcd}\]
~~~

whence it is immediate that the lifting we desire is $(x, \psi \circ \phi)$.

```agda
  Free-isofibration-is-isofibration : Isofibration P∙
  Free-isofibration-is-isofibration = record where
    _^*_ ψ (x , φ) = x , ψ B.∘Iso φ
    ^*-lifts ψ (x , φ) = Free-isofibration-iso
      E.id-iso
      (P.elimr refl)
```

## The total category

There is an evident [[lifting]] of $P_\bull$ against $P$, which sends an
object $x : \cB$ to the pair $(x, \id) : \P_x$.

```agda
  Free-isofibration-lifting : Lifting P∙ P
  Free-isofibration-lifting .F₀'  x   = x , B.id-iso
  Free-isofibration-lifting .F₁'  f   = f , B.id-comm-sym
  Free-isofibration-lifting .F-id'    = Σ-prop-pathp! refl
  Free-isofibration-lifting .F-∘' f g = Σ-prop-pathp! refl
```

<details>
<summary>
Taken as a functor `E→∫`{.Agda} from $\cE \to \int P_\bull$, this
lifting extends to an [[equivalence of categories]].

```agda
  private
    E→∫ : Functor E (∫ P∙)
    E→∫ = Lifting→Functor _ Free-isofibration-lifting

  Free-isofibration-lifting-split-eso : is-split-eso E→∫
  Free-isofibration-lifting-is-ff     : is-fully-faithful E→∫
```

The proofs are, again, straightforward functoriality reasoning.
</summary>

```agda
  Free-isofibration-lifting-split-eso (b , x , φ) = record where
    fst = x
    snd = total-iso-from-isos _ φ $ Free-isofibration-iso E.id-iso $ B.cdr P.F-id

  Free-isofibration-lifting-is-ff = is-iso→is-equiv λ where
    .is-iso.from h → h .snd .fst
    .is-iso.rinv h → ∫Hom-path _
      (B.introl refl ∙∙ h .snd .snd ∙∙ B.elimr refl)
      (Σ-prop-pathp! refl)
    .is-iso.linv h → refl
```

</details>

Finally, as desired, precomposition with this equivalence takes the
projection functor $\pi^f$ to $P$.[^recover]

```agda
  Free-isofibration-recovers : πᶠ P∙ F∘ E→∫ ≅ⁿ P
  Free-isofibration-recovers = to-natural-iso record where
    eta x = B.id
    inv x = B.id
    eta∘inv x = B.idl _
    inv∘eta x = B.idl _
    natural x y f = B.id-comm
```

[^recover]:
    In fact, we recover $P$ *up to identity of functors*, definitionally
    in the relevant components.

    ```agda
  _ : πᶠ P∙ F∘ E→∫ ≡ P
    ```

    This is both inconvenient to work with and needlessly strict.

<!--
```agda
  _ = Functor-path (λ _ → refl) (λ _ → refl)
```
-->

## Freeness as an isofibration

To show that $P_\bull$ is freely generated as an isofibration over $\cB$
by $P$, we show that any [[lifting]] of some other isofibration $\cH
\liesover \cB$ against $P$ can be re-expressed as a [[vertical functor]]
$P_\bull \to H$.

```agda
  Free-isofibration-factor
    : ∀ {oh ℓh} {H : Displayed B oh ℓh}
    → Isofibration H → Lifting H P
    → Vertical-functor P∙ H
  Free-isofibration-factor {H = H} H-isofib F = F† where
```

<!--
```agda
    open Cat.Displayed.Reasoning H
    module H = Isofibration H-isofib
    module F = Lifting F renaming (F₀' to ₀' ; F₁' to ₁')
```
-->

The gist of the construction is presented below. Starting with an object
$(x, \phi) : P_a$, we obtain an $F(x) : \cH_x$, which we can transport
to our desired $\phi^*F(x) : \cH_{a}$ since $\cH$ is an isofibration.

```agda
    F† : Vertical-functor P∙ H
    F† .F₀' (x , φ) = φ H.^* F.₀' x
    F† .F₁' {a' = x , φ} {b' = y , ψ} (h , p) =
      hom[ B.pulll p ∙ B.cancelr (φ .invl) ] (H.π* ∘' F.₁' h ∘' H.ι!)
```

<details>
<summary>Verifying that this assignment is functorial boils down to a
straightforward calculation, using functoriality of the lifting
$F$.</summary>

```agda
    F† .F-id' {x' = x , φ} = begin[]
      hom[] (H.π* ∘' F.₁' E.id ∘' H.ι!) ≡[]⟨ unwrap _ ⟩
      H.π* ∘' F.₁' E.id ∘' H.ι!         ≡[]⟨ refl⟩∘'⟨ eliml[] _ F.F-id' ⟩
      H.π* ∘' H.ι!                      ≡[]⟨ H.^*-lifts _ _ .invl' ⟩
      id'                               ∎[]

    F† .F-∘' {a' = x , φ} {b' = y , ψ} {c' = z , θ} {f' = f , p} {g' = g , q} =
      let
        open _≅[_]_ (H.^*-lifts φ (F.₀' x)) renaming (from' to φ^*→; to' to φ^*←)
        open _≅[_]_ (H.^*-lifts ψ (F.₀' y)) renaming (from' to ψ^*→; to' to ψ^*←)
        open _≅[_]_ (H.^*-lifts θ (F.₀' z)) renaming (from' to θ^*→; to' to θ^*←)
      in begin[]
        hom[] (θ^*← ∘' F.₁' (f E.∘ g) ∘' φ^*→)                           ≡[]⟨ unwrap _ ⟩
        θ^*← ∘' F.₁' (f E.∘ g) ∘' φ^*→                                   ≡[]⟨ refl⟩∘'⟨ (pushl[] _ (F.F-∘' f g)) ⟩
        θ^*← ∘' F.₁' f ∘' F.₁' g ∘' H.ι!                                 ≡[]⟨ refl⟩∘'⟨ refl⟩∘'⟨ (introl[] _ (H.^*-lifts _ _ .invr')) ⟩
        θ^*← ∘' F.₁' f ∘' (ψ^*→ ∘' ψ^*←) ∘' F.₁' g ∘' H.ι!               ≡[]⟨ refl⟩∘'⟨ refl⟩∘'⟨ pullr[] _ (wrap _) ⟩
        θ^*← ∘' F.₁' f ∘' ψ^*→ ∘' hom[] (ψ^*← ∘' F.₁' g ∘' φ^*→)         ≡[]⟨ pushr[] _ (assoc' _ _ _) ∙[] wrapl _ ⟩
        hom[] (θ^*← ∘' F.₁' f ∘' ψ^*→) ∘' hom[] (ψ^*← ∘' F.₁' g ∘' φ^*→) ∎[]
```

</details>
