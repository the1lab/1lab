<!--
```agda
open import Cat.Displayed.Cocartesian
open import Cat.Diagram.Limit.Finite
open import Cat.Displayed.Cartesian
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Prelude

open import Order.Base
open import Order.Cat

import Cat.Displayed.Reasoning as Disp
import Cat.Reasoning as Cat

import Order.Reasoning
```
-->

```agda
module Cat.Displayed.Doctrine {o ℓ} (B : Precategory o ℓ) where
```

<!--
```agda
open Cat B
```
-->

# Regular hyperdoctrines {defines="regular-hyperdoctrine"}

A **regular hyperdoctrine** is a generalisation of the defining features
of the [[poset of subobjects]] of a [[regular category]]; More
abstractly, it axiomatises exactly what is necessary to interpret
first-order (regular) logic _over_ a [[finitely complete category]].
There is quite a lot of data involved, so we'll present it in stages.

::: warning
While the _raison d'être_ of regular hyperdoctrines is the
interpretation of regular logic, that is far too much stuff for Agda to
handle if it were placed in this module. **The interpretation of logic
lives at [[logic in a hyperdoctrine]]**.
:::

```agda
record Regular-hyperdoctrine o' ℓ' : Type (o ⊔ ℓ ⊔ lsuc (o' ⊔ ℓ')) where
```

To start with, fix a category $\cB$, which we think of as the _category
of contexts_ of our logic --- though keep in mind the definition works
over a completely arbitrary category. The heart of a regular
hyperdoctrine is a [[displayed category]] $\bP \liesover \cB$, which, a
priori, assigns to every object $\Gamma : \cB$ a category $\bP(\Gamma)$
of **predicates** over it, where the set $\hom(\phi, \psi)$ for $\phi,
\psi : \bP(\Gamma)$ interprets the **entailment** relation between
predicates; we therefore write $\phi \vdash_\Gamma \psi$.

```agda
  field
    ℙ : Displayed B o' ℓ'

  module ℙ = Displayed ℙ
```

However, having an entire _category_ of predicates is hard to make
well-behaved: that would lend itself more to an interpretation of
dependent type theory, rather than the first-order logic we are
concerned with. Therefore, we impose the following two restrictions on
$\bP$:

```agda
  field
    has-is-thin    : ∀ {x y} {f : Hom x y} x' y' → is-prop (ℙ.Hom[ f ] x' y')
    has-univalence : ∀ x → is-category (Fibre ℙ x)
```

First, the entailment relation $\phi \vdash_\Gamma \psi$ must be a
[[proposition]], rather than an arbitrary set --- which we will use as
justification to omit the names of its inhabitants. Second, each
[[fibre category]] $\bP(\Gamma)$ must be [[univalent|univalent
category]]. In light of the previous restriction, this means that each
fibre satisfies _antisymmetry_, or, specialising to logic, that
inter-derivable propositions are indistinguishable. To put it more
concisely, this means that every fibre $\bP(\Gamma)$ is a [[poset]]:

```agda
  ≤-Poset : ∀ {x : Ob} → Poset o' ℓ'
  ≤-Poset {x = x} = thin→poset (Fibre ℙ x) has-is-thin (has-univalence x)
```

Next, each fibre $\bP(\Gamma)$ must be [[finitely complete]]. The binary
products interpret conjunction, and the terminal object interprets the
true proposition; since we are working with posets, these two shapes of
limit suffice to have full finite completeness.

```agda
  field
    fibrewise-meet : ∀ {x} x' y' → Product (Fibre ℙ x) x' y'
    fibrewise-top  : ∀ x → Terminal (Fibre ℙ x)
```

Everything we have so far is fine, but it only allows us to talk about
predicates over a _specific_ context, and we do not yet have an
interpretation of _substitution_ that would allow us to move between
fibres. This condition is fortunately very easy to state: it suffices to
ask that $\bP$ be a [[Cartesian fibration]].

```agda
    cartesian : Cartesian-fibration ℙ
```

We're almost done with the structure. To handle existential
quantification, the remaining connective of regular logic, we use the
key insight of Lawvere: the existential elimination and introduction
rules

<div class=mathpar>

$$
\frac{\phi \vdash_{x} \psi}{\exists_x \phi \vdash \psi}
$$

$$
\frac{\exists_x \phi \vdash \psi}{\phi \vdash_{x} \psi}
$$

</div>

say precisely that existential quantification along $x$ is [[left
adjoint]] to weakening by $x$! Since weakening will be interpreted by
[[cartesian lifts]], we will interpret the existential quantification by
a left adjoint to that: in other words, $\bP$ must also be a
[[cocartesian fibration]] over $\bP$.

```agda
    cocartesian : Cocartesian-fibration ℙ
```

Note that we have assumed the existence of left adjoints to arbitrary
substitutions, which correspond to forms of existential quantification
more general than quantification over the latest variable. For example,
if the base category $\cB$ has finite products, then existential
quantification of a predicate $\phi : \bP(A)$ over $\delta : A \to A
\times A$ corresponds to the predicate "$(i, j) \mapsto (i = j) \land
\phi(i)$".

<details>
<summary>That concludes the _data_ of a regular hyperdoctrine. We will
soon write down the axioms it must satisfy: but before that, we need a
digression to introduce better notation for working with the
deeply-nested data we have introduced.
</summary>

```agda
  module fibrewise-meet {x} (x' y' : ℙ.Ob[ x ]) = Product (fibrewise-meet x' y')

  open Cartesian-fibration ℙ cartesian hiding (rebase) public
  open Cocartesian-fibration ℙ cocartesian public

  _[_] : ∀ {x y} → ℙ.Ob[ x ] → Hom y x → ℙ.Ob[ y ]
  _[_] x f = f ^* x

  module fibrewise-top x = Terminal (fibrewise-top x)

  exists : ∀ {x y} (f : Hom x y) → ℙ.Ob[ x ] → ℙ.Ob[ y ]
  exists f x = f ^! x

  _&_ : ∀ {x} (p q : ℙ.Ob[ x ]) → ℙ.Ob[ x ]
  _&_ = fibrewise-meet.apex

  aye : ∀ {x} → ℙ.Ob[ x ]
  aye = fibrewise-top.top _

  infix 30 _[_]
  infix 25 _&_
```

</details>

The first two axioms concern the commutativity of substitution and the
conjunctive connectives:

```agda
  field
    subst-&
      : ∀ {x y} (f : Hom y x) (x' y' : ℙ.Ob[ x ])
      → (x' & y') [ f ] ≡ x' [ f ] & y' [ f ]

    subst-aye
      : ∀ {x y} (f : Hom y x)
      → aye [ f ] ≡ aye
```

Next, we have a _structural rule_, called **Frobenius reciprocity**,
governing the interaction of existential quantification and conjunction.
If substitution were invisible, it would say that $(\exists \phi) \land
\psi$ is $\exists (\phi \land \psi)$; Unfortunately, proof assistants
force us to instead say that if we have $\phi : \bP(\Gamma)$, $\psi :
\bP(\Delta)$, and $\rho : \Gamma \to \Delta$, then $\exists_\rho(\phi)
\land \psi$ is $\exists_\rho(\phi \land \psi[\rho])$.

```agda
  field
    frobenius
      : ∀ {x y} (f : Hom x y) {α : ℙ.Ob[ x ]} {β : ℙ.Ob[ y ]}
      → exists f α & β ≡ exists f (α & β [ f ])
```

Finally, we have a general rule for the commutativity of existential
quantification and substitution. While in general the order matters, the
**Beck-Chevalley condition** says that we can conclude

$$
\exists_h (a[k]) = (\exists_g a)[f]
$$

provided that the square

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  d \&\& a \\
  \\
  b \&\& c
  \arrow["k"', from=1-1, to=3-1]
  \arrow["h", from=1-1, to=1-3]
  \arrow["f", from=1-3, to=3-3]
  \arrow["g"', from=3-1, to=3-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

is a pullback.

```agda
    beck-chevalley
      : ∀ {a b c d} {f : Hom a c} {g : Hom b c} {h : Hom d a} {k : Hom d b}
      → is-pullback B h f k g
      → ∀ {α} → exists h (α [ k ]) ≡ (exists g α) [ f ]
```

That concludes the definition of regular hyperdoctrine. Said snappily, a
**regular hyperdoctrine** $\bP \liesover \cB$ is a [[bifibration]] into
[[(meet-)semilattices|meet-semilattice]] satisfying Frobenius reciprocity and
the Beck-Chevalley condition.

<!--
```agda
  abstract
    has-is-set : ∀ Γ → is-set ℙ.Ob[ Γ ]
    has-is-set Γ = Poset.Ob-is-set ≤-Poset

  module _ {x} where
    open Order.Reasoning (≤-Poset {x}) hiding (Ob-is-set ; Ob) public
  open Disp ℙ public
  subst-∘ : ∀ {x y z} (f : Hom y z) (g : Hom x y) {α} → (α [ f ]) [ g ] ≡ α [ f ∘ g ]
  subst-∘ f g = ≤-antisym
    (π*.universalv
      (π* _ _ ℙ.∘' π* _ _))
    (π*.universalv
      (π*.universal g (π* _ _)))

  subst-id : ∀ {x} (α : ℙ.Ob[ x ]) → α [ id ] ≡ α
  subst-id α = ≤-antisym
    (π* id α)
    (π*.universal _ (ℙ.id' ℙ.∘' ℙ.id'))

  subst-≤ : ∀ {x y} (f : Hom x y) {α β : ℙ.Ob[ y ]} → α ≤ β → α [ f ] ≤ β [ f ]
  subst-≤ f p = π*.universalv $
    hom[ idl _ ] (p ℙ.∘' π* f _)

  exists-id : ∀ {x} (α : ℙ.Ob[ x ]) → exists id α ≡ α
  exists-id α = ≤-antisym
    (ι!.universal _ (ℙ.id' ℙ.∘' ℙ.id'))
    (ι! id α)

  &-univ : ∀ {x} {α β γ : ℙ.Ob[ x ]} → α ≤ β → α ≤ γ → α ≤ (β & γ)
  &-univ p q = fibrewise-meet.⟨_,_⟩ _ _ p q

  &-comm : ∀ {x} {α β : ℙ.Ob[ x ]} → α & β ≡ β & α
  &-comm = ≤-antisym
    (&-univ (fibrewise-meet.π₂ _ _) (fibrewise-meet.π₁ _ _))
    (&-univ (fibrewise-meet.π₂ _ _) (fibrewise-meet.π₁ _ _))

  ≤-exists : ∀ {x y} (f : Hom x y) {α β} → α ≤ β [ f ] → exists f α ≤ β
  ≤-exists f p = ι!.universalv $
    hom[ idr f ] (π* f _ ℙ.∘' p)

  subst-! : ∀ {x y} (f : Hom y x) {α} → ℙ.Hom[ id ] α (aye [ f ])
  subst-! f {α} = subst (λ e → ℙ.Hom[ id ] α e) (sym (subst-aye f))
    (Terminal.! (fibrewise-top _))
```
-->
