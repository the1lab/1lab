```agda
open import Cat.Diagram.Monad
open import Cat.Functor.Base
open import Cat.Univalent
open import Cat.Prelude

module
  Cat.Univalent.Instances.Algebra
    {o ℓ} {C : Precategory o ℓ}
    (isc : is-category C)
    (M : Monad C)
  where
```

# Eilenberg-Moore Categories

Given a base [univalent category] $\ca{C}$, we can consider a [monad]
$M$ on $\ca{C}$, and its associated [Eilenberg-Moore category]
$\ca{C}^M$, as a standard way of constructing categories of "algebraic
gadgets" backed by objects of $\ca{C}$. A concrete example is given by
the [category of monoids]: A [monoid] (in [sets]) is equivalent to an
algebra for the [list monad].

[univalent category]: Cat.Univalent.html
[monad]: Cat.Diagram.Monad.html
[Eilenberg-Moore category]: Cat.Diagram.Monad.html#eilenberg-moore-category
[category of monoids]: Algebra.Monoid.Category.html
[monoid]: Algebra.Monoid.html
[sets]: Category.Instances.Sets.html
[list monad]: Algebra.Monoid.Category.html#free-objects

Given that "hand-rolled" categories of this sort tend to be
well-behaved, in particular when it comes to identifications (see
[univalence of monoids], [univalence of groups], [univalence of
semilattices]), it's natural to ask whether _all_ Eilenberg-Moore
categories are themselves univalent, assuming that their underlying
category is. Here we give a positive answer.

[univalence of monoids]: Algebra.Monoid.html#Monoid-univalent
[univalence of groups]: Algebra.Group.html#Group-univalent
[univalence of semilattices]: Algebra.Semilattice.html#Semilattice-univalent

Fixing a monad $M$ on a univalent category $\ca{C}$, we abbreviate its
Eilenberg-Moore category $\ca{C}^M$ as `EM`{.Agda}.

```agda
private EM = Eilenberg-Moore C M

import Cat.Reasoning EM as EM
import Cat.Reasoning C as C
```

As usual, we take the centre of contraction to be $A$ and the `identity
isomorphism`{.Agda ident=EM.id-iso} $A \cong A$; The hard part is
proving that, given a pair of $M$-algebras $A$ and $X$, together with a
specified [isomorphism] $f : A \cong X$, we can build an identification
$A \cong X$, such that [over] this identification, $f$ is the identity
map.

[isomorphism]: Cat.Morphism.html#isos
[over]: 1Lab.Path.html#dependent-paths

```agda
Eilenberg-Moore-is-category : is-category EM
Eilenberg-Moore-is-category A .centre = A , EM.id-iso
Eilenberg-Moore-is-category (A , Am) .paths ((X , Xm) , A≅X) =
  Σ-pathp A≡M triv where
```

The first thing we shall note is that an algebra is given by a pair of
two data: An underlying object $A_0$ (resp $X_0$), together with the
structure $A_m$ (resp. $X_m$) of an `M-algebra on`{.Agda
ident=Algebra-on} $A_0$. Hence, an identification of algebras can be
broken down into an identification of their components, re-using the
equality lemma `for dependent pairs`{.Agda ident=Σ-pathp}.

<!--
```agda
    module A = Algebra-on Am
    module X = Algebra-on Xm
    module A≅X = EM._≅_ A≅X
    open Algebra-hom renaming (morphism to map ; commutes to sq)
    open Algebra-on
```
-->

Recall that a `homomorphism of M-algebras`{.Agda ident=Algebra-hom}
between $(A_0,A_m) \to (X_0,X_m)$ is given by a map $h : A_0 \to X_0$ in
$\ca{C}$, such that the diagram below commutes. By forgetting that the
square commutes, algebra homomorphisms correspond [faithfully] to
morphisms in the underlying category $\ca{C}$.

[faithfully]: agda://Cat.Diagram.Monad#Forget

~~~{.quiver}
\[\begin{tikzcd}
  {M(A_0)} && {M(X_0)} \\
  \\
  {A_0} && {X_0}
  \arrow["{M_1(h)}", from=1-1, to=1-3]
  \arrow["{A_m}"', from=1-1, to=3-1]
  \arrow["{X_m}", from=1-3, to=3-3]
  \arrow["h"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

Hence, given an _isomorphism_ $(A_0, A_m) \cong (X_0, X_m)$ (let us call
it $f$) in $\ca{C}^M$, we can forget all of the commutativity data
associated with the algebra homomorphisms, and recover an isomorphism
between the underlying objects in $\ca{C}$:

```agda
    A₀≅X₀ : A C.≅ X
    A₀≅X₀ = C.make-iso
      (map A≅X.to) (map A≅X.from) (ap map A≅X.invl) (ap map A≅X.invr)
```

Since we assumed $\ca{C}$ to be univalent, this isomorphism can be `made
into a path`{.Agda ident=iso→path} $A_0 \equiv X_0$. This covers a third
of the task: We must now show first that the algebra structures $A_m$
and $X_m$ are identified over `A₀≡X₀`{.Agda}, and we must prove that the
resulting identification makes $f$ into the identity isomorphism.

```agda
    A₀≡X₀ : A ≡ X
    A₀≡X₀ = iso→path C isc A₀≅X₀
```

By the characterisation of `paths in algebras`{.Agda
ident=Algebra-on-pathp}, it suffices to show that `A₀≡X₀`{.Agda}
transports $A_m$'s multiplication to that of $X_m$'s; Using the
corresponding lemma for `paths in hom-spaces`{.Agda ident=Hom-pathp-iso}
of univalent categories, we can get away with (still calling our
isomorphism $f$) showing the square below commutes.

~~~{.quiver}
\[\begin{tikzcd}
  {M(X_0)} && {M(A_0)} \\
  \\
  {X_0} && {A_0}
  \arrow["{X_m}"', from=1-1, to=3-1]
  \arrow["{M_1(f^{-1})}", from=1-1, to=1-3]
  \arrow["{A_m}", from=1-3, to=3-3]
  \arrow["f", from=3-3, to=3-1]
\end{tikzcd}\]
~~~

Since we have assumed that $f$ is an $M$-algebra isomorphism, we can
simultaneously turn the square above into one which has $f$ and $f^{-1}$
in adjacent faces and swap $A_m$ for $X_m$; A straightforward
calculation then shows that the square above commutes.

```agda
    Am≡Xm : PathP (λ i → Algebra-on C M (A₀≡X₀ i)) Am Xm
    Am≡Xm = Algebra-on-pathp _ A₀≡X₀ same-mults′ where
      same-mults
        : PathP
          (λ i → C.Hom (iso→path C isc (F-map-iso (Monad.M M) A₀≅X₀) i) (A₀≡X₀ i))
          (Am .ν) (Xm .ν)
      same-mults =
        Hom-pathp-iso C isc (
          map A≅X.to C.∘ Am .ν C.∘ Monad.M₁ M (map A≅X.from)                 ≡⟨ C.pulll (sq A≅X.to) ⟩
          (Xm .ν C.∘ Monad.M₁ M (A≅X.to .map)) C.∘ Monad.M₁ M (map A≅X.from) ≡⟨ C.cancelr (sym (Monad.M-∘ M _ _) ·· ap (Monad.M₁ M) (ap map A≅X.invl) ·· Monad.M-id M) ⟩
          Xm .ν                                                              ∎
        )
```

Note, however, that the path above is not in the correct space! While it
is in a space of $\ca{C}$-morphisms, the source is not of the correct
type. This is because functors between univalent categories can act on
paths in "two" ways: One can either apply the functor's `action on
isos`{.Agda ident=F-map-iso}, then take a path in the codomain category;
Or take a path in the domain category, and then use the canonical
`action on paths`{.Agda ident=ap}. Fortunately these `coincide`{.Agda
ident=F-map-path}, and we can correct the source:

```agda
      same-mults′ : PathP (λ i → C.Hom (Monad.M₀ M (A₀≡X₀ i)) (A₀≡X₀ i))
                      (Am .ν) (Xm .ν)
      same-mults′ =
        transport
          (λ j → PathP
            (λ i → C.Hom (F-map-path (Monad.M M) A₀≅X₀ isc isc (~ j) i) (A₀≡X₀ i))
            (Am .ν) (Xm .ν))
          same-mults

    A≡M : Path (Algebra _ M) (A , Am) (X , Xm)
    A≡M i = A₀≡X₀ i , Am≡Xm i
```

To finish the proof that $\ca{C}^M$ is univalent, we must show that the
identification we've built trivialises the isomorphism $A \cong X$ we
were given. This follows immediately from the characterisation of `paths
in isomorphism spaces`{.Agda ident=≅-pathp} and `in Hom-spaces`{.Agda
ident=Hom-pathp}.

```agda
    triv : PathP (λ i → (A , Am) EM.≅ A≡M i) EM.id-iso A≅X
    triv = EM.≅-pathp refl _
      (Algebra-hom-pathp _ _ _ (Hom-pathp-reflr-iso C isc (C.idr _)))
```
