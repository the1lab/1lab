<!--
```agda
open import Cat.Diagram.Comonad
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning

open Total-hom
open Functor
open _=>_
open _⊣_
```
-->

```agda
module Cat.Instances.Coalgebras where
```

# Coalgebras over a comonad {defines="coalgebra category-of-coalgebras"}

A **coalgebra** for a [[comonad]] $W : \cC \to \cC$ is a pair of an object
$A : \cC$ and morphism $\alpha : A \to W(A)$ that satisfy the dual axioms
of a [[monad algebra]].

~~~{.quiver}
\begin{tikzcd}
  A && {W(A)} && A && {W(A)} \\
  \\
  && A && {W(A)} && {W(W(A))}
  \arrow["\alpha", from=1-1, to=1-3]
  \arrow["\id"', from=1-1, to=3-3]
  \arrow["\varepsilon", from=1-3, to=3-3]
  \arrow["\alpha", from=1-5, to=1-7]
  \arrow["\alpha"', from=1-5, to=3-5]
  \arrow["{W(\alpha)}", from=1-7, to=3-7]
  \arrow["\delta"', from=3-5, to=3-7]
\end{tikzcd}
~~~

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} {W : Functor C C} (cm : Comonad-on W) where
  open Cat.Reasoning C
  private module W = Comonad-on cm
  open W
```
-->

```agda
  record Coalgebra-on (A : Ob) : Type (o ⊔ ℓ) where
    no-eta-equality

    field
      ρ        : Hom A (W₀ A)
      ρ-counit : W.ε A ∘ ρ ≡ id
      ρ-comult : W₁ ρ ∘ ρ ≡ δ A ∘ ρ
```

This definition is rather abstract, but has a nice intuition in terms of
computational processes. First, recall that a [[monad]] $M$ can be
thought of as a categorical representation of an abstract syntax tree
for some algebraic theory, with the unit $\eta : A \to M(A)$ serving as
the inclusion of "variables" into syntax trees, and the join $\mu :
M(M(A)) \to M(A)$ encoding substitution. From this perspective, a monad
algebra $\alpha : M(A) \to A$ describes how to *evaluate* syntax trees
that contain variables of type $A$. In other words, a monad $M$
describes some class of inert computations that requires an environment
to be evaluated, and a monad algebra describes the objects of $\cC$ that
can function as environments[^1].

[^1]: This becomes even more clear when we consider [[relative extension algebras]].

Dually, a [[comonad]] $W$ can be interpreted as an inert environment
that is waiting for a computation to perform, with the counit $\eps :
W(A) \to A$ discarding the environment, and the comultiplication map
$\delta : W(A) \to W(W(A))$ reifying the environment as a value[^2].
Similarly, a comonad coalgebra $\rho : A \to W(A)$ describes the objects
of $\cC$ that can function as computations. More explicitly, the map
$\rho : A \to W(A)$ can be thought of as a way of taking an $A$ and
situating it in an environment $W(A)$; the counit compatibility $\eps
\circ \rho = \id$ ensures that the underlying $A$ does not change when
we include it in an environment, and the comultiplication condition
$W(\rho) \circ \rho = \delta \circ \rho$ ensures that the environments
reified by $\delta$ align with those produced by $\rho$.

[^2]: This analogy of comonads-as-contexts shows up quite often; see
[[comprehension comonad]] for an example.

<!--
```agda
  open Coalgebra-on
  module _ where
    open Displayed
```
-->

## The Eilenberg-Moore category of a comonad

If we view a comonad $W$ as a specification of an environment, and a
comonad coalgebra as a computational process that produces environments,
then a **homomorphism of $W$-coalgebras** $(A, \alpha) \to (B, \beta)$
ought to be a map $f : A \to B$ that allows us to "simulate" the
computation $\alpha$ via $\beta$. We can neatly formalize this intuition
by requiring that the following square commute:

~~~{.quiver}
\begin{tikzcd}
  A && B \\
  \\
  {W(A)} && {W(B)}
  \arrow["f", from=1-1, to=1-3]
  \arrow["\alpha"', from=1-1, to=3-1]
  \arrow["\beta", from=1-3, to=3-3]
  \arrow["{W(f)}"', from=3-1, to=3-3]
\end{tikzcd}
~~~

```agda
    is-coalgebra-hom : ∀ {x y} (h : Hom x y) → Coalgebra-on x → Coalgebra-on y → Type _
    is-coalgebra-hom f α β = W₁ f ∘ α .ρ ≡ β .ρ ∘ f
```

We can then assemble $W$-coalgebras and their homomorphisms into a
[[displayed category]] over $\cC$: the type of displayed objects over
some $A$ consists of all possible $W$-coalgebra structures on $A$, and
the type of morphisms over $\cC(A,B)$ are proofs that $f$ is a
$W$-coalgebra homomorphism.

```agda
    Coalgebras-over : Displayed C (o ⊔ ℓ) ℓ
    Coalgebras-over .Ob[_]            = Coalgebra-on
    Coalgebras-over .Hom[_]           = is-coalgebra-hom
    Coalgebras-over .Hom[_]-set f α β = hlevel 2

    Coalgebras-over .id'      = eliml W-id ∙ intror refl
    Coalgebras-over ._∘'_ p q = pushl (W-∘ _ _) ∙∙ ap (W₁ _ ∘_) q ∙∙ extendl p

    Coalgebras-over .idr' f'         = prop!
    Coalgebras-over .idl' f'         = prop!
    Coalgebras-over .assoc' f' g' h' = prop!
```

The [[total category]] of this displayed category is referred to as the
**Eilenberg-Moore** category of $W$.

```agda
  Coalgebras : Precategory (o ⊔ ℓ) ℓ
  Coalgebras = ∫ Coalgebras-over

  private
    module CoEM = Cat.Reasoning Coalgebras

  Coalgebra : Type _
  Coalgebra = CoEM.Ob

  Coalgebra-hom : (X Y : Coalgebra) → Type _
  Coalgebra-hom X Y = CoEM.Hom X Y
```

<!--
```agda
  module Coalgebras = Cat.Reasoning Coalgebras

module _ {o ℓ} {C : Precategory o ℓ} {F : Functor C C} {W : Comonad-on F} where instance
  Extensional-coalgebra-hom
    : ∀ {ℓr} {x y} ⦃ _ : Extensional (C .Precategory.Hom (x .fst) (y .fst)) ℓr ⦄
    → Extensional (Coalgebras.Hom W x y) ℓr
  Extensional-coalgebra-hom ⦃ e ⦄ = injection→extensional! (λ p → total-hom-path (Coalgebras-over W) p prop!) e

module _ {o ℓ} {C : Precategory o ℓ} {F : Functor C C} (W : Comonad-on F) where
  open Cat.Reasoning C
  private module W = Comonad-on W
  open Coalgebra-on
  open W
```
-->

## Cofree coalgebras {defines="cofree-coalgebra"}

Recall that for a [[monad]] $M : \cC \to \cC$, the forgetful functor
$\cC^{M} \to \cC$ from the [[Eilenberg-Moore category]] has a [[left
adjoint]] that sends an object $A : \cC$ to the [[free algebra]] $(M(A),
\mu)$. We can completely dualize this construction to comonads, which
gives us **cofree coalgebras**.

```agda
  Cofree-coalgebra : Ob → Coalgebras.Ob W
  Cofree-coalgebra A .fst = W₀ A
  Cofree-coalgebra A .snd .ρ = δ _
  Cofree-coalgebra A .snd .ρ-counit = δ-idr
  Cofree-coalgebra A .snd .ρ-comult = δ-assoc

  Cofree : Functor C (Coalgebras W)
  Cofree .F₀ = Cofree-coalgebra

  Cofree .F₁ h .hom       = W₁ h
  Cofree .F₁ h .preserves = sym (comult.is-natural _ _ h)

  Cofree .F-id    = ext W-id
  Cofree .F-∘ f g = ext (W-∘ _ _)
```

However, there is a slight twist: instead of obtaining a left adjoint to
the forgetful functor, we get a right adjoint!

```agda
  Forget⊣Cofree : πᶠ (Coalgebras-over W) ⊣ Cofree
  Forget⊣Cofree .unit .η (x , α) .hom       = α .ρ
  Forget⊣Cofree .unit .η (x , α) .preserves = α .ρ-comult
  Forget⊣Cofree .unit .is-natural x y f = ext (sym (f .preserves))

  Forget⊣Cofree .counit .η x              = W.ε x
  Forget⊣Cofree .counit .is-natural x y f = W.counit.is-natural _ _ _

  Forget⊣Cofree .zig {A , α} = α .ρ-counit
  Forget⊣Cofree .zag         = ext δ-idl
```

<!--
```agda
  to-cofree-hom
    : ∀ {X Y} → Hom (X .fst) Y → Coalgebras.Hom W X (Cofree-coalgebra Y)
  to-cofree-hom f = L-adjunct Forget⊣Cofree f
```
-->
