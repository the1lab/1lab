<!--
```agda
open import Cat.Functor.Adjoint.Compose
open import Cat.Instances.Slice.Twice
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Exponential
open import Cat.Instances.Functor
open import Cat.Diagram.Pullback
open import Cat.Functor.Pullback
open import Cat.Diagram.Product
open import Cat.Functor.Adjoint
open import Cat.Instances.Slice
open import Cat.Prelude

import Cat.Functor.Bifunctor as Bifunctor
import Cat.Reasoning
```
-->

```agda
module Cat.CartesianClosed.Locally where
```

<!--
```agda
open make-natural-iso
open Functor
open /-Obj
open /-Hom
```
-->

# Locally cartesian closed categories {defines="locally-cartesian-closed locally-cartesian-closed-category"}

A [[finitely complete category]] $\cC$ is said to be **locally Cartesian
closed** when each of its [[slice categories]] is [[Cartesian closed]].
Note that requiring finite limits in $\cC$ does exclude some examples,
since $\cC$ might have each of its slices Cartesian closed, but lack a
terminal object.[^lh] With the extra condition, a locally Cartesian closed
category is Cartesian closed.

[^lh]: An example is the category of locales and local homeomorphisms,
$\thecat{LH}$. Each slice $\thecat{LH}/X$ is Cartesian closed ---
they're even topoi --- but $\thecat{LH}$ has no terminal object.


[base change]: Cat.Functor.Pullback.html

```agda
record Locally-cartesian-closed {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ ℓ) where
  field
    has-is-lex : Finitely-complete C
    slices-cc  : ∀ A → Cartesian-closed (Slice C A)
      (Slice-products (Finitely-complete.pullbacks has-is-lex))
      Slice-terminal-object
```

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) (fp : Finitely-complete C) where
  open Locally-cartesian-closed
  open Finitely-complete fp
  open Cat.Reasoning C
  open Pullback

  module _ {A : Ob} where
    private module Fc = Cat.Reasoning Cat[ Slice C A , Slice C A ]
    ×/ = Binary-products.×-functor (Slice C A) (Slice-products pullbacks)
    open make-natural-iso
```
-->

The idea of exponentials in a slice is pretty complicated[^sets], so
fortunately, there is an alternative characterisation of local cartesian
closure, which is informed by $\cC$'s _internal type theory_.

Recall that, when thinking about dependent type theory in a category
$\cC$, we have the following dictionary: The objects of $\cC$ correspond
to the _contexts_ $\Gamma, \Delta, \dots$, and the morphisms $\Gamma \to
\Delta$ are the _substitutions_ between those contexts. The objects in
$\cC/\Gamma$ are the _types in context $\Gamma$_. From this point of
view, the [[pullback functors]] implement _substitution_ in a dependent
type, mapping a type $\Gamma \vdash A$ to $\Delta \vdash \sigma^*A$,
along the substitution $\sigma : \Delta \to \Gamma$.

[^sets]: Indeed, even for the category $\Sets$, showing local Cartesian
closure is not at all straightforward: the local exponential $f^g$ over
$B$ is the set $\sum_{b : B} f^{-1}(b) \to g^{-1}(b)$, though this
computation is best understood in terms of [slices of
sets](Cat.Instances.Slice.html#slices-of-sets).

To make this a bit clearer, let's focus on the simplest case, where
$\sigma$ is the projection of a variable $\pi_1 : \Gamma.A \to \Gamma$.
Instantiating the discussion above, we discover that base change along
$\pi_1$ will map types $\Gamma \vdash B$ to their _weakenings_ $\Gamma,
x : A \vdash \pi_1^*B$.

Under this correspondence, what do _dependent function types_ correspond
to?  Let's roll up our sleeves and write out some gosh-darn $\Gamma$s
and turnstiles. It's not much, but it's honest work. We have the
introduction and elimination rules

<div class=mathpar>

$$
\frac{
  \Gamma, x : A \vdash e : B
}{
  \Gamma \vdash (\lambda x. e) : \Pi_{(x : A)}B(x)
}
$$

$$
\frac{
  \Gamma \vdash f : \Pi_{x : A}B(x) \quad
  \Gamma \vdash e : A
}{
  \Gamma \vdash f(x) : B(e)
}
$$

</div>

which, by abstracting away the substitution of the argument[^app],
expresses that there is an isomorphism between derivations $\Gamma
\vdash f : \Pi_{(x : A)} B(x)$ and $\Gamma, x : A \vdash f(x) : B(x)$.
If we squint, this says precisely that $\Pi$ is a [[right adjoint]] to
the action of base change along $\pi_1 : \Gamma.A \to A$!

[^app]: To expand on the idea of this more _categorical_ application, if
we have $\Gamma \vdash f : \Pi_{x : A}B(x)$, we first "open" it to
uncover $\Gamma, x : A \vdash f(x) : B(x)$; if we then have an argument
$\Gamma \vdash a : A$, then we can use substitution to obtain $\Gamma
\vdash f(x)[a/x] : B(a)$.

This is our second characterisation of locally Cartesian closed
categories. Generalising away from weakenings, we should have a
correspondence between $\hom(f^*A, B)$ and $\hom(A, \Pi_f B)$, for an
arbitrary substitution $f : \Gamma \to \Delta$. Back to categorical
language, that is a [[right adjoint]] to the [[base change
functor|pullback functor]], fitting into an adjoint triple

$$
\Sigma_f \dashv f^* \dashv \textstyle\Pi_f\text{.}
$$

## From dependent products

But how does this correlate to the characterisation in terms of
Cartesian closed slices? Other than the intuition about "function types
(in context) between dependent types", we can do some honest category
theory. First, observe that, for $f : X \to A$, the product functor $-
\times f : \cC/A \to \cC/A$ is isomorphically given by

$$
\cC/A \xto{f^*} \cC/X \xto{\Sigma_f} \cC/A \text{,}
$$

since [[products in a slice]] are implemented by pullbacks in $\cC$; We
can chase a $g : Y \to A$ along the above diagram to see that it first
gets sent to $f^*g$ as in the diagram

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  {X \times_A Y} \&\& Y \\
  \\
  X \&\& {A\text{,}}
  \arrow["f"', from=3-1, to=3-3]
  \arrow["g", from=1-3, to=3-3]
  \arrow[from=1-1, to=1-3]
  \arrow["{f^*g}"', from=1-1, to=3-1]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

by the pullback functor, then to $f \circ (f^*g) : X \times_A Y \to A$
by the dependent sum. But this is exactly the object $g \times f$ in
$\cC/A$, so that $- \times f$ and $\Sigma_f f^*$ are indeed naturally
isomorphic.

```agda
    Slice-product-functor : ∀ {X} → make-natural-iso
      (Σf (X .map) F∘ Base-change pullbacks (X .map))
      (Bifunctor.Left ×/ X)

    Slice-product-functor .eta x .map      = id
    Slice-product-functor .eta x .commutes = idr _ ∙ pullbacks _ _ .square
    Slice-product-functor .inv x .map      = id
    Slice-product-functor .inv x .commutes = idr _ ∙ sym (pullbacks _ _ .square)
    Slice-product-functor .eta∘inv x     = ext $ idl _
    Slice-product-functor .inv∘eta x     = ext $ idl _
    Slice-product-functor .natural x y f = ext $ id-comm ∙ ap (id ∘_) (pullbacks _ _ .unique
      (pullbacks _ _ .p₁∘universal) (pullbacks _ _ .p₂∘universal ∙ idl _))
```

If we then have a functor $\Pi_f$ fitting into an adjoint triple
$\Sigma_f \dashv f^* \dashv \Pi_f$, we can [[compose|adjunctions
compose]] that to obtain $\Sigma_f f^* \dashv \Pi_f f^*$, and, by the
natural isomorphism we just constructed, $- \times f \dashv \Pi_f f^*$.
Since a right adjoint to Cartesian product is exactly the definition of
an exponential object, such an adjoint triple serves to conclude that
each slice of $\cC$ is Cartesian closed.

```agda
  dependent-product→lcc
    : (Πf    : ∀ {a b} (f : Hom a b) → Functor (Slice C a) (Slice C b))
    → (f*⊣Πf : ∀ {a b} (f : Hom a b) → Base-change pullbacks f ⊣ Πf f)
    → Locally-cartesian-closed C
  dependent-product→lcc Πf adj = record { has-is-lex = fp ; slices-cc = slice-cc } where
    slice-cc : (A : Ob) → Cartesian-closed (Slice C A) _ _
    slice-cc A = product-adjoint→cartesian-closed (Slice C A) _ _
      (λ f → Πf (f .map) F∘ Base-change pullbacks (f .map))
      λ A → adjoint-natural-isol (to-natural-iso Slice-product-functor)
              (LF⊣GR (adj _) (Σf⊣f* _ _))
```

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) (lcc : Locally-cartesian-closed C) where
  open Locally-cartesian-closed lcc
  open Finitely-complete has-is-lex
  open Cat.Reasoning C
  open Pullback

  private
    module _ A where open Cartesian-closed (slices-cc A) public

    prod/ : ∀ {a} → has-products (Slice C a)
    prod/ = Slice-products pullbacks

    pullback/ : ∀ {b} → has-pullbacks (Slice C b)
    pullback/ = Slice-pullbacks pullbacks
```
-->

## Recovering the adjunction

Now suppose that each slice of $\cC$ is Cartesian closed. How do we
construct the dependent product $\Pi_f : \cC/A \to \cC/B$? Happily, this
is another case where we just have to assemble preëxisting parts, like
we're putting together a theorem from IKEA.

We already know that, since $f : A \to B$ is an [[exponentiable object]]
in $\cC/B$, there is a _product along $f$ functor_, mapping from the
double slice $(\cC/B)/f \to \cC/B$, which is a right adjoint to the
[[constant families]] functor $\cC/B \to (\cC/B)/f$. And since (by the
yoga of [[iterated slices]]) $(\cC/B)/f$ is identical to $\cC/A$, this
becomes a functor $\Pi_f : \cC/A \to \cC/B$, of the right type.

```agda
  lcc→dependent-product
    : ∀ {a b} (f : Hom a b) → Functor (Slice C a) (Slice C b)
  lcc→dependent-product {a} {b} f =
       exponentiable→product _ _ _ _ (has-exp b (cut f)) pullback/
    F∘ Slice-twice f
```

It remains to verify that it's actually an adjoint to pullback along
$f$. We know that it's a right adjoint to the constant families functor
$\Delta_f$ _on $\cC/B$_, and that constant families are given by $\pi_2
: g \times f \to f$. Since the Cartesian product in a slice is given by
pullback, the base change functor turns out naturally isomorphic to
$f^*$, when regarded as a functor $\cC/B \to \cC/A$ through the
equivalence $(\cC/B)/f \cong \cC/A$.

```agda
  lcc→pullback⊣dependent-product
    : ∀ {a b} (f : Hom a b) → Base-change pullbacks f ⊣ lcc→dependent-product f
  lcc→pullback⊣dependent-product {b = b} f = adjoint-natural-isol
    (to-natural-iso rem₂) (LF⊣GR rem₁ (Twice⊣Slice f))
    where
    rem₁ : constant-family prod/ ⊣ exponentiable→product (Slice C _) _ _ _ _ _
    rem₁ = exponentiable→constant-family⊣product _ _ _ _ _ _

    rem₂ : make-natural-iso (Twice-slice f F∘ constant-family prod/)
                            (Base-change pullbacks f)
    rem₂ .eta x .map      = id
    rem₂ .eta x .commutes = idr _
    rem₂ .inv x .map      = id
    rem₂ .inv x .commutes = idr _
    rem₂ .eta∘inv x = ext (idr _)
    rem₂ .inv∘eta x = ext (idr _)
    rem₂ .natural x y f = ext $
         idr _
      ·· ap (pullbacks _ _ .universal) prop!
      ·· sym (idl _)
```
