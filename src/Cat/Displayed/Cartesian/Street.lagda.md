<!--
```agda
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Cartesian.Street where
```

<!--
```agda
open Displayed
```
-->

# Street fibrations

In classical category theory, a [[fibration|cartesian fibration]] is
defined to be a certain functor $P : \cE \to \cB$, the idea being that
$\cE$ is really the [[total category]] of a certain [[displayed
category]], and $P$ is really the first projection functor $\pi^f$,
which sends each displayed object to the object it is displayed over.
But can we go the other way? If we have a functor $P : \cE \to \cB$, can
we create a category displayed $\cE'$ over $\cB$, such that $\int \cE'
\cong \cE$?

<!--
```agda
module _ {o ℓ o' ℓ'} {E : Precategory o ℓ} {B : Precategory o' ℓ'} (P : Functor E B) where
  private
    module E = Cat.Reasoning E
    module B = Cat.Reasoning B
    module P = Functor P
  open B.HLevel-instance
  open E.HLevel-instance
```
-->

```agda
  functor→displayed : Displayed B (o ⊔ ℓ') (ℓ ⊔ ℓ')
  functor→displayed .Ob[_] x = Σ[ u ∈ E.Ob ] (P.₀ u B.≅ x)
```

Following [@relativect], we define such a category by defining the space
of objects over $x$ to be "left corners". Strictly speaking, a left
corner is given by an object $u$ together with an isomorphism $\phi :
P(u) \cong x$. But visually, we depict them as

~~~{.quiver}
\[\begin{tikzcd}
  u \\
  {P(u)} & {x\text{,}}
  \arrow[lies over, from=1-1, to=2-1]
  \arrow["\phi"', from=2-1, to=2-2]
\end{tikzcd}\]
~~~

whence the name "left corner". The maps lying over $f$ consist of those
maps $u \to_f v$ which commute with the mediating isomorphisms:

```agda
  functor→displayed .Hom[_] f (u , φ) (v , ψ) =
    Σ[ h ∈ E.Hom u v ] (B.to ψ B.∘ P.₁ h ≡ f B.∘ B.to φ)
```

This fits in a diagram like the one below. Note that the commutativity
condition is for the lower shape, which is a distorted square.

~~~{.quiver .tall-2}
\[\begin{tikzcd}
  & u && v \\
  & {P(u)} && {P(v)} \\
  x &&&& y
  \arrow[lies over, from=1-2, to=2-2]
  \arrow[lies over, from=1-4, to=2-4]
  \arrow["{P(h)}"', from=2-2, to=2-4]
  \arrow["h"{description}, from=1-2, to=1-4]
  \arrow["\phi"', from=3-1, to=2-2]
  \arrow["\psi"', from=2-4, to=3-5]
  \arrow["f"', curve={height=12pt}, from=3-1, to=3-5]
\end{tikzcd}\]
~~~

The axioms for a displayed category are evident: all that matters are
the maps in the total category $\cE$, since the rest of the data is
property (rather than data).

```agda
  functor→displayed .Hom[_]-set f a b = hlevel 2
  functor→displayed .id' = E.id , B.elimr P.F-id ∙ B.introl refl
  functor→displayed ._∘'_ (f , φ) (g , ψ) = f E.∘ g ,
    ap₂ B._∘_ refl (P.F-∘ f g) ∙ B.pulll φ ∙ B.pullr ψ ∙ B.assoc _ _ _
  functor→displayed .idr' f' = Σ-pathp (E.idr _) $
    is-set→squarep (λ _ _ → hlevel 2) _ _ _ _
  functor→displayed .idl' f' = Σ-pathp (E.idl _) $
    is-set→squarep (λ _ _ → hlevel 2) _ _ _ _
  functor→displayed .assoc' f' g' h' = Σ-pathp (E.assoc _ _ _) $
    is-set→squarep (λ _ _ → hlevel 2) _ _ _ _
```

We call a functor that gives rise to a Cartesian fibration through this
process a **Street fibration**. It is routine to verify that _our_
notion of Street fibration corresponds to.. well, Street's.
