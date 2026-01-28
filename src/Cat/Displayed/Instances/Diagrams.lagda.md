<!--
```agda
open import Cat.Displayed.Instances.Pullback
open import Cat.Displayed.Instances.Lifting
open import Cat.Displayed.Cartesian
open import Cat.Functor.Equivalence
open import Cat.Displayed.Functor
open import Cat.Instances.Functor
open import Cat.Functor.Constant
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
```
-->

```agda
module Cat.Displayed.Instances.Diagrams
  {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ')
  where
```

<!--
```agda
open Cat.Displayed.Reasoning E
open Precategory B
open Functor
open _=>_
```
-->

# The diagram fibration

The appropriate notion of structure for a [[displayed category]] $\cE
\liesover \cB$ is fibrewise structure: structure found in each [[fibre
category]], preserved by the reindexing functors when $\cE$ is an
(op)fibration.

For instance, the correct notion of $\cJ$-shaped limit in $\cE$ are the
**fibred limits**: where every fibre category has limits of shape $\cJ$,
and these are preserved by reindexing. Unfortunately, proof assistants:
since none of the commutativity conditions for limits are definitional,
this definition condemns the formaliser to transport hell.

Instead, we opt for a more abstract approach, which starts with a
reorganization of what a fibrewise diagram in $\cE$ is. Recall that the
[fibration of liftings] describes liftings of functors $\cJ \to \cB$
along the projection functor $\pi : \int \cE \to \cB$. If we focus on
liftings along a constant functor $\Delta_{x} : \cJ \to \cB$, we get a
diagram in $\cE$ that lies entirely in the fibre $\cE_{x}$: a fibrewise
diagram!

This allows us to concisely define the fibration of fibrewise diagrams
as the base change of $\cE \to \cB$ along the functor $\cB \to [\cJ,
\cB]$ that takes an object to the constant diagram on that object.

[fibration of liftings]: Cat.Displayed.Instances.Lifting.html

```agda
Diagrams
 : ∀ {oj ℓj} (J : Precategory oj ℓj)
 → Displayed B _ _
Diagrams J = Change-of-base ConstD (Liftings E J)
```

When $\cE$ is a fibration, then so is the fibration of diagrams.

<!--
```agda
module _ {oj ℓj} (J : Precategory oj ℓj) where
  private module J = Precategory J
  open Lifting
  open _=[_]=>l_
```
-->

```agda
  Diagram-fibration : Cartesian-fibration E → Cartesian-fibration (Diagrams J)
  Diagram-fibration fib =
    Change-of-base-fibration ConstD (Liftings E _)
      (Liftings-fibration E _ fib)
```

## The constant fibrewise diagram functor

Crucially, we have a "constant fibrewise diagram functor" that takes an
object $x' : E_{x}$ to the constant diagram. However, defining this
functor will require a small bit of machinery.

To begin, we characterize liftings of the constant functor, and natural
transformations between them.

```agda
  ConstL : ∀ {x} → Ob[ x ] → Lifting {J = J} E (Const x)
  ConstL x' .F₀' _ = x'
  ConstL x' .F₁' _ = id'
  ConstL x' .F-id' = cast[] (λ _ → id')
  ConstL x' .F-∘' _ _ = cast[] (symP (idr' _))

  const-ntl
    : ∀ {x y x' y'} {f : Hom x y} → Hom[ f ] x' y'
    → ConstL x' =[ constⁿ f ]=>l ConstL y'
  const-ntl f' .η' _ = f'
  const-ntl f' .is-natural' _ _ _ = cast[] (idr' _ ∙[] (symP (idl' _)))
```

We also have a vertical functor from $\cE$ to the fibration of diagrams
of shape $\cJ$, which takes an $x'$ to the constant diagram.

```agda
  ConstFibD : Vertical-functor E (Diagrams J)
  ConstFibD .Vertical-functor.F₀' = ConstL
  ConstFibD .Vertical-functor.F₁' = const-ntl
  ConstFibD .Vertical-functor.F-id' = Nat-lift-pathp λ x → coh[ refl ] _
  ConstFibD .Vertical-functor.F-∘'  = Nat-lift-pathp λ x → coh[ refl ] _
```

Next, we note that liftings of the constant functor correspond with
diagrams in fibre categories.

```agda
  ConstL→Diagram : ∀ {x} → Lifting {J = J} E (Const x) → Functor J (Fibre E x)
  Diagram→ConstL : ∀ {x} → Functor J (Fibre E x) → Lifting {J = J} E (Const x)
```

<!--
```agda
  ConstL→Diagram F' .F₀ = F' .F₀'
  ConstL→Diagram F' .F₁ = F' .F₁'
  ConstL→Diagram F' .F-id = cast[] (F' .F-id')
  ConstL→Diagram F' .F-∘ f g = from-pathp[]⁻ $ cast[] (F' .F-∘' f g)

  Diagram→ConstL F .F₀' = F .F₀
  Diagram→ConstL F .F₁' = F .F₁
  Diagram→ConstL F .F-id' = cast[] (F .F-id)
  Diagram→ConstL F .F-∘' f g = cast[] $ to-pathp[]⁻ (F .F-∘ f g)
```
-->

Furthermore, natural transformations between diagrams in a fibre of $E$
correspond to natural transformations between liftings of a constant
functor.

```agda
  ConstL-natl→Diagram-nat
    : ∀ {x} {F G : Functor J (Fibre E x)}
    → Diagram→ConstL F =[ constⁿ id ]=>l Diagram→ConstL G
    → F => G

  Diagram-nat→ConstL-natl
    : ∀ {x} {F G : Functor J (Fibre E x)}
    → F => G
    → Diagram→ConstL F =[ constⁿ id ]=>l Diagram→ConstL G
```

<!--
```agda
  ConstL-natl→Diagram-nat α' .η = α' .η'
  ConstL-natl→Diagram-nat α' .is-natural x y f =
    ap hom[] (cast[] $ α' .is-natural' x y f)

  Diagram-nat→ConstL-natl α .η' = α .η
  Diagram-nat→ConstL-natl {F = F} {G = G} α .is-natural' x y f = cast[] $
    to-pathp[] (α .is-natural x y f)
    ∙[] symP (coh[ idl id ] (G .F₁ f ∘' α .η x))
```
-->

## Fibre categories

The fibre category of the fibration of diagrams are equivalent to
functor categories $[\cJ, \cE_x]$.

```agda
  Fibrewise-diagram : ∀ {x} → Functor Cat[ J , Fibre E x ] (Fibre (Diagrams J) x)
  Fibrewise-diagram .F₀      = Diagram→ConstL
  Fibrewise-diagram .F₁      = Diagram-nat→ConstL-natl
  Fibrewise-diagram .F-id    = Nat-lift-pathp λ _ → coh[ refl ] _
  Fibrewise-diagram .F-∘ _ _ = Nat-lift-pathp λ _ → sym (hom[]-∙ _ _ ∙ reindex _ _)
```

Again, this isomorphism is *almost* definitional.

```agda
  Fibrewise-diagram-is-iso : ∀ {x} → is-precat-iso (Fibrewise-diagram {x})
  Fibrewise-diagram-is-iso .is-precat-iso.has-is-ff = is-iso→is-equiv $ iso
    (ConstL-natl→Diagram-nat)
    (λ α' → Nat-lift-pathp (λ _ → refl))
    (λ α → ext (λ i → refl))
  Fibrewise-diagram-is-iso .is-precat-iso.has-is-iso = is-iso→is-equiv $ iso
    ConstL→Diagram
    (λ F' → Lifting-pathp E refl (λ _ → refl) (λ _ → refl))
    (λ F → Functor-path (λ _ → refl) (λ _ → refl))
```
