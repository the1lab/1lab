<!--
```agda
open import Cat.Instances.Elements.Covariant
open import Cat.Diagram.Coproduct.Copower
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Functor.Hom.Representable
open import Cat.Functor.Equivalence.Path
open import Cat.Instances.Sets.Complete
open import Cat.Functor.Adjoint.Hom
open import Cat.Functor.Equivalence
open import Cat.Functor.Hom.Duality
open import Cat.Instances.Functor
open import Cat.Diagram.Terminal
open import Cat.Diagram.Initial
open import Cat.Functor.Adjoint
open import Cat.Instances.Comma
open import Cat.Instances.Sets
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Reasoning

open Corepresentation
open Representation
open Functor
```
-->

```agda
module Cat.Functor.Adjoint.Representable {o ℓ} {C : Precategory o ℓ} where
```

# Adjoints in terms of representability

Building upon our characterisation of [[adjoints as Hom isomorphisms]], we now
investigate the relationship between [[adjoint functors]] and [[representable
functors]].

In this section, we show that for a functor $R : \cC \to \cD$ to be a right adjoint
is equivalent to the functor $\hom_\cD(d, R-) : \cC \to \Sets$ having a representing
object for all $d : \cD$.

The forward direction follows directly from the natural isomorphism $\hom_\cC(Ld, -)
\cong \hom_\cD(d, R-)$, which exhibits $Ld$ as a representing object.

<!--
```agda
module _ {o'} {D : Precategory o' ℓ}
  {L : Functor D C} {R : Functor C D} (L⊣R : L ⊣ R)
  where
```
-->

```agda
  right-adjoint→objectwise-rep
    : ∀ d → Corepresentation (Hom-from D d F∘ R)
  right-adjoint→objectwise-rep d .corep = L .F₀ d
  right-adjoint→objectwise-rep d .corepresents =
    adjunct-hom-iso-from L⊣R d ni⁻¹

  left-adjoint→objectwise-rep
    : ∀ c → Corepresentation (Hom-into C c F∘ Functor.op L)
  left-adjoint→objectwise-rep c .corep = R .F₀ c
  left-adjoint→objectwise-rep c .corepresents =
    adjunct-hom-iso-into L⊣R c
    ∘ni path→iso (sym (Hom-from-op _))
```

The other direction should be more surprising: if we only have a family of objects
$Ld$ representing the functors $\hom_\cD(d, R-)$, why should we expect them to
assemble into a *functor* $L : \cD \to \cC$?

We answer the question indirectly^[for a more direct construction based on the Yoneda
embedding, see the [nLab](https://ncatlab.org/nlab/show/adjoint+functor#AdjointFunctorFromObjectwiseRepresentingObject)]:
what is a sufficient condition for $R$ to have a left adjoint?
Well, by our characterisation in terms of [[universal morphisms]], it should be
enough to have [[initial objects]] for each [[comma category]] $d \swarrow R$.
But we have also `established`{.Agda ident=corepresentation→initial-element}
that a (covariant) functor into $\Sets$ is representable if and only if its
[[category of elements|covariant category of elements]] has an initial object.

Now we simply observe that the comma category $d \swarrow R$ and the category of
elements of $\hom_\cD(d, R-)$ are exactly the same: both are made out of pairs of
an object $c : \cC$ and a map $d \to Rc$, with the morphisms between them obtained
in the obvious way from morphisms in $\cC$.

<!--
```agda
module _ {o'} {D : Precategory o' ℓ}
  {R : Functor C D}
  (corep : ∀ d → Corepresentation (Hom-from D d F∘ R))
  where

  private
    module D = Cat.Reasoning D
```
-->

```agda
  private
    ↙≡∫ : ∀ d → d ↙ R ≡ ∫ C (Hom-from D d F∘ R)
```

<details>
<summary>The proof is by obnoxious data repackaging, so we hide it away.</summary>

```agda
    ↙≡∫ d = Precategory-path F F-is-precat-iso where
      open is-precat-iso

      F : Functor (d ↙ R) (∫ C (Hom-from D d F∘ R))
      F .F₀ m = elem (m .↓Obj.y) (m .↓Obj.map)
      F .F₁ f = elem-hom (f .↓Hom.β) (sym (f .↓Hom.sq) ∙ D.idr _)
      F .F-id = Element-hom-path _ _ refl
      F .F-∘ f g = Element-hom-path _ _ refl

      F-is-precat-iso : is-precat-iso F
      F-is-precat-iso .has-is-iso = is-iso→is-equiv is where
        is : is-iso (F .F₀)
        is .is-iso.inv e = ↓obj (e .Element.section)
        is .is-iso.rinv e = refl
        is .is-iso.linv o = ↓Obj-path _ _ refl refl refl
      F-is-precat-iso .has-is-ff = is-iso→is-equiv is where
        is : is-iso (F .F₁)
        is .is-iso.inv h = ↓hom (D.idr _ ∙ sym (h .Element-hom.commute))
        is .is-iso.rinv h = Element-hom-path _ _ refl
        is .is-iso.linv h = ↓Hom-path _ _ refl refl
```
</details>

```agda
  objectwise-rep→universal-maps : ∀ d → Universal-morphism d R
  objectwise-rep→universal-maps d = subst Initial (sym (↙≡∫ d))
    (corepresentation→initial-element (corep d))

  objectwise-rep→L : Functor D C
  objectwise-rep→L = universal-maps→L R objectwise-rep→universal-maps

  objectwise-rep→L⊣R : objectwise-rep→L ⊣ R
  objectwise-rep→L⊣R = universal-maps→L⊣R R objectwise-rep→universal-maps
```

## Right adjoints into Sets are representable

For functors into $\Sets_\ell$, we can go one step further: under certain conditions,
being a right adjoint is equivalent to being representable.

Indeed, if $R$ has a left adjoint $L : \Sets_\ell \to \cC$, then $R$ is automatically
represented by $L\{*\}$, the image of the singleton set by $L$, because we have
$\hom_\cC(L\{*\}, c) \cong (\{*\} \to Rc) \cong Rc$.

<!--
```agda
module _
  {R : Functor C (Sets ℓ)} {L : Functor (Sets ℓ) C} (L⊣R : L ⊣ R)
  where
```
-->

```agda
  open Terminal (Sets-terminal {ℓ})

  right-adjoint→corepresentable : Corepresentation R
  right-adjoint→corepresentable .corep = L .F₀ top
  right-adjoint→corepresentable .corepresents =
    iso→isoⁿ (λ _ → equiv→iso (Π-⊤-eqv e⁻¹)) (λ _ → refl)
    ∘ni adjunct-hom-iso-from L⊣R top ni⁻¹
```

Going the other way, if we assume that $\cC$ is [[copowered]] over $\Sets_\ell$
(in other words, that it admits $\ell$-small [[indexed coproducts]]), then any
functor $R$ with representing object $c$ has a left adjoint given by taking copowers
of $c$: for any set $X$, we have $\hom_\cC(X \otimes c, -) \cong
(X \to \hom_\cC(c, -)) \cong (X \to R-)$.

<!--
```agda
module _
  (copowered : has-indexed-coproducts C ℓ)
  {R : Functor C (Sets ℓ)} (R-corep : Corepresentation R)
  where
```
-->

```agda
  private
    open Copowers (λ _ → copowered)

    Hom[X,R-]-rep : ∀ X → Corepresentation (Hom-from (Sets ℓ) X F∘ R)
    Hom[X,R-]-rep X .corep = X ⊗ R-corep .corep
    Hom[X,R-]-rep X .corepresents =
      F∘-iso-r (R-corep .corepresents)
      ∘ni copower-hom-iso ni⁻¹

  corepresentable→L : Functor (Sets ℓ) C
  corepresentable→L = objectwise-rep→L Hom[X,R-]-rep

  corepresentable→L⊣R : corepresentable→L ⊣ R
  corepresentable→L⊣R = objectwise-rep→L⊣R Hom[X,R-]-rep
```
