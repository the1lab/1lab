<!--
```agda
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Instances.Shape.Interval
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Coequaliser
open import Cat.Diagram.Pullback
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Coequaliser.RegularEpi where
```

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C
  private variable a b : Ob
```
-->

# Regular epimorphisms {defines="regular-epi regular-epimorphism"}

[Dually] to [regular monomorphisms], which behave as _embeddings_,
regular [epimorphisms] behave like _covers_: A regular epimorphism $f :
a \epi b$ expresses $b$ as "a union of parts of $a$, possibly glued
together".

[Dually]: Cat.Base.html#opposites
[regular monomorphisms]: Cat.Diagram.Equaliser.RegularMono.html
[epimorphisms]: Cat.Morphism.html#epis

The definition is also precisely dual: A map $f : a \to b$ is a
**regular epimorphism** if it is the [coequaliser] of some pair of
arrows $R \tto a$.

[coequaliser]: Cat.Diagram.Coequaliser.html

```agda
  record is-regular-epi (f : Hom a b) : Type (o ⊔ ℓ) where
    no-eta-equality
    constructor reg-epi
    field
      {r}           : Ob
      {arr₁} {arr₂} : Hom r a
      has-is-coeq   : is-coequaliser C arr₁ arr₂ f

    open is-coequaliser has-is-coeq public
```

From the definition we can directly conclude that regular epis are in
fact epic:

```agda
    is-regular-epi→is-epic : is-epic f
    is-regular-epi→is-epic = is-coequaliser→is-epic _ has-is-coeq

  open is-regular-epi using (is-regular-epi→is-epic) public
```

## Effective epis

Again by duality, we have a pair of canonical choices of maps which $f$
may coequalise: Its _kernel pair_, that is, the [[pullback]] of $f$ along
itself. An epimorphism which coequalises its kernel pair is called an
**effective epi**, and effective epis are immediately seen to be regular
epis:

```agda
  record is-effective-epi (f : Hom a b) : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      {kernel}       : Ob
      p₁ p₂          : Hom kernel a
      has-kernel-pair : is-kernel-pair C p₁ p₂ f
      has-is-coeq    : is-coequaliser C p₁ p₂ f

    is-effective-epi→is-regular-epi : is-regular-epi f
    is-effective-epi→is-regular-epi = re where
      open is-regular-epi hiding (has-is-coeq)
      re : is-regular-epi f
      re .r = _
      re .arr₁ = _
      re .arr₂ = _
      re .is-regular-epi.has-is-coeq = has-is-coeq
```

If a regular epimorphism (a coequaliser) has a kernel pair, then it is
also the coequaliser of its kernel pair. That is: If the pullback of $a
\xto{f} b \xot{f} a$ exists, then $f$ is also an effective epimorphism.

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C
  private variable a b : Ob
```
-->

```agda
  is-regular-epi→is-effective-epi
    : ∀ {a b} {f : Hom a b}
    → Pullback C f f
    → is-regular-epi C f
    → is-effective-epi C f
  is-regular-epi→is-effective-epi {f = f} kp reg = epi where
    module reg = is-regular-epi reg
    module kp = Pullback kp

    open is-effective-epi
    open is-coequaliser
    epi : is-effective-epi C f
    epi .kernel = kp.apex
    epi .p₁ = kp.p₁
    epi .p₂ = kp.p₂
    epi .has-kernel-pair = kp.has-is-pb
    epi .has-is-coeq .coequal = kp.square
    epi .has-is-coeq .universal {F = F} {e'} p = reg.universal q where
      q : e' ∘ reg.arr₁ ≡ e' ∘ reg.arr₂
      q =
        e' ∘ reg.arr₁                               ≡⟨ ap (e' ∘_) (sym kp.p₂∘universal) ⟩
        e' ∘ kp.p₂ ∘ kp.universal (sym reg.coequal)  ≡⟨ pulll (sym p) ⟩
        (e' ∘ kp.p₁) ∘ kp.universal _                ≡⟨ pullr kp.p₁∘universal ⟩
        e' ∘ reg.arr₂                               ∎
    epi .has-is-coeq .factors = reg.factors
    epi .has-is-coeq .unique = reg.unique
```

# Existence of regular epis

Let $\cJ, \cC$ be a categories such that $\cC$ has coproducts indexed
by the objects and arrows of $\cC$, and let $F : \cJ \to \cC$ be a functor
with a colimit $C$ in $\cC$. The canonical map $\coprod_{j : \cJ} F(j) \to C$
is a regular epimorphism

```agda
module _ {o ℓ oj ℓj}
  {C : Precategory o ℓ} {J : Precategory oj ℓj}
  {F : Functor J C}
  (∐Ob : has-coproducts-indexed-by C ⌞ J ⌟)
  (∐Hom : has-coproducts-indexed-by C (Arrows J))
  (∐F : Colimit F)
  where
```

<!--
```agda
  private
    module C = Cat.Reasoning C
    module J = Cat.Reasoning J
    module F = Cat.Functor.Reasoning F
    module ∐Ob F = Indexed-coproduct (∐Ob F)
    module ∐Hom F = Indexed-coproduct (∐Hom F)
    module ∐F = Colimit ∐F

  open is-regular-epi
  open is-coequaliser
```
-->

```agda
  indexed-coproduct→regular-epi : is-regular-epi C (∐Ob.match F.₀ ∐F.ψ)
```

We start by constructing a pair of maps $p, q : \coprod_{f : \cJ(i,j)} F(i) \to \coprod_{j : \cJ} F(j)$
via the universal property of $\coprod_{f : \cJ(i,j)} F(i)$.

```agda
  indexed-coproduct→regular-epi .r = ∐Hom.ΣF λ (i , j , f) → F.₀ i
  indexed-coproduct→regular-epi .arr₁ = ∐Hom.match _ λ (i , j , f) → ∐Ob.ι F.₀ j C.∘ F.₁ f
  indexed-coproduct→regular-epi .arr₂ = ∐Hom.match _ λ (i , j , f) → ∐Ob.ι F.₀ i
```

By some rather tedious calculations, we can show that $p$ and $q$
coequalize $f$.

```agda
  indexed-coproduct→regular-epi .has-is-coeq .coequal =
    ∐Hom.unique₂ _ λ (i , j , f) →
    (∐Ob.match F.₀ ∐F.ψ C.∘ ∐Hom.match _ _) C.∘ ∐Hom.ι _ (i , j , f) ≡⟨ C.pullr (∐Hom.commute _) ⟩
    ∐Ob.match F.₀ ∐F.ψ C.∘ ∐Ob.ι _ j C.∘ F.₁ f                       ≡⟨ C.pulll (∐Ob.commute _) ⟩
    ∐F.ψ j C.∘ F.₁ f                                                 ≡⟨ ∐F.commutes f ⟩
    ∐F.ψ i                                                           ≡˘⟨ ∐Ob.commute _ ⟩
    ∐Ob.match F.₀ ∐F.ψ C.∘ ∐Ob.ι _ i                                 ≡˘⟨ C.pullr (∐Hom.commute _) ⟩
    (∐Ob.match F.₀ ∐F.ψ C.∘ ∐Hom.match _ _) C.∘ ∐Hom.ι _ (i , j , f) ∎
```

Moreover, $p$ and $q$ form the universal such coequalizing pair. This
follows by yet more brute-force calculation.

```agda
  indexed-coproduct→regular-epi .has-is-coeq .universal {e' = e'} p =
    ∐F.universal (λ j → e' C.∘ ∐Ob.ι F.₀ j) comm
    where abstract
      comm
        : ∀ {i j} (f : J.Hom i j)
        → (e' C.∘ ∐Ob.ι F.₀ j) C.∘ F.₁ f ≡ e' C.∘ ∐Ob.ι F.₀ i
      comm {i} {j} f =
        (e' C.∘ ∐Ob.ι F.₀ j) C.∘ F.₁ f                   ≡⟨ C.pullr (sym (∐Hom.commute _)) ⟩
        e' C.∘ (∐Hom.match _ _ C.∘ ∐Hom.ι _ (i , j , f)) ≡⟨ C.extendl p ⟩
        e' C.∘ (∐Hom.match _ _ C.∘ ∐Hom.ι _ (i , j , f)) ≡⟨ ap₂ C._∘_ refl (∐Hom.commute _) ⟩
        e' C.∘ ∐Ob.ι F.₀ i                               ∎
  indexed-coproduct→regular-epi .has-is-coeq .factors {e' = e'} {p = p} =
    ∐Ob.unique₂ F.₀ λ j →
      (∐F.universal _ _ C.∘ ∐Ob.match F.₀ ∐F.ψ) C.∘ ∐Ob.ι F.₀ j ≡⟨ C.pullr (∐Ob.commute _) ⟩
      ∐F.universal _ _ C.∘ ∐F.ψ j                               ≡⟨ ∐F.factors _ _ ⟩
      e' C.∘ ∐Ob.ι F.₀ j                                        ∎
  indexed-coproduct→regular-epi .has-is-coeq .unique {e' = e'} {colim = h} p =
    ∐F.unique _ _ _ λ j →
      h C.∘ ∐F.ψ j                               ≡˘⟨ ap₂ C._∘_ refl (∐Ob.commute _) ⟩
      h C.∘ (∐Ob.match F.₀ ∐F.ψ C.∘ ∐Ob.ι F.₀ j) ≡⟨ C.pulll p ⟩
      e' C.∘ ∐Ob.ι F.₀ j                         ∎
```
