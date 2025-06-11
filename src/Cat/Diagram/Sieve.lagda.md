<!--
```agda
open import Cat.Instances.Presheaf.Limits
open import Cat.Diagram.Subterminal
open import Cat.Instances.Functor
open import Cat.Instances.Slice
open import Cat.Functor.Hom
open import Cat.Prelude

open import Data.Power

import Cat.Reasoning

open /-Obj
open /-Hom
```
-->

```agda
module Cat.Diagram.Sieve where
```

<!--
```agda
module _ {o κ : _} (C : Precategory o κ) (c : ⌞ C ⌟) where
  private module C = Precategory C
```
-->

# Sieves {defines="sieve"}

Given a category $\cC$, a **sieve** $S$ on an object $c$ is a subset of
the maps $a \to c$ closed under composition: if $f \in S$, then $(f
\circ g) \in S$. The data of a sieve on $c$ corresponds to the data of a
subobject of $\yo(c)$, considered as an object of $\psh(\cC)$.

Here, the subset is represented as the function `arrows`{.agda}, which,
given an arrow $f : a \to c$ (and its domain), yields a proposition
representing inclusion in the subset.

```agda
  record Sieve : Type (o ⊔ κ) where
    no-eta-equality
    field
      arrows : ∀ {y} → ℙ (C.Hom y c)
      closed : ∀ {y z f} (hf : f ∈ arrows) (g : C.Hom y z) → (f C.∘ g) ∈ arrows
  open Sieve public
```

The `maximal`{.agda} sieve on an object is the collection of _all_ maps
$a \to c$; It represents the identity map $\yo(c) \to \yo(c)$ as a
subfunctor. A [$\kappa$-small] family of sieves can be intersected (the
underlying predicate is the "$\kappa$-ary conjunction" $\Pi$ --- the
universal quantifier), and this represents a wide pullback of
subobjects.

[$\kappa$-small]: 1Lab.intro.html#universes-and-size-issues

<!--
```agda
module _ {o ℓ : _} {C : Precategory o ℓ} where
  private
    module C   = Cat.Reasoning C
    module PSh = Cat.Reasoning (PSh ℓ C)
    open Precategory C

  Sieve-path : ∀ {c} {x y : Sieve C c} → Path (∀ {y} → ℙ (C.Hom y c)) (x .arrows) (y .arrows) → x ≡ y
  Sieve-path {x = x} {y} p i .arrows = p i
  Sieve-path {x = x} {y} p i .closed {f = f} hf g =
    is-prop→pathp (λ i → fun-is-hlevel {A = ⌞ p i f ⌟} 1 (p i (f ∘ g) .is-tr)) (λ w → x .closed w g) (λ w → y .closed w g) i hf

  instance
    hom∈Sieve : ∀ {c d} → Membership (C.Hom d c) (Sieve C c) _
    hom∈Sieve = record { _∈_ = λ x S → x ∈ S .Sieve.arrows }

    slice∈Sieve : ∀ {c} → Membership (/-Obj {C = C} c) (Sieve C c) _
    slice∈Sieve = record { _∈_ = λ x S → x .map ∈ S }

    Inclusion-sieve : ∀ {U} → Inclusion (Sieve C U) _
    Inclusion-sieve {U} = record { _⊆_ = λ S T → ∀ {V} (h : Hom V U) → h ∈ S → h ∈ T }

    Extensional-sieve : ∀ {ℓr c} ⦃ _ : Extensional (∀ {y} → C.Hom y c → Ω) ℓr ⦄ → Extensional (Sieve C c) ℓr
    Extensional-sieve ⦃ e ⦄ = injection→extensional! Sieve-path e

    H-Level-Sieve : ∀ {c n} → H-Level (Sieve C c) (2 + n)
    H-Level-Sieve = basic-instance 2 $
      embedding→is-hlevel 1 (injective→is-embedding! Sieve-path) (hlevel 2)

  open PSh._↪_
  open _=>_
  open Functor
```
-->

```agda
  maximal' : ∀ {c} → Sieve C c
  maximal' .arrows x = ⊤Ω
  maximal' .closed g x = tt

  intersect : ∀ {c} {I : Type ℓ} (F : I → Sieve C c) → Sieve C c
  intersect {I = I} F .arrows h = elΩ ((x : I) → h ∈ F x)
  intersect {I = I} F .closed x g = inc λ i → F i .closed (□-out! x i) g
```

<!--
```agda
  _∩S_ : ∀ {U} → Sieve C U → Sieve C U → Sieve C U
  (S ∩S T) .arrows f = S .arrows f ∧Ω T .arrows f
  (S ∩S T) .closed (Sf , Tf) g = S .closed Sf g , T .closed Tf g
```
-->

## Representing subfunctors {defines="sieves-as-presheaves"}

Let $S$ be a sieve on $\cC$. We show that it determines a presheaf
$S'$, and that this presheaf admits a monic natural transformation $S'
\mono \yo(c)$. The functor determined by a sieve $S$ sends each object
$d$ to the set of arrows $d \xto{f} c$ s.t. $f \in S$; The functorial
action is given by composition, as with the $\hom$ functor.

```agda
  to-presheaf : ∀ {c} → Sieve C c → PSh.Ob
  to-presheaf {c} sieve .F₀ d = el! (Σ[ f ∈ C.Hom d c ] (f ∈ sieve))
  to-presheaf sieve .F₁ f (g , s) = g C.∘ f , sieve .closed s _
```

<!--
```agda
  to-presheaf sieve .F-id    = funext λ _ → Σ-prop-path! (C.idr _)
  to-presheaf sieve .F-∘ f g = funext λ _ → Σ-prop-path! (C.assoc _ _ _)
```
-->

That this functor is a subobject of $\yo$ follows straightforwardly: The
injection map $S' \mono \yo(c)$ is given by projecting out the first
component, which is an embedding (since "being in a sieve" is a
proposition). Since natural transformations are monic if they are
componentwise monic, and embeddings are monic, the result follows.

```agda
  to-presheaf↪よ : ∀ {c} {S : Sieve C c} → to-presheaf S PSh.↪ よ₀ C c
  to-presheaf↪よ {S} .mor .η x (f , _) = f
  to-presheaf↪よ {S} .mor .is-natural x y f = refl
  to-presheaf↪よ {S} .monic g h path = ext λ i x → Σ-prop-path! (unext path i x)
```

## Pullback of sieves {defines="pullback-sieve"}

If we have a sieve $R$ on $U$, and any morphism $f : V \to U$, then
there is a natural way to restrict the $h_i$ to a sieve on $V$: a
morphism $g : V_i \to V$ belongs to the restriction if the composite $fg
: V_i \to V \to U$ belongs to $R$. We refer to the resulting sieve as
the **pullback of $R$ along $f$**, and write it $f^*(R)$.

```agda
  pullback : ∀ {u v} → C.Hom v u → Sieve C u → Sieve C v
  pullback f s .arrows h = el (f C.∘ h ∈ s) (hlevel 1)
  pullback f s .closed hf g = subst (_∈ s) (sym (C.assoc f _ g)) (s .closed hf g)
```

If we consider the collection of "sieves on $U$" as varying along $U$ as
a parameter, the pullback operation becomes functorial. Since it is
contravariant, this means that the assignment $U \mapsto
\operatorname{Sieves}(U)$ is *itself* a presheaf on $U$.

```agda
  abstract
    pullback-id : ∀ {c} {s : Sieve C c} → pullback C.id s ≡ s
    pullback-id {s = s} = ext λ h → Ω-ua
      (subst (_∈ s) (C.idl h))
      (subst (_∈ s) (sym (C.idl h)))

    pullback-∘
      : ∀ {u v w} {f : C.Hom w v} {g : C.Hom v u} {R : Sieve C u}
      → pullback (g C.∘ f) R ≡ pullback f (pullback g R)
    pullback-∘ {f = f} {g} {R = R} = ext λ h → Ω-ua
      (subst (_∈ R) (sym (C.assoc g f h)))
      (subst (_∈ R) (C.assoc g f h))
```

This presheaf has an important universal property: the natural
transformations $X \to \operatorname{Sieves}$ correspond naturally to
the [[subobjects|poset of subobjects]] of $X$. Categorically, we say
that $\operatorname{Sieves}$ is a [[subobject classifier]] in the
category $\psh(\cC)$; for more details see [[subobject classifier
presheaf]].

```agda
  Sieves : Functor (C ^op) (Sets (o ⊔ ℓ))
  Sieves .F₀ U .∣_∣ = Sieve C U
  Sieves .F₀ U .is-tr = hlevel 2
  Sieves .F₁ = pullback
  Sieves .F-id    = funext λ x → pullback-id
  Sieves .F-∘ f g = funext λ x → pullback-∘
```

## Generated sieves

Often, it's more practical to define a *family* of maps, and to obtain a
sieve from this family after the fact. To this end, we define a type
`Cover`{.Agda} for families of maps into a common codomain, paired with
their indexing type.

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  open Precategory C using (Hom)
```
-->

```agda
  record Cover (U : ⌞ C ⌟) ℓ' : Type (o ⊔ ℓ ⊔ lsuc ℓ') where
    field
      {index}  : Type ℓ'
      {domain} : index → ⌞ C ⌟
      map      : ∀ i → Hom (domain i) U
```

<!--
```agda
open Cover

module _ {o ℓ} {C : Precategory o ℓ} where
  private module C = Cat.Reasoning C
  instance
    Underlying-Cover : ∀ {ℓ' U} → Underlying (Cover C U ℓ')
    Underlying-Cover = record { ⌞_⌟ = index }
```
-->

The **sieve generated by a cover** $(f_i : V_i \to U)_{i : I}$ is the
collection of maps that factor through at least one of the $f_i$, i.e.,
for a map $g : W \to U$, it is the proposition
$$
\exists (i : I) (h : W \to V_i).~ f_i \circ h = g
$$.

```agda
  cover→sieve : ∀ {ℓ' U} → Cover C U ℓ' → Sieve C U
  cover→sieve {U = U} f .arrows {W} g = elΩ do
    Σ[ i ∈ f ] Σ[ h ∈ C.Hom W (f .domain i) ] (f .map i C.∘ h ≡ g)
  cover→sieve f .closed = rec! λ i h p g → inc (i , h C.∘ g , C.pulll p)
```

Since the primary purpose of `Cover`{.Agda} is to present sieves, we
register an instance of the `⟦⟧-notation`{.Agda} class, so that we can
write `⟦ cov ⟧` instead of `cover→sieve cov`.

<!--
```agda
  map→sieve : ∀ {V U} → C.Hom V U → Sieve C U
  map→sieve f .arrows g = elΩ (Σ[ h ∈ C.Hom _ _ ] (f C.∘ h ≡ g))
  map→sieve f .closed = rec! λ g p h → inc (g C.∘ h , C.pulll p)

  instance
    ⟦⟧-Cover : ∀ {ℓ' U} → ⟦⟧-notation (Cover C U ℓ')
    ⟦⟧-Cover = brackets _ cover→sieve
```
-->

## Sieves in a category {defines="sieve-in"}

We have defined sieves *on* an object above, but there is also a notion
of sieve *in* a category $\cC$: a subcollection $S$ of the objects of
$\cC$ such that if $f : X \to Y$ is a morphism and $Y \in S$, then
$X \in S$.

<!--
```agda
module _ {o ℓ : _} (C : Precategory o ℓ) where
  private module C = Precategory C
```
-->

```agda
  record Sieve-in : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      objects : ℙ C.Ob
      closed : ∀ {x y} (hy : y ∈ objects) (f : C.Hom x y) → x ∈ objects
  open Sieve-in public
```

The two notions are related as follows:

- A sieve *on* an object $c : \cC$ is a sieve *in* the [[slice category]]
  $\cC/c$.
- If $\cC$ has a [[terminal object]] $\top$, then a sieve *in* $\cC$ is
  a sieve *on* $\top$.

<!--
```agda
module _ {o ℓ : _} {C : Precategory o ℓ} where

  Sieve-in-path : ∀ {s s' : Sieve-in C} → s .objects ≡ s' .objects → s ≡ s'
  Sieve-in-path p i .objects = p i
  Sieve-in-path {s = s} {s'} p i .closed {x = x} {y = y} hy f =
    is-prop→pathp (λ i → fun-is-hlevel {A = ⌞ p i y ⌟} 1 (p i x .is-tr)) (λ w → s .closed w f) (λ w → s' .closed w f) i hy

module _ {o ℓ : _} (C : Precategory o ℓ) (c : ⌞ C ⌟) where
```
-->

```agda
  Sieve→Sieve-in/c : Sieve C c → Sieve-in (Slice C c)
  Sieve→Sieve-in/c s .objects (cut f) = s .arrows f
  Sieve→Sieve-in/c s .closed hy f = subst (_∈ s .arrows) (f .commutes)
    (s .closed hy (f .map))

  Sieve-in/c→Sieve : Sieve-in (Slice C c) → Sieve C c
  Sieve-in/c→Sieve s .arrows f = s .objects (cut f)
  Sieve-in/c→Sieve s .closed hf g = s .closed hf λ where
    .map → g
    .commutes → refl

  Sieve≃Sieve-in/c : Sieve C c ≃ Sieve-in (Slice C c)
  Sieve≃Sieve-in/c .fst = Sieve→Sieve-in/c
  Sieve≃Sieve-in/c .snd = is-iso→is-equiv (iso Sieve-in/c→Sieve
    (λ s → Sieve-in-path refl) (λ s → Sieve-path refl))
```

Furthermore, just as sieves *on* $c : \cC$ correspond to subobjects of
the representable functor $\yo(c)$, sieves *in* $\cC$ correspond to
subobjects of the terminal presheaf, i.e. [[subterminal]] presheaves.

<!--
```agda
module _ {o ℓ : _} {C : Precategory o ℓ} where
  open Functor
  private
    module C = Precategory C
    module PSh = Cat.Reasoning (PSh lzero C)
```
-->

```agda
  Sieve-in→presheaf : Sieve-in C → PSh.Ob
  Sieve-in→presheaf s .F₀ c = el! (c ∈ s .objects)
  Sieve-in→presheaf s .F₁ f hx = s .closed hx f
  Sieve-in→presheaf s .F-id = prop!
  Sieve-in→presheaf s .F-∘ _ _ = prop!

  Sieve-in→subterminal
    : ∀ {S : Sieve-in C} → is-subterminal (PSh lzero C) (Sieve-in→presheaf S)
  Sieve-in→subterminal {S} = prop→is-subterminal-PSh _ C (Sieve-in→presheaf S)
```
