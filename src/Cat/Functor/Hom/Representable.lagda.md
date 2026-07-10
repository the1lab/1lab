<!--
```agda
open import Cat.Univalent.Instances.Opposite
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Limit.Base
open import Cat.Functor.Hom.Yoneda
open import Cat.Functor.Properties
open import Cat.Instances.Elements
open import Cat.Instances.Functor
open import Cat.Diagram.Terminal
open import Cat.Functor.Constant
open import Cat.Morphism.Duality
open import Cat.Diagram.Initial
open import Cat.Instances.Sets
open import Cat.Functor.Hom
open import Cat.Duality
open import Cat.Prelude

import Cat.Instances.Elements.Covariant as Co
import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Functor.Hom.Representable where
```

# Representable functors

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  private
    module C = Cat.Reasoning C
    open Functor
```
-->

:::{.definition #representing-object}
Let $F : \cC\op \to \Sets_\kappa$ be a presheaf. An object $r : \cC$ is
a **representing object** of a section $s : F(r)$ if

```agda
  record is-representation
    {κ} (F : Functor (C ^op) (Sets κ))
    (rep : C.Ob)
    (section : F ʻ rep)
    : Type (o ⊔ ℓ ⊔ κ) where
    no-eta-equality
```

- For every other object $x : \cC$ and section $s' : F(x)$, there exists
  map $u_{s'} : \cC(x, r)$ such that $s'$ is a restriction of $s$ along $u$.

```agda
    field
      universal : ∀ {x} → F ʻ x → C.Hom x rep
      factors : ∀ {x} (s : F ʻ x) → F ⟪ universal s ⟫ section ≡ s
```

- The map $u_{s'}$ is the unique such map.

```agda
    field
      unique
        : ∀ {x} (s : F ʻ x)
        → (other : C.Hom x rep)
        → F ⟪ other ⟫ section ≡ s
        → universal s ≡ other
```
:::

<!--
```agda
    universal-η : ∀ {x} (f : C.Hom x rep) → universal (F ⟪ f ⟫ section) ≡ f
    universal-η f = unique (F ⟪ f ⟫ section) f refl

    universal-∘
      : ∀ {x y} (f : C.Hom x y) (s : F ʻ y)
      → F ⟪ universal s C.∘ f ⟫ section ≡ F ⟪ f ⟫ s
    universal-∘ f s = (F .F-∘ f (universal s) ·ₚ section) ∙ ap (F ⟪ f ⟫_) (factors s)

    universal-natural
      : ∀ {x y} (s : F ʻ y) (f : C.Hom x y)
      → universal s C.∘ f ≡ universal (F ⟪ f ⟫ s)
    universal-natural s f = sym (unique (F ⟪ f ⟫ s) (universal s C.∘ f) (universal-∘ f s))

    universal-inj
      : ∀ {x} {s s' : F ʻ x}
      → universal s ≡ universal s'
      → s ≡ s'
    universal-inj {s = s} {s' = s'} p = sym (factors s) ∙∙ ap (F ⟪_⟫ section) p ∙∙ factors s'

    unique₂
      : ∀ {x}
      → (f g : C.Hom x rep)
      → F ⟪ f ⟫ section ≡ F ⟪ g ⟫ section
      → f ≡ g
    unique₂ f g p = sym (universal-η f) ∙∙ ap universal p ∙∙ universal-η g

    unique-endo
      : ∀ (f : C.Hom rep rep)
      → F ⟪ f ⟫ section ≡ section
      → f ≡ C.id
    unique-endo f p = unique₂ f C.id (p ∙ sym (F .F-id ·ₚ section))
```
-->

:::{.definition #representable-functor}
A **representation** for a functor is a choice of a representing object.
:::

```agda
  record Representation {κ} (F : Functor (C ^op) (Sets κ)) : Type (o ⊔ ℓ ⊔ κ) where
    no-eta-equality
    field
      rep : C.Ob
      section : F ʻ rep
      has-is-rep : is-representation F rep section

    open is-representation has-is-rep public
```

<!--
```agda
{-# INLINE is-representation.constructor #-}
{-# INLINE Representation.constructor #-}

module _ {o ℓ κ} {C : Precategory o ℓ} {F : Functor (C ^op) (Sets κ)} where
  private
    module C = Cat.Reasoning C
    module F = Functor F

  is-representation-is-prop
    : ∀ {rep} {section}
    → is-prop (is-representation F rep section)
  is-representation-is-prop {rep} {section} is-rep is-rep' = path where
    open is-representation

    universal-path : ∀ {x} (s : F ʻ x) → is-rep .universal s ≡ is-rep' .universal s
    universal-path s = is-rep .unique s (is-rep' .universal s) (is-rep' .factors s)

    path : is-rep ≡ is-rep'
    path i .universal s = universal-path s i
    path i .factors {x} s =
      is-prop→pathp (λ i → F.₀ x .is-tr (F ⟪ universal-path s i ⟫ section) s)
        (is-rep .factors s)
        (is-rep' .factors s) i
    path i .unique s other p =
      is-prop→pathp (λ i → C.Hom-set _ _ (universal-path s i) other)
        (is-rep .unique s other p)
        (is-rep' .unique s other p) i

  instance
    H-Level-is-representation
      : ∀ {rep} {section} {n}
      → H-Level (is-representation F rep section) (suc n)
    H-Level-is-representation = prop-instance is-representation-is-prop

  private unquoteDecl representation-Σ-iso = declare-record-iso representation-Σ-iso (quote Representation)

  Representation≃is-representation
    : Representation F
    ≃ (Σ[ rep ∈ C.Ob ] Σ[ section ∈ F ʻ rep ] is-representation F rep section)
  Representation≃is-representation = Iso→Equiv representation-Σ-iso

  instance
    Extensional-Representation
      : ∀ {ℓr}
      → ⦃ _ : Extensional (Σ[ rep ∈ C.Ob ] F ʻ rep) ℓr ⦄
      → Extensional (Representation F) ℓr
    Extensional-Representation ⦃ e ⦄ =
      embedding→extensional
        (Equiv→Embedding (Representation≃is-representation ∙e Σ-assoc)
        ∙emb ((fst , Subset-proj-embedding λ _ → hlevel 1)))
        e
```
-->

This definition is _deceptively_ simple: the idea of representable
functor (and of representing object) is _key_ to understanding the idea
of **universal property**, which could be called the most important
concept in category theory. Most constructions in category theory
specified in terms of the existence of certain maps are really instances
of representing objects for functors: [[limits]], [[colimits]], [[coends]],
[[adjoint functors]], [[Kan extensions]], etc.

## Universal properties

The first thing we will observe is that an object $r : \cC$ is a representation
of $s : F(r)$ if and only if the map $F(-)(s) : \cC(x, r) \to F(x)$ is an
[[equivalence]] for every $x : \cC$.

```agda
  yo-is-equiv→is-representation
    : ∀ {rep} {section}
    → (∀ x → is-equiv λ (f : C.Hom x rep) → F ⟪ f ⟫ section)
    → is-representation F rep section

  is-representation→yo-is-equiv
    : ∀ {rep} {section}
    → is-representation F rep section
    → ∀ x → is-equiv λ (f : C.Hom x rep) → F ⟪ f ⟫ section
```

This is follows essentially by definition.

```agda
  {-# INLINE yo-is-equiv→is-representation #-}
  yo-is-equiv→is-representation {rep} {section} yo-equiv = record
    { universal = rep.from
    ; factors = rep.ε
    ; unique = λ s other p → sym (rep.adjunctl p)
    }
    where module rep {x} = Equiv (_ , yo-equiv x)

  is-representation→yo-is-equiv {rep} {section} is-rep x = is-iso→is-equiv λ where
      .is-iso.from → rep.universal
      .is-iso.rinv → rep.factors
      .is-iso.linv → rep.universal-η
    where module rep = is-representation is-rep
```

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} {F : Functor (C ^op) (Sets ℓ)} where
  private
    module C^ = Cat.Reasoning (Cat[ C ^op , Sets ℓ ])
    module C = Cat.Reasoning C
    module F = Functor F
    open _=>_
```
-->

If $F : \cC\op \to \Sets_{\kappa}$ and $\cC$ is locally $\kappa$-small,
then we can sharpen our previous result by observing that the map
$F(-)(s) : \cC(x, r) \to F(x)$ is the action of the natural transformation
$\operatorname{yo} s$ obtained via the [[Yoneda lemma]].

```agda
  yo-invertible→is-representation
    : ∀ {rep} {section}
    → is-invertibleⁿ (yo F section)
    → is-representation F rep section

  is-representation→yo-invertible
    : ∀ {rep} {section}
    → is-representation F rep section
    → is-invertibleⁿ (yo F section)
```

To see why, note that $\operatorname{yo} s$ is invertible if and only if it is a
levelwise equivalence, as natural transformations are invertible if and only
if they are levelwise invertible, and invertible maps in $\Sets$ are equivalences.

```agda
  {-# INLINE yo-invertible→is-representation #-}
  yo-invertible→is-representation {rep} {section} yo-inv =
    yo-is-equiv→is-representation λ x →
      is-invertible→is-equiv
      $ is-invertibleⁿ→is-invertible yo-inv x

  is-representation→yo-invertible {rep} {section} is-rep =
    invertible→invertibleⁿ (yo F section) λ x →
      is-equiv→is-invertible (is-representation→yo-is-equiv is-rep x)
```

Finally, we can extend this idea to obtain an equivalence between
representations and natural isomorphisms $\cC(-,r) \iso F$.

```agda
  isoⁿ→representation
    : ∀ {rep}
    → Hom-into C rep ≅ⁿ F
    → Representation F

  representation→isoⁿ
    : (R : Representation F)
    → Hom-into C (Representation.rep R) ≅ⁿ F

  representation≃isoⁿ
    : Representation F ≃ (Σ[ rep ∈ C.Ob ] (Hom-into C rep ≅ⁿ F))
```

The reverse direction is the easiest, so we will knock that out first.
We've already shown that $\operatorname{yo} s : \cC(-,r) \to F$ must be invertible if
$r$ is a representing object of $s$, so clearly $\cC(-,r) \iso F$ if we have a
representation for $F$.

```agda
  representation→isoⁿ R =
    is-invertibleⁿ→isoⁿ
    $ is-representation→yo-invertible (Representation.has-is-rep R)
```

For the forward direction, suppose that we have a natural isomorphism
$\cC(-,r) \iso F$. By the [[Yoneda lemma]], we know that maps $\cC(-,r) \to \iso F$
are given by sections $F(r)$. Moreover, if the map is invertible, then the section
is universal.

```agda
  {-# INLINE isoⁿ→representation #-}
  isoⁿ→representation {rep} α = record
    { rep = rep
    ; section = unyo F (C^.to α)
    ; has-is-rep =
      yo-is-equiv→is-representation λ x →
        right-inverse→equiv (rinv x) (α.inverse x .snd)
    }
    where
      module α x = Equiv (natural-iso→equiv α x)

      abstract
        rinv : ∀ x f → α.from x (F ⟪ f ⟫ α.to rep C.id) ≡ f
        rinv x f =
          α.from x (F ⟪ f ⟫ α.to rep C.id) ≡⟨ C^.from α .is-natural _ _ _ ·ₚ _ ⟩
          α.from rep (α.to rep C.id) C.∘ f ≡⟨ C.eliml (α.η rep C.id) ⟩
          f                                ∎
```

This gives rise to an equivalence between representations and natural
isomorphisms $\cC(-,r) \iso F$.

```agda
  representation≃isoⁿ .fst R .fst = Representation.rep R
  representation≃isoⁿ .fst R .snd = representation→isoⁿ R
  representation≃isoⁿ .snd = is-iso→is-equiv (iso (isoⁿ→representation ⊙ snd) invr invl) where
    invl : (R : Representation F) → isoⁿ→representation (representation→isoⁿ R) ≡ R
    invl R = ext (refl ,ₚ F.F-id ·ₚ _)

    invr
      : (α : Σ[ rep ∈ C.Ob ] (Hom-into C rep ≅ⁿ F))
      → (α .fst , representation→isoⁿ (isoⁿ→representation (α .snd))) ≡ α
    invr (rep , α) = refl ,ₚ ext λ f s →
      F ⟪ s ⟫ C^.to α .η rep C.id ≡˘⟨ C^.to α .is-natural _ _ _ ·ₚ _ ⟩
      C^.to α .η f (C.id C.∘ s)   ≡⟨ ap (C^.to α .η f) (C.idl s) ⟩
      C^.to α .η f s              ∎
```

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  private
    module C = Cat.Reasoning C
```
-->

In particular, this means that every hom functor $\cC(-,x)$ must
be representable.

```agda
  Hom-into-is-representation
    : (x : C.Ob)
    → is-representation (Hom-into C x) x C.id
  Hom-into-is-representation x =
    yo-is-equiv→is-representation λ y → C.id-postcomp-is-equiv
```

## Uniqueness

<!--
```agda
module _ {o ℓ κ} {C : Precategory o ℓ} {F : Functor (C ^op) (Sets κ)} where
  private
    module C = Cat.Reasoning C
    module F = Functor F

  open Representation using (rep; section; has-is-rep)
  open is-representation
```
-->

The first thing we will observe is an immediate consequence of the
[Yoneda lemma]: representing objects are unique. Intuitively this is
because $X$ is a representation of $F$" determines how $X$ reacts to
being mapped into, and since the only thing we can probe objects in an
arbitrary category by are morphisms, two objects which react to
morphisms in the same way must be isomorphic.

[Yoneda lemma]: Cat.Functor.Hom.html

```agda
  abstract
    is-representation→section-of
      : ∀ {r r'} {s} {s'}
      → (rep : is-representation F r s)
      → (rep' : is-representation F r' s')
      → rep .universal s' C.section-of rep' .universal s
    is-representation→section-of {s = s} {s' = s'} rep rep' = unique-endo rep' _ $
      F ⟪ rep' .universal s C.∘ rep .universal s' ⟫ s'     ≡⟨ F.F-∘ _ _ ·ₚ s' ⟩
      F ⟪ rep .universal s' ⟫ (F ⟪ rep' .universal s ⟫ s') ≡⟨ ap (F ⟪ rep .universal s' ⟫_) (rep' .factors s) ⟩
      F ⟪ rep .universal s' ⟫ s                            ≡⟨ rep .factors s' ⟩
      s'                                                   ∎

  is-representation→invertible
    : ∀ {r r'} {s} {s'}
    → (rep : is-representation F r s)
    → (rep' : is-representation F r' s')
    → C.is-invertible (rep' .universal s)
  is-representation→invertible {s = s} {s' = s'} rep rep' =
    C.make-invertible
      (rep .universal s')
      (is-representation→section-of rep rep')
      (is-representation→section-of rep' rep)

  representation-iso
    : (X Y : Representation F)
    → X .rep C.≅ Y .rep
  representation-iso X Y =
    C.invertible→iso _ (is-representation→invertible (X .has-is-rep) (Y .has-is-rep))
```

Therefore, if $\cC$ is a [[univalent category]], then the type of
representations for a functor $F$ is a [[proposition]]. This does not follow
immediately from the lemma above: we also need to show that the
isomorphism we just defined lifts to a path between the sections of the
two representations. The gist of the argument is that there is a `PathP`{.Agda}
linking the above isomorphism and the identity isomorphism, so we can
use functoriality of $F$ and the factorisation of sections to obtain
our desired path. Unfortunately, everything in sight is wildly heterogeneous,
so this argument is obfuscated behind some cube manipulations.

```agda
  Representation-is-prop : is-category C → is-prop (Representation F)
  Representation-is-prop c-cat X Y = ext (rep-path ,ₚ section-pathp) where
    module X = Representation X
    module Y = Representation Y

    rep-path : X.rep ≡ Y.rep
    rep-path = c-cat .to-path (representation-iso X Y)

    rep-path-over : PathP (λ i → X.rep C.≅ rep-path i) C.id-iso (representation-iso X Y)
    rep-path-over = c-cat .to-path-over (representation-iso X Y)

    section-pathp : PathP (λ i → F ʻ rep-path i) X.section Y.section
    section-pathp i = comp (λ j → F ʻ rep-path (i ∧ j)) (∂ i) λ where
      j (i = i0) → Y.factors X.section j
      j (i = i1) → F.F-id j (coe1→i (λ i → F ʻ rep-path i) j Y.section)
      j (j = i0) → F ⟪ C.to (rep-path-over (~ i)) ⟫ coe1→i (λ i → F ʻ rep-path i) (~ i) Y.section
```

## As terminal objects

<!--
```agda
module _ {o ℓ κ} {C : Precategory o ℓ} {F : Functor (C ^op) (Sets κ)} where
  private
    module C = Cat.Reasoning C
    module F = Functor F
    open Element-hom
```
-->

We begin to connect the idea of representing objects to other universal
constructions by proving this alternative characterisation of
representations: A functor $F$ is representable if, and only if, its
[[category of elements]] $\int F$ has a [[terminal object]].

```agda
  is-terminal-element→is-representation
    : ∀ {rep} {section}
    → is-terminal (∫ C F) (rep , section)
    → is-representation F rep section
```

The proof basically amounts to currying.

```agda
  {-# INLINE is-terminal-element→is-representation #-}
  is-terminal-element→is-representation {rep} {section} rep-term = record
    { universal = λ {x} fx → rep.! {elem x fx} .hom
    ; factors = λ {x} fx → rep.! {elem x fx} .commute
    ; unique = λ {x} fx h p → ap hom (rep.!-unique (elem-hom h p))
    }
    where
      module rep = is-terminal (∫ C F) rep-term
```

In the other direction, we take the terminal element to be the image of the
identity on the representing object.

```agda
  is-representation→is-terminal-element
    : ∀ {rep} {section}
    → is-representation F rep section
    → is-terminal (∫ C F) (rep , section)
  is-representation→is-terminal-element {rep} {section} is-rep (x , fx) =
    contr (elem-hom (rep.universal fx) (rep.factors fx)) λ h →
      ext (rep.unique fx (h .hom) (h .commute))
    where
      module rep = is-representation is-rep
```

<!--
```agda
  terminal-element→representation
    : Terminal (∫ C F)
    → Representation F
  {-# INLINE terminal-element→representation #-}
  terminal-element→representation term = record
    { rep = top .fst
    ; section = top .snd
    ; has-is-rep = is-terminal-element→is-representation has⊤
    }
    where open Terminal term

  representation→terminal-element
    : Representation F
    → Terminal (∫ C F)
  representation→terminal-element F-rep = record
    { top = elem rep section
    ; has⊤ = is-representation→is-terminal-element has-is-rep
    }
    where open Representation F-rep
```
-->

## Corepresentable functors

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  private
    module C = Cat.Reasoning C
    open Functor
```
-->

:::{.definition #corepresentable-functor}
As noted earlier, we can dualise the definition of a representable
functor to the covariant setting to get **corepresentable** functors.


```agda
  record is-corepresentation
    {κ} (F : Functor C (Sets κ))
    (corep : C.Ob)
    (section : F ʻ corep)
    : Type (o ⊔ ℓ ⊔ κ) where
    no-eta-equality
    field
      universal : ∀ {x} → F ʻ x → C.Hom corep x
      factors : ∀ {x} (s : F ʻ x) → F ⟪ universal s ⟫ section ≡ s
      unique
        : ∀ {x} (s : F ʻ x)
        → (other : C.Hom corep x)
        → F ⟪ other ⟫ section ≡ s
        → universal s ≡ other
```
:::

<!--
```agda
    abstract
      universal-η : ∀ {x} (f : C.Hom corep x) → universal (F ⟪ f ⟫ section) ≡ f
      universal-η f = (unique (F ⟪ f ⟫ section) f refl)

      universal-∘
        : ∀ {x y} (f : C.Hom x y) (s : F ʻ x)
        → F ⟪ f C.∘ universal s ⟫ section ≡ F ⟪ f ⟫ s
      universal-∘ f s = F .F-∘ f (universal s) ·ₚ section ∙ ap (F ⟪ f ⟫_) (factors s)

      universal-inj
        : ∀ {x} {s s' : F ʻ x}
        → universal s ≡ universal s'
        → s ≡ s'
      universal-inj {s = s} {s' = s'} p = sym (factors s) ∙∙ ap (F ⟪_⟫ section) p ∙∙ factors s'

      unique₂
        : ∀ {x}
        → (f g : C.Hom corep x)
        → F ⟪ f ⟫ section ≡ F ⟪ g ⟫ section
        → f ≡ g
      unique₂ f g p = sym (universal-η f) ∙∙ ap universal p ∙∙ universal-η g

      unique-endo
        : ∀ (f : C.Hom corep corep)
        → F ⟪ f ⟫ section ≡ section
        → f ≡ C.id
      unique-endo f p = unique₂ f C.id (p ∙ sym (F .F-id ·ₚ section))
```
-->

```agda
  record Corepresentation {κ} (F : Functor C (Sets κ)) : Type (o ⊔ ℓ ⊔ κ) where
    no-eta-equality
    field
      corep : C.Ob
      section : F ʻ corep
      has-is-corep : is-corepresentation F corep section

    open is-corepresentation has-is-corep public
```

<!--
```agda
{-# INLINE is-corepresentation.constructor #-}
{-# INLINE Corepresentation.constructor #-}

module _ {o ℓ κ} {C : Precategory o ℓ} {F : Functor C (Sets κ)} where
  private
    module C = Cat.Reasoning C
    module F = Functor F

  is-corepresentation-is-prop
    : ∀ {rep} {section}
    → is-prop (is-corepresentation F rep section)
  is-corepresentation-is-prop {rep} {section} is-rep is-rep' = path where
    open is-corepresentation

    universal-path : ∀ {x} (s : F ʻ x) → is-rep .universal s ≡ is-rep' .universal s
    universal-path s = is-rep .unique s (is-rep' .universal s) (is-rep' .factors s)

    path : is-rep ≡ is-rep'
    path i .universal s = universal-path s i
    path i .factors {x} s =
      is-prop→pathp (λ i → F.₀ x .is-tr (F ⟪ universal-path s i ⟫ section) s)
        (is-rep .factors s)
        (is-rep' .factors s) i
    path i .unique s other p =
      is-prop→pathp (λ i → C.Hom-set _ _ (universal-path s i) other)
        (is-rep .unique s other p)
        (is-rep' .unique s other p) i

  instance
    H-Level-is-corepresentation
      : ∀ {rep} {section} {n}
      → H-Level (is-corepresentation F rep section) (suc n)
    H-Level-is-corepresentation = prop-instance is-corepresentation-is-prop

  private unquoteDecl corepresentation-Σ-iso = declare-record-iso corepresentation-Σ-iso (quote Corepresentation)

  Corepresentation≃is-corepresentation
    : Corepresentation F
    ≃ (Σ[ rep ∈ C.Ob ] Σ[ section ∈ F ʻ rep ] is-corepresentation F rep section)
  Corepresentation≃is-corepresentation = Iso→Equiv corepresentation-Σ-iso

  instance
    Extensional-Corepresentation
      : ∀ {ℓr}
      → ⦃ _ : Extensional (Σ[ rep ∈ C.Ob ] F ʻ rep) ℓr ⦄
      → Extensional (Corepresentation F) ℓr
    Extensional-Corepresentation ⦃ e ⦄ =
      embedding→extensional
        (Equiv→Embedding (Corepresentation≃is-corepresentation ∙e Σ-assoc)
        ∙emb ((fst , Subset-proj-embedding λ _ → hlevel 1)))
        e
```
-->

## Duality

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  private
    module C = Cat.Reasoning C
    open Functor
```
-->

Corepresentations of a functor $F : \cC \to \Sets_{\kappa}$ are dual
to representations of $F$ viewed as a functor ${\cC\op}\op \to \Sets_{\kappa}$.

```agda
  is-co-representation→is-corepresentation
    : ∀ {κ} {F : Functor C (Sets κ)} {corep} {section}
    → is-representation {C = C ^op} (F F∘ ^op^op→) corep section
    → is-corepresentation F corep section

  is-corepresentation→is-co-representation
    : ∀ {κ} {F : Functor C (Sets κ)} {corep} {section}
    → is-corepresentation F corep section
    → is-representation (F F∘ ^op^op→) corep section

  Corepresentation→Co-representation
    : ∀ {κ} {F : Functor C (Sets κ)}
    → Corepresentation F
    → Representation (F F∘ ^op^op→)

  Co-representation→Corepresentation
    : ∀ {κ} {F : Functor C (Sets κ)}
    → Representation (F F∘ ^op^op→)
    → Corepresentation F

  Corepresentation≃Co-representation
    : ∀ {κ} {F : Functor C (Sets κ)}
    → Corepresentation F
    ≃ Representation (F F∘ ^op^op→)
```

<details>
<summary> The proof is almost entirely duality shuffling, so we omit
the details.
</summary>

```agda
  {-# INLINE is-co-representation→is-corepresentation #-}
  is-co-representation→is-corepresentation is-co-rep = record
    { universal = universal
    ; factors = factors
    ; unique = unique
    }
    where open is-representation is-co-rep

  {-# INLINE is-corepresentation→is-co-representation #-}
  is-corepresentation→is-co-representation is-corep = record
    { universal = universal
    ; factors = factors
    ; unique = unique
    }
    where open is-corepresentation is-corep

  {-# INLINE Co-representation→Corepresentation #-}
  Co-representation→Corepresentation R = record
    { corep = rep
    ; section = section
    ; has-is-corep = is-co-representation→is-corepresentation has-is-rep
    }
    where open Representation R

  {-# INLINE Corepresentation→Co-representation #-}
  Corepresentation→Co-representation R = record
    { rep = corep
    ; section = section
    ; has-is-rep = is-corepresentation→is-co-representation has-is-corep
    }
    where open Corepresentation R

  Corepresentation≃Co-representation .fst = Corepresentation→Co-representation
  Corepresentation≃Co-representation .snd =
    is-iso→is-equiv $ iso Co-representation→Corepresentation
      (λ R → ext refl)
      (λ R → ext refl)
```

</details>

## Universal properties

<!--
```agda
module _ {o ℓ κ} {C : Precategory o ℓ} {F : Functor C (Sets κ)} where
  private
    module C = Cat.Reasoning C
    module F = Functor F
```
-->

Like representables, an object $r : \cC$ is a corepresentation of a
section $s : F(r)$ if and only if the map $F(-)(s) : \cC(r,x) \to F(x)$
is an equivalence for all $x : \cC$.

```agda
  yo-is-equiv→is-corepresentation
    : ∀ {corep} {section}
    → (∀ x → is-equiv λ (f : C.Hom corep x) → F ⟪ f ⟫ section)
    → is-corepresentation F corep section

  is-corepresentation→yo-is-equiv
    : ∀ {corep} {section}
    → is-corepresentation F corep section
    → (∀ x → is-equiv λ (f : C.Hom corep x) → F ⟪ f ⟫ section)
```

<details>
<summary>This follows immediately from duality, so we omit the details.
</summary>

```agda
  {-# INLINE yo-is-equiv→is-corepresentation #-}
  yo-is-equiv→is-corepresentation yo-equiv =
    is-co-representation→is-corepresentation
    $ yo-is-equiv→is-representation
    $ yo-equiv

  is-corepresentation→yo-is-equiv is-corep =
    is-representation→yo-is-equiv
    $ is-corepresentation→is-co-representation
    $ is-corep
```

</details>

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  private
    module C = Cat.Reasoning C

  open is-corepresentation
```
-->

This means that the hom functors $\cC(x,-)$ are all corepresentable.

```agda
  Hom-from-is-corepresentation
    : (x : C.Ob)
    → is-corepresentation (Hom-from C x) x C.id
  Hom-from-is-corepresentation x =
    yo-is-equiv→is-corepresentation λ x → C.id-precomp-is-equiv
```

## Uniqueness

<!--
```agda
module _ {o ℓ κ} {C : Precategory o ℓ} {F : Functor C (Sets κ)} where
  private
    module C = Cat.Reasoning C
    module F = Functor F

  open Corepresentation using (corep; section; has-is-corep)
  open is-corepresentation
```
-->

If $r, r' : \cC$ are corepresentations of $s : F(r)$ and $s' : F(r')$,
then $r \iso r'$.

```agda
  abstract
    is-corepresentation→retract-of
      : ∀ {r r'} {s} {s'}
      → (corep : is-corepresentation F r s)
      → (corep' : is-corepresentation F r' s')
      → corep .universal s' C.retract-of corep' .universal s
    is-corepresentation→retract-of corep corep' =
      is-representation→section-of
        (is-corepresentation→is-co-representation corep)
        (is-corepresentation→is-co-representation corep')

    is-corepresentation→invertible
      : ∀ {r r'} {s} {s'}
      → (rep : is-corepresentation F r s)
      → (rep' : is-corepresentation F r' s')
      → C.is-invertible (rep .universal s')
    is-corepresentation→invertible {s = s} {s' = s'} rep rep' =
      C.make-invertible
        (rep' .universal s)
        (is-corepresentation→retract-of rep rep')
        (is-corepresentation→retract-of rep' rep)

    corepresentation-iso
      : (X Y : Corepresentation F)
      → X .corep C.≅ Y .corep
    corepresentation-iso X Y =
      C.invertible→iso _
      $ is-corepresentation→invertible (X .has-is-corep) (Y .has-is-corep)
```

This implies that the type of corepresentations is a proposition when
$\cC$ is univalent.

```agda
  Corepresentation-is-prop : is-category C → is-prop (Corepresentation F)
```

The flip in variance ends up making a direct proof *much* more difficult
than the previous case. Luckily, we can appeal to duality.

```agda
  Corepresentation-is-prop c-cat =
    Equiv→is-hlevel 1 Corepresentation≃Co-representation
    $ Representation-is-prop
    $ opposite-is-category c-cat
```

## As initial objects

<!--
```agda
module _ {o ℓ κ} {C : Precategory o ℓ} {F : Functor C (Sets κ)} where
  private
    module C = Cat.Reasoning C
    module F = Functor F
    open Co.Element-hom
```
-->

Dualising [the representable case](#as-terminal-objects), we have that a functor is
corepresentable if and only if its [[covariant category of elements]] has an
[[initial object]].

```agda
  is-initial-element→is-corepresentation
    : ∀ {corep} {section}
    → is-initial (Co.∫ F) (corep , section)
    → is-corepresentation F corep section

  is-corepresentation→is-initial-element
    : ∀ {corep} {section}
    → is-corepresentation F corep section
    → is-initial (Co.∫ F) (corep , section)
```

<details>
<summary>The proofs are again entirely analogous to the representable case.
</summary>

```agda
  {-# INLINE is-initial-element→is-corepresentation #-}
  is-initial-element→is-corepresentation {corep} {section} rep-is-init = record
    { universal = λ {x} fx → corep.¡ {elem x fx} .hom
    ; factors = λ {x} fx → corep.¡ {elem x fx} .commute
    ; unique = λ {x} fx h p → ap hom (corep.¡-unique (Co.elem-hom h p))
    }
    where module corep = is-initial (Co.∫ F) rep-is-init

  is-corepresentation→is-initial-element {corep} {section} is-corep (x , fx) =
    contr (Co.elem-hom (corep.universal fx) (corep.factors fx)) λ h →
      ext (corep.unique fx (h .hom) (h .commute))
    where module corep = is-corepresentation is-corep
```

</details>

<!--
```agda
  initial-element→corepresentation
    : Initial (Co.∫ F)
    → Corepresentation F
  {-# INLINE initial-element→corepresentation #-}
  initial-element→corepresentation init = record
    { corep = bot .fst
    ; section = bot .snd
    ; has-is-corep = is-initial-element→is-corepresentation has⊥
    }
    where open Initial init

  corepresentation→initial-element
    : Corepresentation F
    → Initial (Co.∫ F)
  {-# INLINE corepresentation→initial-element #-}
  corepresentation→initial-element R = record
    { bot = corep , section
    ; has⊥ = is-corepresentation→is-initial-element has-is-corep
    }
    where open Corepresentation R
```
-->

## Corepresentable functors preserve limits

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  module C = Cat.Reasoning C
  open Functor
  open _=>_
```
-->

Every corepresentable functor [[preserves limits]].

```agda
  is-corepresentation→preserves-limits
    : ∀ {κ oj ℓj} {F : Functor C (Sets κ)} {corep} {section}
    → is-corepresentation F corep section
    → is-continuous oj ℓj F
```

To start, suppose that $\psi_{j} : \cC(L, D(j))$ is the limit of a diagram
$D : \cJ \to \cC$; our goal is to show that $F(\psi_{j}) : F(L) \to F(D(j))$
is a limit in $\Sets$.

To that end, let $\xi_{j} : F(X) \to F(D(j))$ be an $F \circ D$ cone in $\Sets$.
The key observation is that every section $x : F(X)$ gives rise to a cone
$u_{\xi_{j}(x)} : \cC(R, D(j))$ in $\cC$ whose legs are formed by the
universal map associated to $\xi_{j}(x) : F(D(j))$. This in turn gives
us a suitably unique map $\langle u_{\xi_{j}(x)} \rangle : \cC(R, L)$, as
$L$ is a limit of $D(j)$. We can then drop back down to $\Sets$, and apply
our newly constructed map $\langle u_{\xi_{j}(x)} \rangle : \cC(R, L)$
to the universal section $r : F(R)$ to get an element of $F(L)$.

```agda
  is-corepresentation→preserves-limits {F = F} {section = section} is-corep {J = J} {Diagram = Dia} {K} lim =
    to-is-limitp ml refl where

    module J = Precategory J
    module F = Cat.Functor.Reasoning F
    module Dia = Functor Dia
    module lim = is-limit lim
    module corep = is-corepresentation is-corep
    open make-is-limit

    ml : make-is-limit (F F∘ Dia) (F · (K · tt))
    ml .ψ j x = F ⟪ lim.ψ j ⟫ x
    ml .commutes {i} {j} f = ext λ x → F.collapse (lim.commutes f) ·ₚ x
    ml .universal {X} ξ p x =
      F ⟪ lim.universal (λ j → corep.universal (ξ j x)) (λ f → sym $ corep.unique _ _ (comm f)) ⟫ section
      where abstract
        comm
          : ∀ {x i j} (f : J.Hom i j)
          → F ⟪ Dia.₁ f C.∘ corep.universal (ξ i x) ⟫ section ≡ ξ j x
        comm {x} {i} {j} f =
          F ⟪ Dia.₁ f C.∘ corep.universal (ξ i x) ⟫ section ≡⟨ corep.universal-∘ (Dia.₁ f) (ξ i x) ⟩
          F.F₁ (Dia.₁ f) (ξ i x)                            ≡⟨ p f ·ₚ x ⟩
          ξ j x                                             ∎
```

<details>
<summary>All that remains is to prove that the map $F(X) \to F(L)$ we
just constructed factors through $\xi$ and is suitably unique. This
essentially *has* to be the case, as it was constructed only using
universal properties. Nevertheless, the proof amounts to some unenlightening
algebra, so we elide the details.

</summary>

```agda
    ml .factors ξ p = ext λ x →
      F ⟪ lim.ψ _ ⟫ (F ⟪ lim.universal (λ j → corep.universal (ξ j x)) _ ⟫ section) ≡˘⟨ F.F-∘ _ _ ·ₚ _ ⟩
      (F ⟪ lim.ψ _ C.∘ lim.universal (λ j → corep.universal (ξ j x)) _ ⟫ section)   ≡⟨ ap (F ⟪_⟫ section) (lim.factors _ _) ⟩
      F ⟪ corep.universal (ξ _ x) ⟫ section                                         ≡⟨ corep.factors _ ⟩
      ξ _ x ∎
    ml .unique ξ p other q = ext λ x →
      corep.universal-inj $ corep.unique _ _ $ ap (F ⟪_⟫ section) $ sym $ lim.unique _ _ _ λ j →
        sym $ corep.unique _ _ $
          F ⟪ lim.ψ j C.∘ corep.universal (other x) ⟫ section ≡⟨ corep.universal-∘ (lim.ψ j) (other x) ⟩
          F ⟪ lim.ψ j ⟫ other x                               ≡⟨ q j ·ₚ x ⟩
          ξ j x                                               ∎
```

</details>

As a corollary, we get that the hom functor $\cC(c,-) : \cC \to \Sets$
preserves limits.

```agda
  Hom-from-preserves-limits
    : ∀ {oj ℓj}
    → (c : C.Ob)
    → is-continuous oj ℓj (Hom-from C c)
  Hom-from-preserves-limits c =
    is-corepresentation→preserves-limits
    $ Hom-from-is-corepresentation c
```
We can show a similar fact for representable functors, but with a twist:
they **reverse** colimits! This is due to the fact that a representable
functor $F : \cC\op \to \Sets$ is contravariant. Specifically, $F$ will
take limits in $\cC\op$ to limits in $\Sets$, but limits in $\cC\op$
are colimits, so $F$ will take colimits in $\cC$ to limits in $\Sets$.

A less formal perspective on this is that the collection of maps
out of a colimit is still defined as a limit in $\Sets$. For instance,
to give a $a + b \to x$ out of a coproduct, we are required to give
a pair of maps $a \to x$ and $b \to x$.

```agda
  is-representation→reverses-colimits
    : ∀ {κ oj ℓj} {F : Functor (C ^op) (Sets κ)} {corep} {section}
    → is-representation F corep section
    → is-cocontinuous oj ℓj (opFʳ F)
```

<details>
<summary>Luckily, the proof is essentially identical to the corepresentable case.
</summary>

```agda
  is-representation→reverses-colimits {F = F} {corep} {section} is-rep {J} {Dia} colim =
    to-is-colimitp mc refl where

    module J = Precategory J
    module F = Cat.Functor.Reasoning F
    module Dia = Functor Dia
    module colim = is-colimit colim
    module rep = is-representation is-rep
    open make-is-colimit

    mc : make-is-colimit _ _
    mc .ψ j x = F ⟪ colim.ψ j ⟫ x
    mc .commutes {i} {j} f = ext λ x → F.collapse (colim.commutes f) ·ₚ x
    mc .universal ξ p x =
      F ⟪ colim.universal (λ j → rep.universal (ξ j x)) comm ⟫ section
      where abstract
        comm
          : ∀ {x i j} (f : J.Hom i j)
          → rep.universal (ξ j x) C.∘ Dia.₁ f ≡ rep.universal (ξ i x)
        comm {x} f = sym $ rep.unique _ _ (rep.universal-∘ (Dia.₁ f) (ξ _ x) ∙ p f ·ₚ x)
    mc .factors {j} ξ p = ext λ x →
      F ⟪ colim.ψ j ⟫ (F ⟪ colim.universal (λ j → rep.universal (ξ j x)) _ ⟫ section) ≡⟨ F.collapse (colim.factors _ _) ·ₚ section ⟩
      F ⟪ rep.universal (ξ j x) ⟫ section                                             ≡⟨ rep.factors (ξ j x) ⟩
      ξ j x ∎
    mc .unique ξ p other q = ext λ x →
      rep.universal-inj $ rep.unique _ _ $ ap (F ⟪_⟫ section) $ sym $ colim.unique _ _ _ λ j →
        sym $ rep.unique _ _ $
          F ⟪ rep.universal (other x) C.∘ colim.ψ j ⟫ section ≡⟨ rep.universal-∘ _ _ ⟩
          F ⟪ colim.ψ j ⟫ other x                             ≡⟨ q j ·ₚ x ⟩
          ξ j x ∎
```
</details>

Like before, we get that the hom functor $\cC(-,c) : \cC\op \to \Sets$
reverses colimits.

```agda
  Hom-into-reverses-colimits
    : ∀ {oj ℓj}
    → (c : C.Ob)
    → is-cocontinuous oj ℓj (opFʳ (Hom-into C c))
  Hom-into-reverses-colimits c =
    is-representation→reverses-colimits
    $ Hom-into-is-representation c
```
