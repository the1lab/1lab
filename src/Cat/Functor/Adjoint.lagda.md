---
description: |
  We present two definitions of adjoint functors, one which is
  computationally convenient (units and counits), and one which is
  conceptually clean (adjoints as "optimal solutions" --- initial
  objects in certain comma categories).
---
<!--
```agda
open import Cat.Functor.Naturality
open import Cat.Diagram.Initial
open import Cat.Functor.Compose
open import Cat.Instances.Comma
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning
```
-->

```agda
module Cat.Functor.Adjoint where
```

<!--
```agda
private variable
  o h : Level
  C D E : Precategory o h

open Functor hiding (op)

adj-level : ∀ {o₁ h₁ o₂ h₂} (C : Precategory o₁ h₁) (D : Precategory o₂ h₂)
          → Level
adj-level {o₁ = o₁} {h₁} {o₂} {h₂} _ _ = o₁ ⊔ o₂ ⊔ h₁ ⊔ h₂
```
-->

# Adjoint functors

Category theory is, in general, the study of how things can be related.
For instance, structures at the level of sets (e.g. the collection of
natural numbers) are often interestingly related by propositions (i.e.
the proposition $x \le y$). Structures at the level of groupoids (e.g.
the collection of all sets) are interestingly related by sets (i.e. the
set of maps $x \to y$). Going further, we have structures at the level
of 2-groupoids, which could be given an interesting _category_ of
relations, etc.

:::{.definition #adjunction alias="left-adjoint right-adjoint adjoint-functor"}
A particularly important relationship is, of course, "sameness". Going
up the ladder of category number, we have equality at the (-1)-level,
isomorphism at the 0-level, and what's generally referred to as
"equivalence" at higher levels. It's often interesting to weaken these
relations, by making some components directed: This starts at the level
of categories, where "directing" an equivalence gives us the concept of
**adjunction**.
:::

An _equivalence of categories_ between $\cC$ and $\cD$ is given by
a pair of functors $L : \cC \leftrightarrows \cD : R$, equipped
with natural _isomorphisms_ $\eta : \Id \cong (R \circ L)$ (the
"unit") and $\eps : (L \circ R) \cong \Id$ (the "counit"). We
still want the correspondence to be bidirectional, so we can't change
the types of $R$, $L$; What we _can_ do is weaken the natural
isomorphisms to natural _transformations_. The data of an **adjunction**
starts as such:

```agda
record _⊣_ (L : Functor C D) (R : Functor D C) : Type (adj-level C D) where
  no-eta-equality
  private
    module C = Precategory C
    module D = Precategory D

  field
    unit   : Id => (R F∘ L)
    counit : (L F∘ R) => Id

  module unit = _=>_ unit
  module counit = _=>_ counit renaming (η to ε)
```

Unfortunately, the data that we have here is not particularly coherent.
The `unit`{.Agda} and `counit`{.Agda} let us introduce $R\circ L$ and
eliminate $L\circ R$ in a composition, which gives us two ways of mapping
$L \To L$. One is the identity, and the other is going through
the unit: $L \To L\circ R\circ L \To L$ (the situation
with $R$ is symmetric). We must impose further equations on the natural
transformations to make sure these match:

```agda
  field
    zig : ∀ {A} → counit.ε (F₀ L A) D.∘ F₁ L (unit.η A) ≡ D.id
    zag : ∀ {B} → F₁ R (counit.ε B) C.∘ unit.η (F₀ R B) ≡ C.id

infixr 15 _⊣_
```

These are called "triangle identities" because of the shape they have as
commutative diagrams:

<div class=mathpar>

~~~{.quiver}
\[\begin{tikzcd}
  R & RLR \\
  & R
  \arrow[from=1-1, to=2-2]
  \arrow["{\eta R}", from=1-1, to=1-2]
  \arrow["R\epsilon", from=1-2, to=2-2]
\end{tikzcd}\]
~~~

~~~{.quiver}
\[\begin{tikzcd}
  L & LRL \\
  & L
  \arrow[from=1-1, to=2-2]
  \arrow["L\eta", from=1-1, to=1-2]
  \arrow["{\epsilon L}", from=1-2, to=2-2]
\end{tikzcd}\]
~~~

</div>

# Universal morphisms {defines="universal-morphism"}

<!--
```agda
module _
  {o h o' h'}
  {C : Precategory o h}
  {D : Precategory o' h'}
  where

  private
    module C = Precategory C
    module D = Precategory D
```
-->

Another perspective on adjoint functors is given by finding "most
efficient solutions" to the "problem" posed by a functor. For instance,
the ([[fully faithful]]) inclusion of [[posets]] into [[strict
(pre)categories|strict category]] poses the problem of turning a
precategory into a poset. While this can't be done in a 1:1 way
(precategories are strictly more general than posets), we _can_ still
ponder whether there is some "most efficient" way to turn a category
into a poset.

While we can't directly consider maps from precategories to posets, we
_can_ consider maps from precategories to the inclusion of a poset; Let
us write $\cC$ for a generic precategory, $\cP$ for a generic poset, and
$U(\cP)$ for $\cP$ considered as a precategory. Any functor $\cC \to
U(\cP)$ can be seen as "a way to turn $\cC$ into a poset", but not all
of these can be the "most efficient" way. In fact, there is a vast sea
of uninteresting ways to turn a precategory into a poset: turn them all
into the [[terminal|terminal object]] poset!

A "most efficient" solution, then, would be one through which all others
factor. A "universal" way of turning a strict precategory into a poset:
A **universal morphism** from $\cC$ to $U$. The way we think about
universal morphisms (reusing the same variables) is as [initial objects]
in the [comma category] $\cC \swarrow U$, where that category is
conceptualised as being "the category of maps from $\cC$ to $U$".

[initial objects]: Cat.Diagram.Initial.html
[comma category]: Cat.Instances.Comma.html

```agda
  Universal-morphism : C.Ob → Functor D C → Type _
  Universal-morphism X R = Initial (X ↙ R)
```

If $R : \cD \to \cC$ has universal morphisms for every object of $\cC$, then
this assignment extends to a functor $L : \cC \to \cD$ with $L \dashv R$ as defined
above. Likewise, if there already exists a left adjoint $L \dashv R$, then we
can obtain a system of universal morphisms; see [here] for details.

[here]: Cat.Diagram.Free.html#free-objects-and-universal-morphisms

# Adjuncts {defines=adjuncts}

Another view on adjunctions, one which is productive when thinking about
adjoint *endo*functors $L \dashv R$, is the concept of _adjuncts_. Any
pair of natural transformations _typed like_ a unit and counit allow you
to pass between the Hom-sets $\hom(La,b)$ and $\hom(a,Rb)$, by composing
the functorial action of $L$ (resp $R$) with the natural
transformations:

<!--
```agda
module _ {L : Functor C D} {R : Functor D C} (adj : L ⊣ R) where
  private
    module L = Func L
    module R = Func R
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module adj = _⊣_ adj
```
-->

```agda
  L-adjunct : ∀ {a b} → D.Hom (L.₀ a) b → C.Hom a (R.₀ b)
  L-adjunct f = R.₁ f C.∘ adj.unit.η _

  R-adjunct : ∀ {a b} → C.Hom a (R.₀ b) → D.Hom (L.₀ a) b
  R-adjunct f = adj.counit.ε _ D.∘ L.₁ f
```

The important part that the actual data of an adjunction gets you is
these functions are inverse _equivalences_ between the hom-sets
$\hom(La,b) \cong \hom(a,Rb)$.

```agda
  L-R-adjunct : ∀ {a b} → is-right-inverse (R-adjunct {a} {b}) L-adjunct
  L-R-adjunct f =
    R.₁ (adj.counit.ε _ D.∘ L.₁ f) C.∘ adj.unit.η _        ≡⟨ R.pushl refl ⟩
    R.₁ (adj.counit.ε _) C.∘ R.₁ (L.₁ f) C.∘ adj.unit.η _  ≡˘⟨ C.refl⟩∘⟨ adj.unit.is-natural _ _ _ ⟩
    R.₁ (adj.counit.ε _) C.∘ adj.unit.η _ C.∘ f            ≡⟨ C.cancell adj.zag ⟩
    f                                                      ∎

  R-L-adjunct : ∀ {a b} → is-left-inverse (R-adjunct {a} {b}) L-adjunct
  R-L-adjunct f =
    adj.counit.ε _ D.∘ L.₁ (R.₁ f C.∘ adj.unit.η _)       ≡⟨ D.refl⟩∘⟨ L.F-∘ _ _ ⟩
    adj.counit.ε _ D.∘ L.₁ (R.₁ f) D.∘ L.₁ (adj.unit.η _) ≡⟨ D.extendl (adj.counit.is-natural _ _ _) ⟩
    f D.∘ adj.counit.ε _ D.∘ L.₁ (adj.unit.η _)           ≡⟨ D.elimr adj.zig ⟩
    f                                                     ∎

  L-adjunct-is-equiv : ∀ {a b} → is-equiv (L-adjunct {a} {b})
  L-adjunct-is-equiv = is-iso→is-equiv
    (iso R-adjunct L-R-adjunct R-L-adjunct)

  R-adjunct-is-equiv : ∀ {a b} → is-equiv (R-adjunct {a} {b})
  R-adjunct-is-equiv = is-iso→is-equiv
    (iso L-adjunct R-L-adjunct L-R-adjunct)
```

<!--
```agda
  module L-adjunct {a b} = Equiv (L-adjunct {a} {b} , L-adjunct-is-equiv)
  module R-adjunct {a b} = Equiv (R-adjunct {a} {b} , R-adjunct-is-equiv)
```
-->

Furthermore, these equivalences are natural.

```agda
  L-adjunct-naturall
    : ∀ {a b c} (f : D.Hom (L.₀ b) c) (g : C.Hom a b)
    → L-adjunct (f D.∘ L.₁ g) ≡ L-adjunct f C.∘ g
  L-adjunct-naturall f g =
    R.₁ (f D.∘ L.₁ g) C.∘ adj.unit.η _       ≡⟨ R.F-∘ _ _ C.⟩∘⟨refl ⟩
    (R.₁ f C.∘ R.₁ (L.₁ g)) C.∘ adj.unit.η _ ≡⟨ C.extendr (sym $ adj.unit.is-natural _ _ _) ⟩
    (R.₁ f C.∘ adj.unit.η _) C.∘ g           ∎

  L-adjunct-naturalr
      : ∀ {a b c} (f : D.Hom b c) (g : D.Hom (L.₀ a) b)
      → L-adjunct (f D.∘ g) ≡ R.₁ f C.∘ L-adjunct g
  L-adjunct-naturalr f g = C.pushl (R.F-∘ f g)

  L-adjunct-natural₂
      : ∀ {a b c d} (f : D.Hom a b) (g : C.Hom c d) (x : D.Hom (L.F₀ d) a)
      → L-adjunct (f D.∘ x D.∘ L.₁ g) ≡ R.₁ f C.∘ L-adjunct x C.∘ g
  L-adjunct-natural₂ f g x =
    L-adjunct-naturalr f (x D.∘ L.₁ g) ∙ ap (R.₁ f C.∘_) (L-adjunct-naturall x g)

  R-adjunct-naturall
      : ∀ {a b c} (f : C.Hom b (R.₀ c)) (g : C.Hom a b)
      → R-adjunct (f C.∘ g) ≡ R-adjunct f D.∘ L.₁ g
  R-adjunct-naturall f g = D.pushr (L.F-∘ f g)

  R-adjunct-naturalr
    : ∀ {a b c} (f : D.Hom b c) (g : C.Hom a (R.₀ b))
    → R-adjunct (R.₁ f C.∘ g) ≡ f D.∘ R-adjunct g
  R-adjunct-naturalr f g =
    adj.counit.ε _ D.∘ L.₁ (R.₁ f C.∘ g)     ≡⟨ D.refl⟩∘⟨ L.F-∘ _ _ ⟩
    adj.counit.ε _ D.∘ L.₁ (R.₁ f) D.∘ L.₁ g ≡⟨ D.extendl (adj.counit.is-natural _ _ _) ⟩
    f D.∘ (adj.counit.ε _ D.∘ L.₁ g) ∎

  R-adjunct-natural₂
    : ∀ {a b c d} (f : D.Hom a b) (g : C.Hom c d) (x : C.Hom d (R.F₀ a))
    → R-adjunct (R.₁ f C.∘ x C.∘ g) ≡ f D.∘ R-adjunct x D.∘ L.₁ g
  R-adjunct-natural₂ f g x =
    R-adjunct-naturalr f (x C.∘ g) ∙ ap (f D.∘_) (R-adjunct-naturall x g)
```

<!--
```agda
  R-adjunct-ap
    : ∀ {a b c}
    → {f : D.Hom b c} {g : C.Hom a (R.₀ b)} {h : C.Hom a (R.₀ c)}
    → R.₁ f C.∘ g ≡ h
    → f D.∘ R-adjunct g ≡ R-adjunct h
  R-adjunct-ap p = sym (R-adjunct-naturalr _ _) ∙ ap R-adjunct p

  R-adjunct-square
    : ∀ {a b c d}
    → {p1 : C.Hom a (R.₀ b)} {f : D.Hom b d} {p2 : C.Hom a (R.₀ c)} {g : D.Hom c d}
    → R.₁ f C.∘ p1 ≡ R.₁ g C.∘ p2
    → f D.∘ R-adjunct p1 ≡ g D.∘ R-adjunct p2
  R-adjunct-square sq =
    sym (R-adjunct-naturalr _ _) ·· ap R-adjunct sq ·· R-adjunct-naturalr _ _
```
-->

# Induced adjunctions

Any adjunction $L \dashv R$ induces, in a very boring way, an *opposite* adjunction
$R\op \dashv L\op$ between `opposite functors`{.Agda ident=op}:

```agda
module _ {L : Functor C D} {R : Functor D C} (adj : L ⊣ R) where
  private
    module L = Functor L
    module R = Functor R
    module adj = _⊣_ adj

  open _⊣_
  open _=>_

  opposite-adjunction : R.op ⊣ L.op
  opposite-adjunction .unit .η _ = adj.counit.ε _
  opposite-adjunction .unit .is-natural x y f = sym (adj.counit.is-natural _ _ _)
  opposite-adjunction .counit .η _ = adj.unit.η _
  opposite-adjunction .counit .is-natural x y f = sym (adj.unit.is-natural _ _ _)
  opposite-adjunction .zig = adj.zag
  opposite-adjunction .zag = adj.zig
```

As well as adjunctions $L \circ - \dashv R \circ -$ and $- \circ R \dashv - \circ L$
between [postcomposition and precomposition functors], respectively:

[postcomposition and precomposition functors]: Cat.Functor.Compose.html

```agda
  open import Cat.Functor.Coherence

  postcomposite-adjunction : postcompose L {D = E} ⊣ postcompose R
  postcomposite-adjunction .unit .η F = cohere! (adj.unit ◂ F)
  postcomposite-adjunction .unit .is-natural F G α = Nat-path λ _ → adj.unit.is-natural _ _ _
  postcomposite-adjunction .counit .η F = cohere! (adj.counit ◂ F)
  postcomposite-adjunction .counit .is-natural F G α = Nat-path λ _ → adj.counit.is-natural _ _ _
  postcomposite-adjunction .zig = Nat-path λ _ → adj.zig
  postcomposite-adjunction .zag = Nat-path λ _ → adj.zag

  precomposite-adjunction : precompose R {D = E} ⊣ precompose L
  precomposite-adjunction .unit .η F = cohere! (F ▸ adj.unit)
  precomposite-adjunction .unit .is-natural F G α = Nat-path λ _ → sym (α .is-natural _ _ _)
  precomposite-adjunction .counit .η F = cohere! (F ▸ adj.counit)
  precomposite-adjunction .counit .is-natural F G α = Nat-path λ _ → sym (α .is-natural _ _ _)
  precomposite-adjunction .zig {F} = Nat-path λ _ → Func.annihilate F adj.zag
  precomposite-adjunction .zag {F} = Nat-path λ _ → Func.annihilate F adj.zig
```

<!--
```agda
adjoint-natural-iso
  : ∀ {L L' : Functor C D} {R R' : Functor D C}
  → L ≅ⁿ L' → R ≅ⁿ R' → L ⊣ R → L' ⊣ R'
adjoint-natural-iso {C = C} {D = D} {L} {L'} {R} {R'} α β L⊣R = L'⊣R' where
  open _⊣_ L⊣R
  module α = Isoⁿ α
  module β = Isoⁿ β
  open _=>_
  module C = Cat.Reasoning C
  module D = Cat.Reasoning D
  module L = Func L
  module L' = Func L'
  module R = Func R
  module R' = Func R'

  -- Abbreviations for equational reasoning
  α→ : ∀ {x} → D.Hom (L.₀ x) (L'.₀ x)
  α→ {x} = α.to .η x

  α← : ∀ {x} → D.Hom (L'.₀ x) (L.₀ x)
  α← {x} = α.from .η x

  β→ : ∀ {x} → C.Hom (R.₀ x) (R'.₀ x)
  β→ {x} = β.to .η x

  β← : ∀ {x} → C.Hom (R'.₀ x) (R.₀ x)
  β← {x} = β.from .η x

  L'⊣R' : L' ⊣ R'
  L'⊣R' ._⊣_.unit =  (β.to ◆ α.to) ∘nt unit
  L'⊣R' ._⊣_.counit = counit ∘nt (α.from ◆ β.from)
  L'⊣R' ._⊣_.zig =
    (counit.ε _ D.∘ (L.₁ β← D.∘ α←)) D.∘ L'.₁ (⌜ R'.₁ α→ C.∘ β→ ⌝ C.∘ unit.η _) ≡⟨ ap! (sym $ β.to .is-natural _ _ _) ⟩
    (counit.ε _ D.∘ ⌜ L.₁ β← D.∘ α← ⌝) D.∘ L'.₁ ((β→ C.∘ R.₁ α→) C.∘ unit.η _)  ≡⟨ ap! (sym $ α.from .is-natural _ _ _) ⟩
    (counit.ε _ D.∘ α← D.∘ L'.₁ β←) D.∘ L'.₁ ((β→ C.∘ R.₁ α→) C.∘ unit.η _)     ≡⟨ D.pullr (D.pullr (L'.collapse (C.pulll (C.cancell (β.invr ηₚ _))))) ⟩
    counit.ε _ D.∘ α← D.∘ L'.₁ (R.₁ α→ C.∘ unit.η _)                            ≡⟨ ap (counit.ε _ D.∘_) (α.from .is-natural _ _ _) ⟩
    counit.ε _ D.∘ L.₁ (R.₁ α→ C.∘ unit.η _) D.∘ α←                             ≡⟨ D.push-inner (L.F-∘ _ _) ⟩
    (counit.ε _ D.∘ L.₁ (R.₁ α→)) D.∘ (L.₁ (unit.η _) D.∘ α←)                   ≡⟨ D.pushl (counit.is-natural _ _ _) ⟩
    α→ D.∘ counit.ε _ D.∘ L.₁ (unit.η _) D.∘ α←                                 ≡⟨ ap (α→ D.∘_) (D.cancell zig) ⟩
    α→ D.∘ α←                                                                   ≡⟨ α.invl ηₚ _ ⟩
    D.id ∎
  L'⊣R' ._⊣_.zag =
    R'.₁ (counit.ε _ D.∘ L.₁ β← D.∘ α←) C.∘ ((R'.₁ α→ C.∘ β→) C.∘ unit.η _) ≡⟨ C.extendl (C.pulll (R'.collapse (D.pullr (D.cancelr (α.invr ηₚ _))))) ⟩
    R'.₁ (counit.ε _ D.∘ L.₁ β←) C.∘ β→ C.∘ unit.η _                        ≡⟨ C.extendl (sym (β.to .is-natural _ _ _)) ⟩
    β→ C.∘ R.₁ (counit.ε _ D.∘ L.₁ β←) C.∘ unit.η _                         ≡⟨ C.push-inner (R.F-∘ _ _) ⟩
    ((β→ C.∘ R.₁ (counit.ε _)) C.∘ (R.₁ (L.₁ β←) C.∘ unit.η _))             ≡⟨ ap₂ C._∘_ refl (sym $ unit.is-natural _ _ _) ⟩
    (β→ C.∘ R.₁ (counit.ε _)) C.∘ (unit.η _ C.∘ β←)                         ≡⟨ C.cancel-inner zag ⟩
    β→ C.∘ β←                                                               ≡⟨ β.invl ηₚ _ ⟩
    C.id ∎

adjoint-natural-isol
  : ∀ {L L' : Functor C D} {R : Functor D C}
  → L ≅ⁿ L' → L ⊣ R → L' ⊣ R
adjoint-natural-isol α = adjoint-natural-iso α idni

adjoint-natural-isor
  : ∀ {L : Functor C D} {R R' : Functor D C}
  → R ≅ⁿ R' → L ⊣ R → L ⊣ R'
adjoint-natural-isor β = adjoint-natural-iso idni β
```
-->

<!--
```agda
{-
Characterising paths between adjoints.
-}
module _
  {L L' : Functor C D} {R R' : Functor D C}
  where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D

  module _
    {adj : L ⊣ R} {adj' : L' ⊣ R'}
    (p : L ≡ L') (q : R ≡ R')
    where
    private
      module adj = _⊣_ adj
      module adj' = _⊣_ adj'
      open Functor
      open _=>_

    adjoint-pathp
      : PathP (λ i → Id => q i F∘ p i) adj.unit adj'.unit
      → PathP (λ i → p i F∘ q i => Id) adj.counit adj'.counit
      → PathP (λ i → p i ⊣ q i) adj adj'
    adjoint-pathp r s i ._⊣_.unit = r i
    adjoint-pathp r s i ._⊣_.counit = s i
    adjoint-pathp r s i ._⊣_.zig {A} =
      is-prop→pathp (λ i → D.Hom-set _ _ (s i .η (p i .F₀ A) D.∘ p i .F₁ (r i .η A)) D.id)
        adj.zig adj'.zig i
    adjoint-pathp r s i ._⊣_.zag {A} =
      is-prop→pathp (λ i → C.Hom-set _ _ (q i .F₁ (s i .η A) C.∘ r i .η (q i .F₀ A)) C.id)
        adj.zag adj'.zag i
```
-->
