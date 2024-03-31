---
description: |
  We present two definitions of adjoint functors, one which is
  computationally convenient (units and counits), and one which is
  conceptually clean (adjoints as "optimal solutions" --- initial
  objects in certain comma categories).
---
<!--
```agda
{-# OPTIONS -vtc.decl:5 #-}
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

  open unit using (η) public
  open counit using (ε) public
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
    zig : ∀ {A} → ε (L .F₀ A) D.∘ L .F₁ (η A) ≡ D.id
    zag : ∀ {B} → R .F₁ (ε B) C.∘ η (R .F₀ B) ≡ C.id

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
  L-adjunct f = R.₁ f C.∘ adj.η _

  R-adjunct : ∀ {a b} → C.Hom a (R.₀ b) → D.Hom (L.₀ a) b
  R-adjunct f = adj.ε _ D.∘ L.₁ f
```

The important part that the actual data of an adjunction gets you is
these functions are inverse _equivalences_ between the hom-sets
$\hom(La,b) \cong \hom(a,Rb)$.

```agda
  L-R-adjunct : ∀ {a b} → is-right-inverse (R-adjunct {a} {b}) L-adjunct
  L-R-adjunct f =
    R.₁ (adj.ε _ D.∘ L.₁ f) C.∘ adj.η _        ≡⟨ R.pushl refl ⟩
    R.₁ (adj.ε _) C.∘ R.₁ (L.₁ f) C.∘ adj.η _  ≡˘⟨ C.refl⟩∘⟨ adj.unit.is-natural _ _ _ ⟩
    R.₁ (adj.ε _) C.∘ adj.η _ C.∘ f            ≡⟨ C.cancell adj.zag ⟩
    f                                          ∎

  R-L-adjunct : ∀ {a b} → is-left-inverse (R-adjunct {a} {b}) L-adjunct
  R-L-adjunct f =
    adj.ε _ D.∘ L.₁ (R.₁ f C.∘ adj.η _)       ≡⟨ D.refl⟩∘⟨ L.F-∘ _ _ ⟩
    adj.ε _ D.∘ L.₁ (R.₁ f) D.∘ L.₁ (adj.η _) ≡⟨ D.extendl (adj.counit.is-natural _ _ _) ⟩
    f D.∘ adj.ε _ D.∘ L.₁ (adj.η _)           ≡⟨ D.elimr adj.zig ⟩
    f                                         ∎

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
    R.₁ (f D.∘ L.₁ g) C.∘ adj.η _       ≡⟨ R.F-∘ _ _ C.⟩∘⟨refl ⟩
    (R.₁ f C.∘ R.₁ (L.₁ g)) C.∘ adj.η _ ≡⟨ C.extendr (sym $ adj.unit.is-natural _ _ _) ⟩
    (R.₁ f C.∘ adj.η _) C.∘ g           ∎

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
    adj.ε _ D.∘ L.₁ (R.₁ f C.∘ g)     ≡⟨ D.refl⟩∘⟨ L.F-∘ _ _ ⟩
    adj.ε _ D.∘ L.₁ (R.₁ f) D.∘ L.₁ g ≡⟨ D.extendl (adj.counit.is-natural _ _ _) ⟩
    f D.∘ (adj.ε _ D.∘ L.₁ g)         ∎

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

# Free Objects

Another perspective is that adjunctions describe free constructions:
the right adjoint forgets structure, and the left adjoint freely adds it.
These sorts of adjunctions are so common that we may be tempted to *define*
free constructions as left adjoints. However, this doesn't quite capture
the whole story: there are many situations where a left adjoint does not
exist, yet we can perform a free constructions on *some* objects.
This gives rise to the following definition:

:::{.definition #free-object}

Let $\cC, \cD$ be a pair of categories, and let $U : \cC \to \cD$ be a
functor. An object $A : \cC$ equipped with a map $\eta : \cD(X, U(A))$
is a **free object** on $X : \cD$ with respect to $U$ if it satisfies
the following universal property:

- For every $B : \cD$ and $f : \cD(X, U(B))$, there exists a unique
  map $\eps : \cC(A, B)$ with $U(\eps) \circ \eta = f$.
:::

<!--
```agda
module _
  (U : Functor C D)
  where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module U = Func U
```
-->

```agda
  record is-free-object {X : D.Ob} {A : C.Ob} (unit : D.Hom X (U.₀ A)) : Type (adj-level C D) where
    field
      adjunctl : ∀ {B} → D.Hom X (U.₀ B) → C.Hom A B
      commute : ∀ {B} {f : D.Hom X (U.₀ B)} → U.₁ (adjunctl f) D.∘ unit ≡ f
      unique
        : ∀ {B} {f : D.Hom X (U.₀ B)}
        → (other : C.Hom A B)
        → U.₁ other D.∘ unit ≡ f
        → other ≡ adjunctl f

    adjunctl-natural
      : ∀ {B B' : C.Ob}
      → (f : C.Hom B B') (g : D.Hom X (U.₀ B))
      → adjunctl (U.₁ f D.∘ g) ≡ f C.∘ adjunctl g
    adjunctl-natural f g = sym (unique (f C.∘ adjunctl g) (U.popr commute))
```


<!--
```agda
    unique₂
      : ∀ {B} {f : D.Hom X (U.₀ B)}
      → (other₁ other₂ : C.Hom A B)
      → U.₁ other₁ D.∘ unit ≡ f
      → U.₁ other₂ D.∘ unit ≡ f
      → other₁ ≡ other₂
    unique₂ other₁ other₂ p q = unique other₁ p ∙ sym (unique other₂ q)

    adjunctl-unit : adjunctl unit ≡ C.id
    adjunctl-unit = sym (unique C.id (D.eliml U.F-id))
```
-->

A free object on $X : \cC$ with respect to $U$ is an explicit choice of
$A : \cC$ and $\eta : \cD(X, U(A))$ that form a free object.

```agda
  record Free-object (X : D.Ob) : Type (adj-level C D) where
    field
      free : C.Ob
      unit : D.Hom X (U.₀ free)
      has-is-free : is-free-object unit
```

Intuitively, a free object on $X$ is an approximation of a
(potentially non-existent) left adjoint at $X$. The universal property
gives us a left adjunct that only works for $X$, and the unit of the free
object gives us the corresponding right adjunct.

```agda
    open is-free-object has-is-free renaming (commute to adjunctrl) public

    adjunctr : ∀ {B : C.Ob} → C.Hom free B → D.Hom X (U.₀ B)
    adjunctr f = U.₁ f D.∘ unit

    adjunctlr : ∀ {B} {f : C.Hom free B} → adjunctl (adjunctr f) ≡ f
    adjunctlr = sym (unique _ refl)

    adjunctr-unique
        : ∀ {B} {f : C.Hom free B}
        → (other : D.Hom X (U.₀ B))
        → adjunctl other ≡ f
        → other ≡ adjunctr f
    adjunctr-unique {f = f} other p =
      other                             ≡˘⟨ adjunctrl ⟩
      (U.₁ ⌜ adjunctl other ⌝ D.∘ unit) ≡⟨ ap! p ⟩
      U.₁ f D.∘ unit                    ∎

    adjunctr-natural
      : ∀ {B B' : C.Ob}
      → (f : C.Hom B B') (g : C.Hom free B)
      → adjunctr (f C.∘ g) ≡ U.₁ f D.∘ adjunctr g 
    adjunctr-natural f g = D.pushl (U.F-∘ _ _)
```

A free object $A : \cC$ on $X : \cD$ induces an equivalence between
$\cD(X, U(B))$ and $\cC(A, B)$. In other words, free objects are
representing objects for the functor $\cD(X,U(-))$.

```agda
    adjunctl-is-equiv : ∀ B → is-equiv (adjunctl {B})
    adjunctl-is-equiv B =
      is-iso→is-equiv $ iso adjunctr (λ _ → adjunctlr) (λ _ → adjunctrl)
```

Free objects have all the usual hallmarks of universal constructions:
the universal property of free objects is a proposition, and they are
unique up to isomorphism.

<!--
```agda
module _
  {U : Functor C D}
  where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module U = Func U

  open Free-object
```
-->

```agda
  is-free-object-is-prop
    : ∀ {X A} {unit : D.Hom X (U.₀ A)}
    → is-prop (is-free-object U unit)

  free-object-unique : ∀ {X} (A B : Free-object U X) → A .free C.≅ B .free
```

<details>
<summary>The proofs follow the usual script for universal constructions,
so we will omit the details.</summary>

```agda
  free-object-unique a b =
    C.make-iso (a .adjunctl (b .unit)) (b .adjunctl (a .unit))
      (unique₂ b _ _ (U.popr (b .adjunctrl) ∙ a .adjunctrl) (D.eliml U.F-id))
      (unique₂ a _ _ (U.popr (a .adjunctrl) ∙ b .adjunctrl) (D.eliml U.F-id))

  is-free-object-is-prop {X = X} {A = A} {unit = unit} fo fo' = path where
    module fo = is-free-object fo
    module fo' = is-free-object fo'

    adjunctl-path : ∀ {B} (f : D.Hom X (U.₀ B)) → fo.adjunctl f ≡ fo'.adjunctl f
    adjunctl-path f = fo'.unique (fo.adjunctl f) fo.commute

    path : fo ≡ fo' 
    path i .is-free-object.adjunctl f = adjunctl-path f i
    path i .is-free-object.commute {f = f} =
      is-prop→pathp (λ i → D.Hom-set _ _ (U.₁ (adjunctl-path f i) D.∘ unit) f)
        fo.commute fo'.commute i
    path i .is-free-object.unique {f = f} o p =
      is-prop→pathp (λ i → C.Hom-set _ _ o (adjunctl-path f i))
        (fo.unique o p) (fo'.unique o p) i
```
</details>

<!--
```agda
  private unquoteDecl free-obj-eqv = declare-record-iso free-obj-eqv (quote Free-object) 

  -- This lets us ignore 'is-free-object' when proving equality.
  Extensional-Free-object
    : ∀ {X ℓr}
    → ⦃ sa : Extensional (Σ[ A ∈ C.Ob ] (D.Hom X (U.₀ A))) ℓr ⦄
    → Extensional (Free-object U X) ℓr
  Extensional-Free-object ⦃ sa ⦄ =
    embedding→extensional
      (Iso→Embedding free-obj-eqv
      ∙emb Equiv→Embedding Σ-assoc
      ∙emb (fst , Subset-proj-embedding λ _ → is-free-object-is-prop))
      sa

  instance
    Extensionality-Free-object
      : ∀ {X}
      → Extensionality (Free-object U X)
    Extensionality-Free-object = record { lemma = quote Extensional-Free-object }
```
-->

## Free objects and adjoints

If $U$ has a left adjoint $F$, then every $X : \cD$ has a corresponding
free object given by $(F(X), \eta)$, where $\eta$ is the unit of the
adjunction.

```agda
  module _ {F : Functor D C} (F⊣U : F ⊣ U) where
    open is-free-object
    open _⊣_ F⊣U

    left-adjoint→unit-is-free : ∀ x → is-free-object U (unit.η x)
    left-adjoint→unit-is-free x .adjunctl f = R-adjunct F⊣U f
    left-adjoint→unit-is-free x .commute = L-R-adjunct F⊣U _
    left-adjoint→unit-is-free x .unique other p =
      Equiv.injective (_ , L-adjunct-is-equiv F⊣U) (p ∙ sym (L-R-adjunct F⊣U _))

    left-adjoint→free-objects : ∀ X → Free-object U X
    left-adjoint→free-objects X .free = Functor.F₀ F X
    left-adjoint→free-objects X .unit = unit.η X
    left-adjoint→free-objects X .has-is-free = left-adjoint→unit-is-free X
```

Conversely, if $\cD$ has all free objects, then $U$ has a left adjoint.
We begin by constructing a functor $F : \cD \to \cC$ that assigns each
object to its free counterpart; functoriality follows from the universal
property.

```agda
  module _ (free-objects : ∀ X → Free-object U X) where
    private
      module F {X} = Free-object (free-objects X)
      open Functor
      open _=>_
      open _⊣_

    free-objects→functor : Functor D C
    free-objects→functor .F₀ X = F.free {X}
    free-objects→functor .F₁ f = F.adjunctl (F.unit D.∘ f)
    free-objects→functor .F-id =
      F.adjunctl ⌜ F.unit D.∘ D.id ⌝ ≡⟨ ap! (D.idr _) ⟩
      F.adjunctl F.unit              ≡⟨ F.adjunctl-unit ⟩
      C.id ∎
    free-objects→functor .F-∘ f g =
      F.adjunctl ⌜ F.unit D.∘ f D.∘ g ⌝                               ≡⟨ ap! (D.extendl (sym F.adjunctrl)) ⟩
      F.adjunctl (U.₁ (F.adjunctl (F.unit D.∘ f)) D.∘ (F.unit D.∘ g)) ≡⟨ F.adjunctl-natural _ _ ⟩
      F.adjunctl (F.unit D.∘ f) C.∘ F.adjunctl (F.unit D.∘ g)         ∎
```

The unit of the adjunction is given by $\eta$, the counit by $\eps \id$,and
Both naturality and the zig-zag identities follow from some short arguments
about adjuncts.

```agda
    free-objects→left-adjoint : free-objects→functor ⊣ U
    free-objects→left-adjoint .unit .η X = F.unit {X}
    free-objects→left-adjoint .unit .is-natural X Y f = sym F.adjunctrl
    free-objects→left-adjoint .counit .η X = F.adjunctl D.id
    free-objects→left-adjoint .counit .is-natural X Y f =
      F.adjunctl D.id C.∘ F.adjunctl (F.unit D.∘ U.₁ f)       ≡˘⟨ F.adjunctl-natural _ _ ⟩
      F.adjunctl (U.₁ (F.adjunctl D.id) D.∘ F.unit D.∘ U.₁ f) ≡⟨ ap F.adjunctl (D.cancell F.adjunctrl ∙ sym (D.idr _)) ⟩
      F.adjunctl (U.₁ f D.∘ D.id)                             ≡⟨ F.adjunctl-natural _ _ ⟩
      f C.∘ F.adjunctl D.id ∎
    free-objects→left-adjoint .zig =
      F.adjunctl D.id C.∘ F.adjunctl (F.unit D.∘ F.unit)       ≡˘⟨ F.adjunctl-natural _ _ ⟩
      F.adjunctl (U.₁ (F.adjunctl D.id) D.∘ F.unit D.∘ F.unit) ≡⟨ ap F.adjunctl (D.cancell F.adjunctrl) ⟩
      F.adjunctl F.unit                                        ≡⟨ F.adjunctl-unit ⟩
      C.id ∎
    free-objects→left-adjoint .zag =
      F.adjunctrl
```

If we round-trip a left adjoint through these two constructions, then
we obtain the same functor we started with. Moreover, we also obtain
the same unit/counit!


```agda
  left-adjoint→free-objects→left-adjoint
    : ∀ {F : Functor D C}
    → (F⊣U : F ⊣ U)
    → free-objects→functor (left-adjoint→free-objects F⊣U) ≡ F
  left-adjoint→free-objects→left-adjoint {F = F} F⊣U =
    Functor-path (λ _ → refl) λ f →
      ap (R-adjunct F⊣U) (unit.is-natural _ _ f)
      ∙ R-L-adjunct F⊣U (F.₁ f)
    where
      module F = Functor F
      open _⊣_ F⊣U

  adjoint-pair→free-objects→adjoint-pair
    : ∀ {F : Functor D C}
    → (F⊣U : F ⊣ U)
    → PathP (λ i → left-adjoint→free-objects→left-adjoint F⊣U i ⊣ U)
      (free-objects→left-adjoint (left-adjoint→free-objects F⊣U))
      F⊣U
  adjoint-pair→free-objects→adjoint-pair {F = F} F⊣U =
    adjoint-pathp _ _
      (Nat-pathp _ _ λ _ → refl)
      (Nat-pathp _ _ λ x → C.elimr F.F-id)
    where module F = Functor F
```

A similar result holds for a system of free objects.

```agda
  free-objects→left-adjoint→free-objects
    : ∀ (free-objects : ∀ x → Free-object U x)
    → left-adjoint→free-objects (free-objects→left-adjoint free-objects) ≡ free-objects
  free-objects→left-adjoint→free-objects free-objects = trivial!
```

This yields an equivalence between systems of free objects and left adjoints.

```agda
  free-objects≃left-adjoint
    : (∀ x → Free-object U x) ≃ (Σ[ F ∈ Functor D C ] F ⊣ U)
```

<details>
<summary>Constructing the equivalence is straightforward, as we
already have all the pieces laying about!
</summary>

```agda
  free-objects≃left-adjoint = Iso→Equiv $
    (λ free-objects →
      free-objects→functor free-objects ,
      free-objects→left-adjoint free-objects) ,
    iso (λ left-adj → left-adjoint→free-objects (left-adj .snd))
      (λ left-adj →
        left-adjoint→free-objects→left-adjoint (left-adj .snd) ,ₚ
        adjoint-pair→free-objects→adjoint-pair (left-adj .snd))
      free-objects→left-adjoint→free-objects
```
</details>

## Free objects and initiality

In categorical semantics, syntax for a theory $\bT$ is often
presented in two seemingly unconnected ways:

1. Via a left adjoint to the forgetful functor that forgets the structure
  of a $\bT$-model; or
2. As an [[initial object]] in the category of $\bT$-models.

Left adjoints encode the universal property "syntax with generators":
structure-preserving maps $\cC(F(X),A)$ out of the syntax generated by $X$
are given by non-structure $\cD(X,U(A))$ on the generators. Conversely,
initial objects give us the universal property of "syntax without generators":
there is a unique structure-preserving map out of the syntax into each model.

We can somewhat reconcile these views by recalling that
[[left adjoints preserve colimits|lapc]]. The initial object is a colimit,
so the initial object in the category $\bT$-models is $F(\bot)$. In other
words: "syntax without generators" and "syntax on 0 generators" coincide.
This correspondence remains intact even when we lack a full left adjoint.

For the remainder of this section, assume that $\cD$ has an initial object
$\bot_{\cD}$. If there is a free object $A : \cC$ on $\bot_{\cD}$, then
$A$ is an initial object in $\cC$.

```agda
  module _ (initial : Initial D) where
    open Initial initial
    open is-free-object

    free-on-initial→initial
      : (F[⊥] : Free-object U bot)
      → is-initial C (F[⊥] .free)
    free-on-initial→initial F[⊥] x .centre = F[⊥] .adjunctl ¡
    free-on-initial→initial F[⊥] x .paths f =
      sym $ F[⊥] .unique f (sym (¡-unique _))
```

Conversely, if $\cC$ has an initial object $\bot_{\cC}$, then $\bot_{\cC}$
is a free object for $\bot_{\cC}$.

```agda
    is-initial→free-on-initial
      : (c-initial : Initial C)
      → is-free-object U {A = Initial.bot c-initial} ¡ 
    is-initial→free-on-initial c-initial .adjunctl _ =
      Initial.¡ c-initial
    is-initial→free-on-initial c-initial .commute =
      ¡-unique₂ _ _
    is-initial→free-on-initial c-initial .unique _ _ =
      sym $ Initial.¡-unique c-initial _
```

Note an initial object in $\cC$ does not guarantee an initial object in
$\cD$, regardless of how many free objects there are. Put syntactically,
a notion of "syntax without generators" does not imply that there is an
object of 0 generators!

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

Yet another perspective on adjoint functors is given by finding "most
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
  Universal-morphism : Functor D C → C.Ob → Type _
  Universal-morphism R X = Initial (X ↙ R)
```

If $R : \cD \to \cC$ has universal morphisms for every object of $\cC$, then
this assignment extends to a functor $L : \cC \to \cD$ with $L \dashv R$ as
defined above. Likewise, if there already exists a left adjoint $L \dashv R$,
then we can obtain a system of universal morphisms.

<!--
```agda
module _
  (U : Functor C D)
  where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module U = Func U

  open Free-object
```
-->

We will establish this correspondence by showing that universal morphisms
are equivalent to free objects: both encode the data of a universal pair
$(A, \cD(X, U(A)))$.

```agda
  free-object≃universal-map : ∀ X → Free-object U X ≃ Universal-morphism U X
```

The proof is an exercise in shuffling data around: if we have a free
object on $X$, then the unit of the free object gives a pair $(A, \cD(X, U(A)))$.
Moreover, the universal properties are almost identical; the only differences
are some extraneous identity morphisms.

```agda
  free-object≃universal-map X = Iso→Equiv isom
    where
      open Initial

      free→univ : Free-object U X → Universal-morphism U X
      free→univ fo .bot = ↓obj (fo .unit)
      free→univ fo .has⊥ x .centre = ↓hom $
        (↓Obj.map x D.∘ D.id)                  ≡⟨ D.idr _ ⟩
        ↓Obj.map x                             ≡˘⟨ fo .adjunctrl ⟩
        adjunctr fo (adjunctl fo (↓Obj.map x)) ∎
      free→univ fo .has⊥ x .paths α = ext $ sym $ fo .unique _ $
        U.₁ (α .↓Hom.β) D.∘ fo .unit ≡˘⟨ ↓Hom.sq α ⟩
        ↓Obj.map x D.∘ D.id ≡⟨ D.idr _ ⟩
        ↓Obj.map x ∎
```

The other direction is equally as easy: a universal morphism is already
a pair $(A, \cD(X, U(A)))$ with the appropriate universal property, so
all that we need to do is shuffle around some fields.

```agda
      univ→free : Universal-morphism U X → Free-object U X
      univ→free i .free = ↓Obj.y (i .bot)
      univ→free i .unit = ↓Obj.map (i .bot)
      univ→free i .has-is-free .is-free-object.adjunctl f =
        ↓Hom.β (i .has⊥ (↓obj f) .centre)
      univ→free i .has-is-free .is-free-object.commute {f = f} =
        sym (↓Hom.sq (i .has⊥ (↓obj f) .centre)) ∙ D.idr _
      univ→free i .has-is-free .is-free-object.unique {f = f} g p =
        sym $ ap ↓Hom.β (i .has⊥ (↓obj f) .paths (↓hom (D.idr _ ∙ sym p)))
```

This proposed isomorphism so mechanice that Agda is able to derive
the left and right inverse proofs for us!

```agda
      isom : Iso (Free-object U X) (Universal-morphism U X)
      isom = trivial-iso! free→univ univ→free
```

We have already shown that systems of free objects are equivalent to
left adjoints, so all that we need to do is precompose with the equivalence
we just constructed to get our result.

```agda
  universal-maps≃left-adjoint
    : (∀ X → Universal-morphism U X) ≃ (Σ[ F ∈ Functor D C ] F ⊣ U)
  universal-maps≃left-adjoint =
    Π-cod≃ free-object≃universal-map e⁻¹ ∙e free-objects≃left-adjoint
```

<!--
```agda
module _
  {U : Functor C D}
  where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module U = Func U

  open Free-object

  universal-maps→L : (∀ X → Universal-morphism U X) → Functor D C
  universal-maps→L = fst ⊙ Equiv.to (universal-maps≃left-adjoint U)

  universal-maps→L⊣R
    : (univ : ∀ X → Universal-morphism U X)
    → (universal-maps→L univ) ⊣ U
  universal-maps→L⊣R = snd ⊙ Equiv.to (universal-maps≃left-adjoint U)

  L⊣R→universal-maps : ∀ {F : Functor D C} → F ⊣ U → ∀ X → Universal-morphism U X
  L⊣R→universal-maps {F = F} F⊣U = Equiv.from (universal-maps≃left-adjoint U) (F , F⊣U)
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
  opposite-adjunction .unit .η _ = adj.ε _
  opposite-adjunction .unit .is-natural x y f = sym (adj.counit.is-natural _ _ _)
  opposite-adjunction .counit .η _ = adj.η _
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
  postcomposite-adjunction .unit .is-natural F G α = ext λ _ → adj.unit.is-natural _ _ _
  postcomposite-adjunction .counit .η F = cohere! (adj.counit ◂ F)
  postcomposite-adjunction .counit .is-natural F G α = ext λ _ → adj.counit.is-natural _ _ _
  postcomposite-adjunction .zig = ext λ _ → adj.zig
  postcomposite-adjunction .zag = ext λ _ → adj.zag

  precomposite-adjunction : precompose R {D = E} ⊣ precompose L
  precomposite-adjunction .unit .η F = cohere! (F ▸ adj.unit)
  precomposite-adjunction .unit .is-natural F G α = ext λ _ → sym (α .is-natural _ _ _)
  precomposite-adjunction .counit .η F = cohere! (F ▸ adj.counit)
  precomposite-adjunction .counit .is-natural F G α = ext λ _ → sym (α .is-natural _ _ _)
  precomposite-adjunction .zig {F} = ext λ _ → Func.annihilate F adj.zag
  precomposite-adjunction .zag {F} = ext λ _ → Func.annihilate F adj.zig
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
  open _=>_ using (is-natural)
  module C = Cat.Reasoning C
  module D = Cat.Reasoning D
  module L = Func L
  module L' = Func L'
  module R = Func R
  module R' = Func R'

  -- Abbreviations for equational reasoning
  α→ : ∀ {x} → D.Hom (L.₀ x) (L'.₀ x)
  α→ {x} = α.to ._=>_.η x

  α← : ∀ {x} → D.Hom (L'.₀ x) (L.₀ x)
  α← {x} = α.from ._=>_.η x

  β→ : ∀ {x} → C.Hom (R.₀ x) (R'.₀ x)
  β→ {x} = β.to ._=>_.η x

  β← : ∀ {x} → C.Hom (R'.₀ x) (R.₀ x)
  β← {x} = β.from ._=>_.η x

  L'⊣R' : L' ⊣ R'
  L'⊣R' ._⊣_.unit =  (β.to ◆ α.to) ∘nt unit
  L'⊣R' ._⊣_.counit = counit ∘nt (α.from ◆ β.from)
  L'⊣R' ._⊣_.zig =
    (ε _ D.∘ (L.₁ β← D.∘ α←)) D.∘ L'.₁ (⌜ R'.₁ α→ C.∘ β→ ⌝ C.∘ η _) ≡⟨ ap! (sym $ β.to .is-natural _ _ _) ⟩
    (ε _ D.∘ ⌜ L.₁ β← D.∘ α← ⌝) D.∘ L'.₁ ((β→ C.∘ R.₁ α→) C.∘ η _)  ≡⟨ ap! (sym $ α.from .is-natural _ _ _) ⟩
    (ε _ D.∘ α← D.∘ L'.₁ β←) D.∘ L'.₁ ((β→ C.∘ R.₁ α→) C.∘ η _)     ≡⟨ D.pullr (D.pullr (L'.collapse (C.pulll (C.cancell (β.invr ηₚ _))))) ⟩
    ε _ D.∘ α← D.∘ L'.₁ (R.₁ α→ C.∘ η _)                            ≡⟨ ap (ε _ D.∘_) (α.from .is-natural _ _ _) ⟩
    ε _ D.∘ L.₁ (R.₁ α→ C.∘ η _) D.∘ α←                             ≡⟨ D.push-inner (L.F-∘ _ _) ⟩
    (ε _ D.∘ L.₁ (R.₁ α→)) D.∘ (L.₁ (η _) D.∘ α←)                   ≡⟨ D.pushl (counit.is-natural _ _ _) ⟩
    α→ D.∘ ε _ D.∘ L.₁ (η _) D.∘ α←                                 ≡⟨ ap (α→ D.∘_) (D.cancell zig) ⟩
    α→ D.∘ α←                                                       ≡⟨ α.invl ηₚ _ ⟩
    D.id ∎
  L'⊣R' ._⊣_.zag =
    R'.₁ (ε _ D.∘ L.₁ β← D.∘ α←) C.∘ ((R'.₁ α→ C.∘ β→) C.∘ η _) ≡⟨ C.extendl (C.pulll (R'.collapse (D.pullr (D.cancelr (α.invr ηₚ _))))) ⟩
    R'.₁ (ε _ D.∘ L.₁ β←) C.∘ β→ C.∘ η _                        ≡⟨ C.extendl (sym (β.to .is-natural _ _ _)) ⟩
    β→ C.∘ R.₁ (ε _ D.∘ L.₁ β←) C.∘ η _                         ≡⟨ C.push-inner (R.F-∘ _ _) ⟩
    ((β→ C.∘ R.₁ (ε _)) C.∘ (R.₁ (L.₁ β←) C.∘ η _))             ≡⟨ ap₂ C._∘_ refl (sym $ unit.is-natural _ _ _) ⟩
    (β→ C.∘ R.₁ (ε _)) C.∘ (η _ C.∘ β←)                         ≡⟨ C.cancel-inner zag ⟩
    β→ C.∘ β←                                                   ≡⟨ β.invl ηₚ _ ⟩
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

