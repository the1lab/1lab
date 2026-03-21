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
open import Cat.Instances.Functor
open import Cat.Diagram.Initial
open import Cat.Functor.Compose
open import Cat.Instances.Comma
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Natural.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Functor.Adjoint where
```

<!--
```agda
private variable
  o h o' ℓ' : Level
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

:::{.definition #adjunction alias="left-adjoint right-adjoint adjoint-functor adjoint unit counit"}
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

  module unit = Cat.Natural.Reasoning unit
  module counit = Cat.Natural.Reasoning counit renaming (η to ε)

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
      is-prop→pathp
        (λ i → D.Hom-set _ _ (s i .η (p i .F₀ A) D.∘ p i .F₁ (r i .η A)) D.id)
        adj.zig adj'.zig i
    adjoint-pathp r s i ._⊣_.zag {A} =
      is-prop→pathp
        (λ i → C.Hom-set _ _ (q i .F₁ (s i .η A) C.∘ r i .η (q i .F₀ A)) C.id)
        adj.zag adj'.zag i
```
-->

## Adjuncts {defines="adjunct left-adjunct right-adjunct"}

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
  abstract
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

  adjunct-hom-equiv : ∀ {a b} → D.Hom (L.₀ a) b ≃ C.Hom a (R.₀ b)
  adjunct-hom-equiv = L-adjunct , L-adjunct-is-equiv
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
    sym (R-adjunct-naturalr _ _) ∙∙ ap R-adjunct sq ∙∙ R-adjunct-naturalr _ _
```
-->

## Free objects {defines="universal-morphism"}

In contrast to the formal descriptions above, this section presents an
*intuitive* perspective on adjoint functors: namely, a (left) adjoint,
when it exists, provides the *most efficient possible solutions* to the
problem posed by its (right) adjoint. This perspective is particularly
helpful when the right adjoint in question is easily conceptualised as a
*forgetful* functor. For a concrete example, we could consider the
([[fully faithful]]) inclusion of [[abelian groups]] into all
[[groups]].

The first thing to notice is that $U : \Ab \to \Grp$ induces a notion of
morphism from groups $G$ to abelian groups $H$: this is the hom-set
$\hom_\Grp(G, U(H))$. This observation isn't particularly deep *in this
case*, since the maps between abelian groups are also group
homomorphisms, but note that this works for *any* functor: the forgetful
functor $U : \Grp \to \Sets$ lets us consider maps "from a set to a
group".

By letting the abelian group $H$ vary, we can consider morphisms from a
group $G$ to *some* abelian group. These form a category in their own
right, the [[comma category]] $G \swarrow U$. In a sense, these are all
solutions to the problem of *turning $G$ into an abelian group* --- or,
more precisely, *mapping* $G$ into an abelian group. For a given $G$,
there can be arbitrarily many of these, and some are extremely boring:
for example, the zero group is abelian, so we can always consider $G \to
\varnothing$ as a way to "turn $G$ into an abelian group"!

So we're left with defining which of these solutions is *the most
efficient*. Since turning a group abelian necessarily involves
identifying elements that were previously distinct --- all the $gh \ne
hg$ have to be squashed --- we could attempt to measure *how many*
elements got identified, and choose the one that imposes the least
amount of these relations. While this might be tractable for finitely
presented groups, it would be really hard to define, let alone measure,
these *imposed relations* for an arbitrary $U : \cD \to \cC$!

However, we don't need any actual *count* of the relations imposed, or
even a notion of relation. The important thing to observe is that, if
$(H, \eta)$ and $(H', \eta')$ are both *ways of turning $G$ into an
abelian group*, then we can factor $\eta'$ as a map

$$
G \xto{\eta} H \xto{f} H'
$$

if *and only if* $\eta$ imposes less relations on the elements of $G$
than $\eta'$ does. The *most efficient* solution to turning $G$ into an
abelian group, then, would be the one through which all others factor,
since it will *impose the least number of relations*! Abstractly, we are
looking for an [[initial object]] in the comma category $G \swarrow U$.

While the abstract phrasing we've arrived at is very elegant, it does
seriously obfuscate the data necessary. To work with left adjoints
smoothly, and to present the ideas more clearly, we introduce an
auxiliary notion: **free objects**.

<!--
```agda
module _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    (U : Functor C D) where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module U = Func U
```
-->

::: {.definition #free-object}
A **free object** on $X : \cC$, relative to $U : \cD \to \cC$, consists
of an object $F(X) : \cD$ and an arrow $\eta : X \to UF(X)$, such that
every $f : X \to UY$, $f$ factors uniquely through $\eta$. Expanding
this to an *operations-and-properties* presentation, we could say that:

* There is a map `fold`{.Agda} from $\cD(X, UY)$ to $\cC(FX, Y)$, and
* for every $f$, we have $U(\operatorname{fold} f)\eta = f$, and
* for every $f$ and $g$, if $U(g)\eta = f$, then $g = \operatorname{fold} f$.
:::

```agda
  record Free-object (X : D.Ob) : Type (adj-level C D) where
    field
      {free} : C.Ob
      unit   : D.Hom X (U.₀ free)

      fold    : ∀ {Y} (f : D.Hom X (U.₀ Y)) → C.Hom free Y
      commute : ∀ {Y} {f : D.Hom X (U.₀ Y)} → U.₁ (fold f) D.∘ unit ≡ f
      unique
        : ∀ {Y} {f : D.Hom X (U.₀ Y)} (g : C.Hom free Y)
        → U.₁ g D.∘ unit ≡ f
        → g ≡ fold f
```

<!--
```agda
    abstract
      fold-natural
        : ∀ {Y Y'} (f : C.Hom Y Y') (g : D.Hom X (U.₀ Y))
        → fold (U.₁ f D.∘ g) ≡ f C.∘ fold g
      fold-natural f g = sym (unique (f C.∘ fold g) (U.popr commute))

      fold-unit : fold unit ≡ C.id
      fold-unit = sym (unique C.id (D.eliml U.F-id))

      unique₂
        : ∀ {B} {f : D.Hom X (U.₀ B)} (g₁ g₂ : C.Hom free B)
        → U.₁ g₁ D.∘ unit ≡ f
        → U.₁ g₂ D.∘ unit ≡ f
        → g₁ ≡ g₂
      unique₂ g₁ g₂ p q = unique g₁ p ∙ sym (unique g₂ q)
```
-->

Note that *factors uniquely through $\eta$* is precisely equivalent to
saying that $\eta$ induces an equivalence between $\cD(X, UY)$ and
$\cC(FX, Y)$. In other words, free objects are representing objects for
the functor $\cD(X,U(-))$.

```agda
    fold-is-equiv : ∀ B → is-equiv (fold {B})
    fold-is-equiv B = is-iso→is-equiv λ where
      .is-iso.from f → U.₁ f D.∘ unit
      .is-iso.rinv _ → sym (unique _ refl)
      .is-iso.linv _ → commute
```

<!--
```agda
module _ {U : Functor C D} where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module U = Func U

  open Free-object
```
-->

This implies that free objects have all the usual properties of
universal constructions: they are unique up to unique isomorphism, and
identity of free objects is determined by identity of the unit maps ---
put another way, *being a free object* is truly a [[property]] of the
pair $(FX, \eta)$.

```agda
  free-object-unique : ∀ {X} (A B : Free-object U X) → A .free C.≅ B .free

  Free-object-path
    : ∀ {X} {x y : Free-object U X}
    → (p : x .free ≡ y .free)
    → (q : PathP (λ i → D.Hom X (U.₀ (p i))) (x .unit) (y .unit))
    → x ≡ y
```

<details>
<summary>The proofs follow the usual script for universal constructions,
so we will omit the details.</summary>

```agda
  free-object-unique a b =
    C.make-iso (a .fold (b .unit)) (b .fold (a .unit))
      (unique₂ b _ _ (U.popr (b .commute) ∙ a .commute) (D.eliml U.F-id))
      (unique₂ a _ _ (U.popr (a .commute) ∙ b .commute) (D.eliml U.F-id))
```

</details>

<!--
```agda
  Free-object-path {X = X} {x} {y} p q = r where
    folds
      : ∀ {Y} (f : D.Hom X (U.₀ Y))
      → PathP (λ i → C.Hom (p i) Y) (x .fold f) (y .fold f)
    folds {Y} f = to-pathp $
      let
        it : U.₁ (x .fold f) D.∘ x .unit
           ≡ U.₁ (transport (λ i → C.Hom (p i) Y) (x .fold f)) D.∘ y .unit
        it i = U.₁ (coe0→i (λ i → C.Hom (p i) Y) i (x .fold f)) D.∘ q i
      in y .unique _ (sym it ∙ x .commute)

    r : x ≡ y
    r i .free = p i
    r i .unit = q i
    r i .fold f = folds f i
    r i .commute {f = f} = is-prop→pathp
      (λ i → D.Hom-set _ _ (U.₁ (folds f i) D.∘ q i) f) (x .commute) (y .commute) i
    r i .unique {Y = Y} {f} = is-prop→pathp
      (λ i → Π-is-hlevel² {A = C.Hom (p i) Y} {B = λ g → U.₁ g D.∘ q i ≡ f} 1
        λ g _ → C.Hom-set _ _ g (folds f i))
      (x .unique) (y .unique) i

  instance
    -- This lets us ignore 'is-free-object' when proving equality.
    Extensional-Free-object
      : ∀ {X ℓr}
      → ⦃ sa : Extensional (Σ[ A ∈ C.Ob ] (D.Hom X (U.₀ A))) ℓr ⦄
      → Extensional (Free-object U X) ℓr
    Extensional-Free-object ⦃ sa = sa ⦄ .Pathᵉ x y =
      sa .Pathᵉ (_ , x .unit) (_ , y .unit)
    Extensional-Free-object ⦃ sa = sa ⦄ .reflᵉ x = sa .reflᵉ (_ , x .unit)
    Extensional-Free-object ⦃ sa = sa ⦄ .idsᵉ .to-path h =
      let p = sa .idsᵉ .to-path h
       in Free-object-path (ap fst p) (ap snd p)
    Extensional-Free-object ⦃ sa = sa ⦄ .idsᵉ .to-path-over p =
      sa .idsᵉ .to-path-over p


  private module I = Initial
  open ↓Hom
```
-->

Finally, we sketch one direction of the equivalence between our new
definition of *free object for $X$ relative to $U$* and the more
abstract construction of *initial object in the comma category $X
\swarrow U$* which we had arrived at earlier. This is simply a
re-labelling of data: it would not be hard to complete this to a full
equivalence, but it would not be very useful, either.

```agda
  free-object→universal-map
    : ∀ {X} → Free-object U X → Initial (X ↙ U)
  free-object→universal-map fo = λ where
    .I.bot → ↓obj (fo .unit)
    .I.has⊥ x .centre  → ↓hom (D.idr _ ∙ sym (fo .commute))
    .I.has⊥ x .paths p → ↓Hom-path _ _ refl $ sym $
      fo .unique _ (sym (p .com) ∙ D.idr _)
```

### Free objects and adjoints

If $U$ has a left adjoint $F$, then every $X : \cD$ has a corresponding
free object: $(FX, \eta)$, where $\eta$ is the unit of the adjunction.
This justifies our use of the notation $FX$ for a free object on $X$,
even if a functor $F(-)$ does not necessarily exist.

<!--
```agda
  module _ {F : Functor D C} (F⊣U : F ⊣ U) where
    open _⊣_ F⊣U
```
-->

```agda
    left-adjoint→free-objects : ∀ X → Free-object U X
    left-adjoint→free-objects X .free    = F .F₀ X
    left-adjoint→free-objects X .unit    = unit.η X
    left-adjoint→free-objects X .fold f  = R-adjunct F⊣U f
    left-adjoint→free-objects X .commute = L-R-adjunct F⊣U _
    left-adjoint→free-objects X .unique g p =
      Equiv.injective (_ , L-adjunct-is-equiv F⊣U) (p ∙ sym (L-R-adjunct F⊣U _))
```

Conversely, if $\cD$ has all free objects, then $U$ has a left adjoint.
We begin by constructing a functor $F : \cD \to \cC$ that assigns each
object to its free counterpart; functoriality follows from the universal
property.

<!--
```agda
  module _ (free-objects : ∀ X → Free-object U X) where
    private module F {X} where open Free-object (free-objects X) public
    open Functor
    open _=>_
    open _⊣_
```
-->

```agda
    free-objects→functor : Functor D C
    free-objects→functor .F₀ X = F.free {X}
    free-objects→functor .F₁ f = F.fold (F.unit D.∘ f)
    free-objects→functor .F-id =
      F.fold (F.unit D.∘ D.id)  ≡⟨ ap F.fold (D.idr _) ⟩
      F.fold F.unit             ≡⟨ F.fold-unit ⟩
      C.id                      ∎
    free-objects→functor .F-∘ f g =
      F.fold (F.unit D.∘ f D.∘ g)                              ≡⟨ ap F.fold (D.extendl (sym F.commute)) ⟩
      F.fold (U.₁ (F.fold (F.unit D.∘ f)) D.∘ (F.unit D.∘ g))  ≡⟨ F.fold-natural _ _ ⟩
      F.fold (F.unit D.∘ f) C.∘ F.fold (F.unit D.∘ g)          ∎
```

The unit of the adjunction is given by $\eta$, the counit by $\eps \id$,and
Both naturality and the zig-zag identities follow from some short arguments
about adjuncts.

```agda
    free-objects→left-adjoint : free-objects→functor ⊣ U
    free-objects→left-adjoint .unit .η X = F.unit {X}
    free-objects→left-adjoint .unit .is-natural X Y f = sym F.commute
    free-objects→left-adjoint .counit .η X = F.fold D.id
    free-objects→left-adjoint .counit .is-natural X Y f =
      F.fold D.id C.∘ F.fold (F.unit D.∘ U.₁ f)        ≡˘⟨ F.fold-natural _ _ ⟩
      F.fold (U.₁ (F.fold D.id) D.∘ F.unit D.∘ U.₁ f)  ≡⟨ ap F.fold (D.cancell F.commute ∙ sym (D.idr _)) ⟩
      F.fold (U.₁ f D.∘ D.id)                          ≡⟨ F.fold-natural _ _ ⟩
      f C.∘ F.fold D.id                                ∎
    free-objects→left-adjoint .zig =
      F.fold D.id C.∘ F.fold (F.unit D.∘ F.unit)        ≡˘⟨ F.fold-natural _ _ ⟩
      F.fold (U.₁ (F.fold D.id) D.∘ F.unit D.∘ F.unit)  ≡⟨ ap F.fold (D.cancell F.commute) ⟩
      F.fold F.unit                                     ≡⟨ F.fold-unit ⟩
      C.id                                              ∎
    free-objects→left-adjoint .zag = F.commute
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
    → left-adjoint→free-objects (free-objects→left-adjoint free-objects)
      ≡ free-objects
  free-objects→left-adjoint→free-objects free-objects = ext (λ x → refl)
```

This yields an equivalence between systems of free objects and left adjoints.

```agda
  free-objects≃left-adjoint
    : (∀ X → Free-object U X) ≃ (Σ[ F ∈ Functor D C ] F ⊣ U)
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

### Free objects and initiality

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
    open Initial initial renaming (bot to init)

    free-on-initial→initial
      : (F[⊥] : Free-object U init)
      → is-initial C (F[⊥] .free)
    free-on-initial→initial F[⊥] x .centre = F[⊥] .fold ¡
    free-on-initial→initial F[⊥] x .paths f =
      sym $ F[⊥] .unique f (sym (¡-unique _))
```

Conversely, if $\cC$ has an initial object $\bot_{\cC}$, then $\bot_{\cC}$
is a free object for $\bot_{\cC}$.

```agda
    is-initial→free-on-initial
      : (c-initial : Initial C)
      → Free-object U init
    is-initial→free-on-initial c-init = record
      { free    = Initial.bot c-init
      ; unit    = ¡
      ; fold    = λ _ → Initial.¡ c-init
      ; commute = ¡-unique₂ _ _
      ; unique  = λ _ _ → Initial.¡-unique₂ c-init _ _
      }
```

Note an initial object in $\cC$ does not guarantee an initial object in
$\cD$, regardless of how many free objects there are. Put syntactically,
a notion of "syntax without generators" does not imply that there is an
object of 0 generators!

## Induced adjunctions

Any adjunction $L \dashv R$ induces, in a very boring way, an *opposite* adjunction
$R\op \dashv L\op$ between `opposite functors`{.Agda ident=op}:

<!--
```agda
module _ {L : Functor (C ^op) (D ^op)} {R : Functor (D ^op) (C ^op)}
    (adj : R ⊣ L) where
  private
    module L = Functor L
    module R = Functor R
    module adj = _⊣_ adj

  open _⊣_
  open _=>_

  unop-adjunction : unopF L ⊣ unopF R
  unop-adjunction .unit .η _ = adj.ε _
  unop-adjunction .unit .is-natural x y f = sym (adj.counit.is-natural _ _ _)
  unop-adjunction .counit .η _ = adj.η _
  unop-adjunction .counit .is-natural x y f = sym (adj.unit.is-natural _ _ _)
  unop-adjunction .zig = adj.zag
  unop-adjunction .zag = adj.zig

module _ {L : Functor C D} {R : Functor D C} (adj : L ⊣ R) where
  private
    module L = Functor L
    module R = Functor R
    module adj = _⊣_ adj

  open _⊣_
  open _=>_
```
-->

```agda
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
  postcomposite-adjunction .unit .is-natural F G α = ext λ _ →
    adj.unit.is-natural _ _ _
  postcomposite-adjunction .counit .η F = cohere! (adj.counit ◂ F)
  postcomposite-adjunction .counit .is-natural F G α = ext λ _ →
    adj.counit.is-natural _ _ _
  postcomposite-adjunction .zig = ext λ _ → adj.zig
  postcomposite-adjunction .zag = ext λ _ → adj.zag

  precomposite-adjunction : precompose R {D = E} ⊣ precompose L
  precomposite-adjunction .unit .η F = cohere! (F ▸ adj.unit)
  precomposite-adjunction .unit .is-natural F G α = ext λ _ →
    sym (α .is-natural _ _ _)
  precomposite-adjunction .counit .η F = cohere! (F ▸ adj.counit)
  precomposite-adjunction .counit .is-natural F G α = ext λ _ →
    sym (α .is-natural _ _ _)
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
  L'⊣R' ._⊣_.unit   = (β.to ◆ α.to) ∘nt unit
  L'⊣R' ._⊣_.counit = counit ∘nt (α.from ◆ β.from)
  L'⊣R' ._⊣_.zig =
    (ε _ D.∘ α← D.∘ L'.₁ β←) D.∘ L'.₁ ((β→ C.∘ R.₁ α→) C.∘ η _) ≡⟨ D.pullr (D.pullr (L'.weave (C.pulll (C.cancell (β.invr ηₚ _))))) ⟩
    ε _ D.∘ α← D.∘ L'.₁ (R.₁ α→) D.∘ L'.₁ (η _)                 ≡⟨ D.extend-inner (α.from .is-natural _ _ _) ⟩
    ε _ D.∘ L.₁ (R.₁ α→) D.∘ α← D.∘ L'.₁ (η _)                  ≡⟨ D.extendl (counit.is-natural _ _ _) ⟩
    α→ D.∘ ε _ D.∘ ⌜ α← D.∘ L'.₁ (η _) ⌝                        ≡⟨ ap! (α.from .is-natural _ _ _) ⟩
    α→ D.∘ ⌜ ε _ D.∘ L.₁ (η _) D.∘ α← ⌝                         ≡⟨ ap! (D.cancell zig) ⟩
    α→ D.∘ α←                                                   ≡⟨ α.invl ηₚ _ ⟩
    D.id                                                        ∎
  L'⊣R' ._⊣_.zag =
    R'.₁ (ε _ D.∘ α← D.∘ L'.₁ β←) C.∘ ((β→ C.∘ R.₁ α→) C.∘ η _) ≡⟨ ap₂ C._∘_ refl (C.pushl (β.to .is-natural _ _ _)) ⟩
    R'.₁ (ε _ D.∘ α← D.∘ L'.₁ β←) C.∘ R'.₁ α→ C.∘ β→ C.∘ η _    ≡⟨ R'.pulll (D.pullr (D.pushl (α.from .is-natural _ _ _) ∙ D.elimr (α.invr ηₚ _))) ⟩
    R'.₁ (ε _ D.∘ L.₁ β←) C.∘ β→ C.∘ η _                        ≡⟨ C.extendl (sym (β.to .is-natural _ _ _)) ⟩
    β→ C.∘ ⌜ R.₁ (ε _ D.∘ L.₁ β←) C.∘ η _ ⌝                     ≡⟨ ap! (R.popr (sym (unit.is-natural _ _ _))) ⟩
    β→ C.∘ ⌜ R.₁ (ε _) C.∘ η _ C.∘ β← ⌝                         ≡⟨ ap! (C.cancell zag) ⟩
    β→ C.∘ β←                                                   ≡⟨ β.invl ηₚ _ ⟩
    C.id                                                        ∎

adjoint-natural-isol
  : ∀ {L L' : Functor C D} {R : Functor D C}
  → L ≅ⁿ L' → L ⊣ R → L' ⊣ R
adjoint-natural-isol α = adjoint-natural-iso α idni

adjoint-natural-isor
  : ∀ {L : Functor C D} {R R' : Functor D C}
  → R ≅ⁿ R' → L ⊣ R → L ⊣ R'
adjoint-natural-isor β = adjoint-natural-iso idni β

module _ {o h o' h'} {C : Precategory o h} {D : Precategory o' h'} where
  private module C = Precategory C

  Universal-morphism : Functor D C → C.Ob → Type _
  Universal-morphism R X = Initial (X ↙ R)

  open Free-object
  open Initial
  open ↓Obj
  open ↓Hom

  universal-map→free-object : ∀ {R X} → Universal-morphism R X → Free-object R X
  universal-map→free-object x .free = _
  universal-map→free-object x .unit = x .bot .map
  universal-map→free-object x .fold f = x .has⊥ (↓obj f) .centre .bot
  universal-map→free-object x .commute = sym (x .has⊥ _ .centre .com) ∙ C.idr _
  universal-map→free-object x .unique g p = ap bot
    (sym (x .has⊥ _ .paths (↓hom (sym (p ∙ sym (C.idr _))))))

  universal-maps→functor : ∀ {R} → (∀ X → Universal-morphism R X) → Functor C D
  universal-maps→functor u = free-objects→functor
    (λ X → universal-map→free-object (u X))

  universal-maps→left-adjoint
    : ∀ {R} (h : ∀ X → Universal-morphism R X)
    → universal-maps→functor h ⊣ R
  universal-maps→left-adjoint h = free-objects→left-adjoint _

  left-adjoint→universal-maps : ∀ {L R} → L ⊣ R → ∀ X → Universal-morphism R X
  left-adjoint→universal-maps L⊣R X =
    free-object→universal-map (left-adjoint→free-objects L⊣R X)
```
-->
