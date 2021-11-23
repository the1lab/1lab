```
open import 1Lab.Equiv.Fibrewise
open import 1Lab.HLevel.Retracts
open import 1Lab.Univalence
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module Category.Base where
```

# Precategories

In univalent mathematics, it makes sense to distinguish two stages in
the construction of categories: A **precategory** is the object that
directly corresponds to the definition of precategory as it is
traditionally formalised, whereas a **category** (or univalent category)
has an extra condition: Isomorphic objects must be identified.

```
record Precategory (o h : Level) : Type (lsuc (o ⊔ h)) where
```

A _precategory_ is a "proof-relevant preorder". In a preordered set $(A,
\le)$, the inhabitants of a set $A$ are related by a _proposition_ $a
\le b$, which is

- _reflexive_: $a \le a$
- _transitive_: $a \le b \land b \le c \to a \le c$

In a precategory, the condition that $a \le b$ be a proposition is
relaxed: A precategory has a `type of objects`{.Agda ident=Ob} and, between
each $x, y$, a **set** $\mathrm{Hom}(x, y)$ of relations (or maps). The
name Hom is historical and it betrays the original context in which
categories where employed: algebra(ic topology), where the maps in
question are **hom**omorphisms.

```
  field
    Ob  : Type o
    Hom : Ob → Ob → Type h
```

Whereas reading a classical definition into a type theory where equality
is a proposition, the word **set** may be read to just mean [inhabitant
of a universe](agda://1Lab.Type). But in HoTT, if we want categories to
be well-behaved, we do actually mean _set_: A type of
[h-level](agda://1Lab.HLevel) 2.

```
  field
    Hom-set : (x y : Ob) → isSet (Hom x y)
```

If you are already familiar with the definition of precategory there are
two things to note here:

First is that out formalization has a _family_ of `Hom`{.Agda}-sets
rather than a single `Hom`{.Agda}-set and source/target maps. This
formulation is not unique to precategory theory done internally to type
theory, but it is the most reasonable way to formulate things in this
context.

Second is that the word "set" in the definition of Hom-set has nothing
to do with "size". Indeed, the "set"/"not a set" (alternatively
"small"/"large") distinction makes no sense in type theory (some may
argue it makes no sense in general).

Instead, the `Precategory`{.Agda} record is parametrised by two levels:
`o`, and `h`. The type of objects has to fit in the universe `Type o`,
and the family of Hom-sets is `Type h` valued. As an example, the thin
precategory corresponding to the natural numbers with their usual ordering
would live in `Precategory lzero lzero`.

This means, for instance, that there is no single "category of sets" -
there is a _family_ of categories of sets, parametrised by the level in
which its objects live.

```
  field
    id  : {x : _}     → Hom x x
    _∘_ : {x y z : _} → Hom y z → Hom x y → Hom x z

  infixr 40 _∘_
```

The "proof-relevant" version of the reflexivity and transitivity laws
are, respectively, the `identity morphisms`{.Agda} and `composition of
morphisms`{.Agda ident="_∘_"}. Unlike in the proof-irrelevant case, in
which an inhabitant of $x \le y$ just says two things are related, these
operations _matter_, and thus must satisfy laws:
  
```
  field
    idr : {x y : _} (f : Hom x y) → f ∘ id ≡ f
    idl : {x y : _} (f : Hom x y) → id ∘ f ≡ f
```

The two identity laws say that the identity morphisms serve as neutral
elements for the composition operation, both on the left and on the
right. The "two" associativity laws (below) say that both ways of writing
parentheses around a composition of three morphisms is equal: $(f \circ
g) \circ h = f \circ (g \circ h)$.
    
```
    assoc : {w x y z : _} (f : Hom y z) (g : Hom x y) (h : Hom w x)
          → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
```

## Opposites

A common theme throughout precategory theory is that of _duality_: The dual
of a categorical concept is same concept, with "all the arrows
inverted". To make this formal, we introduce the idea of _opposite
categories_: The opposite of $C$, written $C^{op}$, has the same
`objects`{.Agda}, but with $\mathrm{Hom}_{C^{op}}(x, y) =
\mathrm{Hom}_{C}(y, x)$.

```
infixl 60 _^op
_^op : {o₁ h₁ : _} → Precategory o₁ h₁ → Precategory o₁ h₁
(C ^op) .Precategory.Ob = Precategory.Ob C
(C ^op) .Precategory.Hom x y = Precategory.Hom C y x
(C ^op) .Precategory.Hom-set x y = Precategory.Hom-set C y x
(C ^op) .Precategory.id = Precategory.id C
(C ^op) .Precategory._∘_ f g = Precategory._∘_ C g f
```

Composition in the opposite precategory $C^{op}$ is "backwards" with
respect to $C$: $f \circ_{op} g = g \circ f$. This inversion, applied
twice, ends up equal to what we started with by the nature of
computation - An equality that arises like this, automatically from what
Agda computes, is called _definitional_.

```
(C ^op) .Precategory.idl x = C .Precategory.idr x
(C ^op) .Precategory.idr x = C .Precategory.idl x
```

The left and right identity laws are swapped for the construction of the
opposite precategory: For `idr`{.Agda} one has to show $f \circ_{op}
\mathrm{id} = f$, which computes into having to show that $\mathrm{id}
\circ_op{f} = f$. The case for `idl`{.Agda} is symmetric.

```
(C ^op) .Precategory.assoc f g h i = Precategory.assoc C h g f (~ i)
```

For associativity, consider the case of `assoc`{.Agda} for the
opposite precategory $C^{op}$. What we have to show is - by the type of
`assoc₁`{.Agda} - $f \circ_{op} (g \circ_{op} h) = (f \circ_{op} g)
\circ_{op} h$. This computes into $(h \circ g) \circ f = h \circ (g
\circ f)$ - which is exactly what `sym (assoc C h g f)` shows!

Taking opposite categories is an involution. Since `sym (sym p) = p` by
definition, taking opposite categories is also definitionally
involutive.

```
_ : {o₁ h₁ : _} {C : Precategory o₁ h₁} → (C ^op) ^op ≡ C
_ = refl
```

# Categories

Just like a partial order is a preorder where $x \le y \and y \le x \to
x = y$, a **category** is a precategory where isomorphic objects are
identified. This is a generalisation of the univalence axiom to
arbitrary categories, and, indeed, it's phrased in the same way: asking
for a canonically defined map to be an equivalence.

```
_[_≅_] : {o h : _} (C : Precategory o h) (a b : Precategory.Ob C) → Type h
```

First, we have to define what it means for two objects in a category to
be isomorphic. This is the same thing as an [isomorphism of sets], but
with morphisms instead of functions: Morphisms in either direction, such
that both ways of composing them are the identity.

[isomorphism of sets]: agda://1Lab.Equiv#Iso

```
_[_≅_] C a b =
  Σ[ fg ∈ C.Hom a b × C.Hom b a ]
  Σ[ _ ∈ (fg .fst) C.∘ (fg .snd) ≡ C.id ]
  (fg .snd C.∘ fg .fst ≡ C.id)
  where module C = Precategory C

idIso : {o h : _} {C : Precategory o h} {a : Precategory.Ob C}
      → C [ a ≅ a ]
idIso {C = C} = (C.id , C.id) , C.idl _ , C.idl _
  where module C = Precategory C
```

A precategory is a category precisely when the type `(Σ[ B ∈ _ ] C [ A ≅
B ])` is contractible. This implies that the type `A ≡ B` is equivalent
to the type `C [ A ≃ B ]`, for any pair of objects `A`, `B` in the
category. This is because `Σ[ B ∈ _ ] (A ≡ _)` is also contractible.
Further, the type `C [ A ≃ B ]` satisfies J, by the same argument used
to construct `EquivJ`{.Agda}.

```
isCategory : {o h : _} → Precategory o h → Type _
isCategory C = {A : _} → isContr (Σ[ B ∈ _ ] C [ A ≅ B ])
```

This notion of univalent category corresponds to the usual notion ---
which is having the canonical map from paths to isomorphisms be an
equivalence --- by the following argument: Since the types `(Σ[ B ∈ _ ]
C [ A ≅ B ])` and `Σ[ B ∈ _ ] A ≣ B`, the action of `pathToIso`{.Agda}
on total spaces is an equivalence; Hence `pathToIso` is an equivalence.

```
pathToIso : {o h : _} {C : Precategory o h} {A : Precategory.Ob C} {B : Precategory.Ob C}
          → A ≡ B → C [ A ≅ B ]
pathToIso {C = C} {A = A} = J (λ B p → C [ A ≅ B ]) (idIso {C = C})
```

First we define, exactly as in the book, the canonical map `pathToIso`{.Agda}.

```
isCategory→isEquiv-pathToIso
  : {o h : _} {C : Precategory o h}
  → isCategory C → {A B : _}
  → isEquiv (pathToIso {C = C} {A = A} {B = B})
isCategory→isEquiv-pathToIso {C = C} iscat {A} {B} = total→equiv isEquiv-total where
  P Q : Precategory.Ob C → Type _
  P B = A ≡ B
  Q B = C [ A ≅ B ]
```

We consider the map `pathToIso`{.Agda} as a [fibrewise equivalence]
between the two families `A ≡ -` and `C [ A ≅ - ]`. This lets us reduce
the problem of proving that `pathToIso`{.Agda} is an equivalence to the
problem of proving that it induces an equivalence of total spaces.

[fibrewise equivalence]: agda://1Lab.Equiv.Fibrewise

```
  isEquiv-total : isEquiv (total {P = P} {Q = Q} (λ A p → pathToIso {C = C} p))
  isEquiv-total =
    isContr→isEquiv (contr (A , λ i → A) isContr-Singleton)
                    iscat
```

Since the total spaces are contractible (`Σ P` by `path induction`{.Agda
ident=J}, `Σ Q` by the assumption that C is a category) [any map between
them is an equivalence](agda://1Lab.Equiv#isContr→isEquiv). This implies
that we can turn categorical isomorphisms into paths of objects:

```
isCategory→isoToPath : {o h : _} {C : Precategory o h}
                     → isCategory C
                     → {A B : _}
                     → C [ A ≅ B ]
                     → A ≡ B
isCategory→isoToPath {C = C} cat =
  isEquiv→isIso (isCategory→isEquiv-pathToIso {C = C} cat) .isIso.g
```

Furthermore, we have that this function is an equivalence, and so the
type of objects in a univalent category is at most a [groupoid]. We use
the fact that [h-levels are closed under equivalences] and that
[dependent sums preserve h-levels].

[h-levels are closed under equivalences]: agda://1Lab.HLevel.Retracts#isHLevel-equiv
[dependent sums preserve h-levels]: agda://1Lab.HLevel.Retracts#isHLevelΣ
[groupoid]: agda://1Lab.HLevel#isGroupoid

```
isCategory→isGroupoid-Ob : {o h : _} {C : Precategory o h}
                         → isCategory C
                         → isGroupoid (C .Precategory.Ob)
isCategory→isGroupoid-Ob {C = C} iscat x y =
  isHLevel-equiv 2
    (isCategory→isoToPath {C = C} iscat)
    (((_ , isCategory→isEquiv-pathToIso {C = C} iscat) e¯¹) .snd)
```

Since `an isomorphism`{.Agda ident=_[_≅_]} is a big dependent sum of
[sets], we have that the paths `x ≡ y` are a set, and so `C` is a
groupoid.

[sets]: agda://1Lab.HLevel#isSet


```
    (isHLevelΣ 2
      (isHLevelΣ 2
        (C.Hom-set _ _) λ _ → C.Hom-set _ _)
        λ { (f , g) →
            isProp→isSet (isHLevelΣ 1 (C.Hom-set _ _ _ _)
                                      λ _ → C.Hom-set _ _ _ _) })
  where module C = Precategory C
```

## The category of Sets

Given a [universe level], we can consider the collection of [all sets]
of that level. This assembles into a `precategory`{.Agda
ident=Precategory} quite nicely, since functions preserve h-levels.

[universe level]: agda://1Lab.Type
[all sets]: agda://1Lab.HLevel#Set

```
module _ where
  open Precategory

  Sets : (o : _) → Precategory (lsuc o) o
  Sets o .Ob = Set o
  Sets o .Hom A B = A .fst → B .fst
  Sets o .Hom-set _ (B , bset) f g p q i j a =
    bset (f a) (g a) (happly p a) (happly q a) i j
  Sets o .id x = x
  Sets o ._∘_ f g x = f (g x)
  Sets o .idl f = refl
  Sets o .idr f = refl
  Sets o .assoc f g h = refl
```

Furthermore, Sets is a univalent category, essentially by the same
argument used to prove [EquivJ].

[EquivJ]: agda://1Lab.Univalence#EquivJ

```
  Sets-category : {o : _} → isCategory (Sets o)
  Sets-category {o = o} {A = a} .centre = a , idIso {C = Sets o} {a = a}
```

We take the centre of contraction to be the object itself, together with
the identity isomorphism. Given any other object and isomorphism, we can
use `ua`{.Agda} to get a path `a ≡ b`, and it's not too hard - but quite
tedious - to prove that the other isomorphism is equal to the identity
isomorphism [over] ua.

[over]: 1Lab.Path.html#dependent-paths

```
  Sets-category {o = o} {A = a} .paths (b , isiso) =
    Σ-Path
      (Σ-Path (ua eqv) (isProp-isHLevel 2 _ _))
      (Σ-Path (λ i → (λ x → transp (λ i → b .fst) i
                              (isiso .fst .fst (transp (λ i → a .fst) i x)))
                   , (λ x → transp (λ i → a .fst) i
                              (isiso .fst .snd (transp (λ i → b .fst) i x))))
```

The functions that make up the isomorphism are equal essentially by a
[transport filler], and the data that proves this is an isomorphism does
not matter since `hom-sets are sets`{.Agda ident=Hom-set}.

[transport filler]: agda://1Lab.Path#transport-filler

```
              (Σ-Path (isHLevelΠ 2 (λ _ → b .snd) _ _ _ _)
                      (isHLevelΠ 2 (λ _ → a .snd) _ _ _ _)))
    where
      eqv : a .fst ≃ b .fst
      eqv = Iso→Equiv ( isiso .fst .fst
                      , iso (isiso .fst .snd)
                          (happly (isiso .snd .fst))
                          (happly (isiso .snd .snd)))
```