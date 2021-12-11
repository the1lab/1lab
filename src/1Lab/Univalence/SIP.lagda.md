---
description: |
  The structure identity principle characterises equality in
  "types-with-structure" as being exactly the equivalences that preserve
  that structure. In a sense, it augments univalence with the notion of
  preservation of structure.
---

```agda
open import 1Lab.Data.Sigma.Properties
open import 1Lab.Data.Pi.Properties
open import 1Lab.Equiv.Embedding
open import 1Lab.Path.Groupoid
open import 1Lab.Univalence
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Univalence.SIP where
```

# Structure Identity Principle

In mathematics in general, it's often _notationally_ helpful to identify
isomorphic _structures_ (e.g.: groups) in a proof. However, when this
mathematics is done using material set theory as a foundations, this
identification is merely a shorthand --- nothing _prevents_ you from
distinguishing isomorphic groups in ZFC by, for instance, asking about
membership of a particular set in the underlying set of each group.

In univalent mathematics, it's a theorem that no family of types can
distinguish between isomorphic structures.  [Univalence] is this
statement, but for _types_. For structures built out of types, it seems
like we would need a bit more power, but in reality, we don't!

[Univalence]: 1Lab.Univalence.html

The idea of the structure identity principle is that we can describe,
generically, a **structure on a type** by a map `S : Type → Type`. Types
equipped with this structure are then represented by the [total space]
`Σ S`. 

[total space]: agda://1Lab.Type#Σ

```agda
record
  Structure
    {ℓ₁ ℓ₂}
    (ℓ₃ : _)
    (S : Type ℓ₁ → Type ℓ₂)
  : Type (lsuc (ℓ₁ ⊔ ℓ₃) ⊔ ℓ₂)
  where field
```

In reality, a `Structure`{.Agda} also comes with a notion of
_homomorphism_: those functions between the underlying types which
preserve the structure. For example, if `S` = groups, then
`is-hom`{.Agda} would be the predicate representing "f is a group
homomorphism".

```agda
   is-hom : (A B : Σ S) → (A .fst → B .fst) → Type ℓ₃

open Structure public
```

<!--
```
private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A : Type ℓ
  S T : Type ℓ → Type ℓ₁

TypeWith : Structure ℓ₁ S → Type _
TypeWith {S = S} _ = Σ S
```
-->

A structure is said to be **univalent** if a homomorphic equivalence of
structures `A`, `B` induces a path of the structures, over the
univalence axiom:

```
isUnivalent : Structure ℓ S → Type _
isUnivalent {S = S} ι =
  ∀ {X Y}
  → (f : X .fst ≃ Y .fst)
  → ι .is-hom X Y (fst f) ≃ PathP (λ i → S (ua f i)) (X .snd) (Y .snd)
```

There are also abbreviations for referring to an equivalence of
structures (i.e. an equivalence with homomorphic underlying map) and a
homomorphism of structures (i.e. an arbitrary map).

```agda
_≃[_]_ : Σ S → Structure ℓ S → Σ S → Type _
A ≃[ σ ] B =
  Σ[ f ∈ A .fst ≃ B .fst ]
   (σ .is-hom A B (f .fst))

_[_⇒_] : Structure ℓ S → Σ S → Σ S → Type _
σ [ A ⇒ B ] = Σ[ f ∈ (A .fst → B .fst) ] (σ .is-hom A B f)
```

## The principle

The **structure identity principle** says that, if `S` is a `univalent
structure`{.Agda ident=isUnivalent}, then the path space of `Σ S` is equivalent
to the space of S-homomorphic equivalences of types. Again using groups
as a grounding example: equality of groups is group isomorphism.

```
SIP : {σ : Structure ℓ S} → isUnivalent σ → {X Y : Σ S} → (X ≃[ σ ] Y) ≃ (X ≡ Y)
SIP {S = S} {σ = σ} is-univ {X} {Y} =
  X ≃[ σ ] Y                                                       ≃⟨⟩
  Σ[ e ∈ X .fst ≃ Y .fst ] (σ .is-hom X Y (fst e))                 ≃⟨ Σ-ap (ua , univalence¯¹) is-univ ⟩
  Σ[ p ∈ X .fst ≡ Y .fst ] PathP (λ i → S (p i)) (X .snd) (Y .snd) ≃⟨ Iso→Equiv Σ-PathP-iso ⟩
  (X ≡ Y)                                                          ≃∎

sip : {σ : Structure ℓ S} → isUnivalent σ → {X Y : Σ S} → (X ≃[ σ ] Y) → (X ≡ Y)
sip σ = SIP σ .fst
```

# Structure Combinators

Structures can be built up in an algebraic manner through the use of
_structure combinators_. These express closure of structures under a
number of type formers. For instance, if `S` and `T` are univalent
structures, then so is `λ X → S X → T X`.

The simplest case of a structure is the _constant structure_, which is
what you get when you equip a type `X` with a choice of inhabitant of
some other type `Y`, unrelated to `X`. Since the given function is `f :
A → B`, it can't act on `T`, so the notion of homomorphism is
independent of `f`.

```
constantStr : (A : Type ℓ) → Structure {ℓ₁} ℓ (λ X → A)
constantStr T .is-hom (A , x) (B , y) f = x ≡ y

constantStr-univalent : {A : Type ℓ} → isUnivalent (constantStr {ℓ₁ = ℓ₁} A)
constantStr-univalent f = _ , idEquiv
```

The next simplest case is considering the identity function as a
structure. In that case, the resulting structured type is that of a
_pointed type_:

```
pointedStr : Structure ℓ (λ X → X)
pointedStr .is-hom (A , x) (B , y) f = f x ≡ y
```

This is univalent by `uaPathP≃Path`{.Agda}, which says `PathP (ua f) x
y` is equivalent to `f .fst x ≡ y`.

```
pointedStr-univalent : isUnivalent (pointedStr {ℓ})
pointedStr-univalent f = uaPathP≃Path _
```

If `S` and `T` are univalent structures, then so is their pointwise
product. The notion of a `S × T`-homomorphism is that of a function
homomorphic for both `S` and `T`, simultaneously:

```
productStr : Structure ℓ S → Structure ℓ₂ T → Structure _ (λ X → S X × T X)
productStr S T .is-hom (A , x , y) (B , x' , y') f =
  S .is-hom (A , x) (B , x') f × T .is-hom (A , y) (B , y') f

productStr-univalent : {σ : Structure ℓ₁ S} {τ : Structure ℓ₂ T}
                     → isUnivalent σ → isUnivalent τ
                     → isUnivalent (productStr σ τ)
productStr-univalent {S = S} {T = T} {σ = σ} {τ} θ₁ θ₂ {X , x , y} {Y , x' , y'} f =
  (σ .is-hom (X , x) (Y , x') _ × τ .is-hom (X , y) (Y , y') _) ≃⟨ Σ-ap (θ₁ f) (λ _ → θ₂ f) ⟩
  (PathP _ _ _ × PathP _ _ _)                                   ≃⟨ Iso→Equiv Σ-PathP-iso ⟩
  PathP (λ i → S (ua f i) × T (ua f i)) (x , y) (x' , y')       ≃∎
```

If `S` and `T` are univalent structures, then so are the families of
functions between them:

```
functionStr : Structure ℓ₁ S → Structure ℓ₂ T → Structure _ (λ X → S X → T X)
functionStr {S = S} σ τ .is-hom (A , f) (B , g) h =
  {s : S A} {t : S B} → σ .is-hom (A , s) (B , t) h
                      → τ .is-hom (A , f s) (B , g t) h

functionStr-univalent : {σ : Structure ℓ₁ S} {τ : Structure ℓ₂ T}
                      → isUnivalent σ → isUnivalent τ
                      → isUnivalent (functionStr σ τ)
functionStr-univalent {S = S} {T = T} {σ = σ} {τ} θ₁ θ₂ eqv =
  Π-impl-cod≃ (λ s → Π-impl-cod≃ λ t → function≃ (θ₁ eqv) (θ₂ eqv)) ∙e funextDep≃
```

# Example: $\infty$-magmas

We provide an example of applying the SIP, and the structure
combinators: **$\infty$-magmas**. Recall that a [magma] is a [Set]
equipped with a binary operation, with no further conditions imposed. In
HoTT, we can relax this even further: An $\infty$-magma is a
`Type`{.Agda} - that is, an $\infty$-groupoid - equipped with a binary
operation.

[magma]: https://ncatlab.org/nlab/show/magma
[Set]: agda://1Lab.HLevel#Set

```agda
private
  binop : Type → Type
  binop X = X → X → X
```

We can impose a `Structure`{.Agda} on `binop`{.Agda} by applying nested
`functionStr`{.Agda} and `pointedStr`{.Agda}. Since this structure is
built out of structure combinators, it's automatically univalent:

```
  ∞-Magma : Structure lzero binop
  ∞-Magma = functionStr pointedStr (functionStr pointedStr pointedStr)

  ∞-Magma-univ : isUnivalent ∞-Magma
  ∞-Magma-univ =
    functionStr-univalent {τ = functionStr pointedStr pointedStr}
      pointedStr-univalent
      (functionStr-univalent {τ = pointedStr}
        pointedStr-univalent
        pointedStr-univalent)
```

The type of `∞-Magma`{.Agda} homomorphisms generated by this equivalence
is slightly inconvenient: Instead of getting $f (x \star y) = f x * f
y$, we get something that is parameterised over two paths:

```
  _ : {A B : TypeWith ∞-Magma} {f : A .fst → B .fst}
    → ∞-Magma .is-hom A B f
    ≡ ( {s : A .fst} {t : B .fst} → f s ≡ t
      → {x : A .fst} {y : B .fst} → f x ≡ y
      → f (A .snd s x) ≡ B .snd t y)
  _ = refl
```

This condition, although it looks a lot more complicated, is essentially
the same as the standard notion:

```
  fixup : {A B : TypeWith ∞-Magma} {f : A .fst → B .fst}
        → ((x y : A .fst) → f (A .snd x y) ≡ B .snd (f x) (f y))
        → ∞-Magma .is-hom A B f
  fixup {A = A} {B} {f} path {s} {t} p {s₁} {t₁} q =
    f (A .snd s s₁)     ≡⟨ path _ _ ⟩
    B .snd (f s) (f s₁) ≡⟨ ap₂ (B .snd) p q ⟩
    B .snd t     t₁     ∎
```

As an example, we equip the type of booleans with two ∞-magma
structures, one given by conjunction, one by disjunction, and prove that
`not`{.Agda} makes them equal as ∞-magmas:

<div class=mathpar>
```agda
  open import 1Lab.Data.Bool
```
</pre></div>

<div class=mathpar>
```agda
  Conj : TypeWith ∞-Magma
  Conj .fst = Bool
  Conj .snd false false = false
  Conj .snd false true  = false
  Conj .snd true  false = false
  Conj .snd true  true  = true
```

```agda
  Disj : TypeWith ∞-Magma
  Disj .fst = Bool
  Disj .snd false false = false
  Disj .snd false true  = true
  Disj .snd true  false = true
  Disj .snd true  true  = true
```
</div>

I claim that `not`{.Agda} is a $\infty$-magma isomorphism between
`Conj`{.Agda} and `Disj`{.Agda}:

```agda
  not-iso : Conj ≃[ ∞-Magma ] Disj
  not-iso .fst = not , isEquiv-not
  not-iso .snd = fixup {A = Conj} {B = Disj} λ where
    false false → refl
    false true → refl
    true false → refl
    true true → refl
```

It's not clear that this should be the case, especially since the case
analysis obfuscates the result further. However, writing $\land$ and
$\lor$ for the actions of `Conj`{.Agda} and `Disj`{.Agda} (as one
should!), then we see that `not-iso`{.Agda} says exactly that

$$
\neg (x \land y) = \neg x \lor \neg y
$$

From this and the SIP we get that `Conj`{.Agda} and `Disj`{.Agda} are the same
$\infty$-magma:

```agda
  Conj≡Disj : Conj ≡ Disj
  Conj≡Disj = sip ∞-Magma-univ not-iso
```

# Adding Axioms

Most mathematical objects of interest aren't merely sets with structure.
More often, the objects we're interested in have _stuff_ (the underlying
type), _structure_ (such as a `SNS`{.Agda}), and _properties_ - for
instance, equations imposed on the structure. A concrete example may
help:

- A **pointed $\infty$-magma** is a pointed type equipped with a binary
operation;

- A **monoid** is a pointed $\infty$-magma with additional data
witnessing that a) the type is a set; b) the operation is associative;
and c) the point acts as a left- and right- identity for the operation.

Fortunately, the SIP again applies here: If you augment a standard
notion of structure with _axioms_, then equality of structures with
axioms is still isomorphism of the underlying structures. For this, we
require that the axioms be [valued in propositions](agda://1Lab.HLevel#isProp).

```agda
module _
  {σ : Structure ℓ S}
  (univ : isUnivalent σ)
  (axioms : (X : _) → S X → Type ℓ₃)
  where
```

First, the notion of structure that you get is just a lifting of the
underlying structure `σ` to ignore the witnesses for the axioms:

```
  axiomsStr : Structure ℓ (λ X → Σ[ s ∈ S X ] (axioms X s))
  axiomsStr .is-hom (A , s , a) (B , t , b) f =
    σ .is-hom (A , s) (B , t) f
```

Then, if the axioms are propositional, a calculation by equivalence
reasoning concludes what we wanted: `axiomsStr`{.Agda} is univalent.

```
  module _ (axioms-prop : ∀ {X} {s} → isProp (axioms X s)) where
    axiomsStr-univalent : isUnivalent axiomsStr
    axiomsStr-univalent {X = A , s , a} {Y = B , t , b} f =
      σ .is-hom (A , s) (B , t) (f . fst)
        ≃⟨ univ f ⟩
      PathP (λ i → S (ua f i)) s t 
        ≃⟨ Σ-contract (λ x → isHLevelPathP 0 (contr b (axioms-prop b))) e¯¹ ⟩
      Σ[ p ∈ PathP (λ i → S (ua f i)) s t ] PathP (λ i → axioms (ua f i) (p i)) a b
        ≃⟨ Iso→Equiv Σ-PathP-iso ⟩
      _ 
        ≃∎
```

A very useful consequence of the SIP is that axioms can be lifted from
equivalent underlying structures. For instance: $\mathbb{N}$ can be
defined as both unary numbers (the construction of `Nat`{.Agda}), or as binary
numbers. If you prove that `Nat`{.Agda} is a monoid, and `Nat ≃ Bin` as
pointed ∞-magmas, then `Bin` inherits the monoid structure.

```
transferAxioms 
  : {σ : Structure ℓ S} {univ : isUnivalent σ}
    {axioms : (X : _) → S X → Type ℓ₃}
  → (A : TypeWith (axiomsStr univ axioms)) (B : TypeWith σ)
  → (A .fst , A .snd .fst) ≃[ σ ] B
  → axioms (B .fst) (B .snd)
transferAxioms {univ = univ} {axioms = axioms} A B eqv =
  subst (λ { (x , y) → axioms x y }) (sip univ eqv) (A .snd .snd)
```