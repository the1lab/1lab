---
description: |
  The structure identity principle characterises identifications in
  "types-with-structure" as being exactly the equivalences that preserve
  that structure. In a sense, it augments univalence with the notion of
  preservation of structure.
---

<!--
```agda
open import 1Lab.Type.Sigma
open import 1Lab.Univalence
open import 1Lab.Type.Pi
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
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

"Structure Identity Principle" is the name for several related theorems
in Homotopy Type Theory, which generically say that "paths on a
structure are isomorphisms of that structure".

For instance, the version in the HoTT Book says that if a structure `S`
on the objects of a [[univalent category]] `S` can be described in a certain
way, then the category of `S`-structured objects of `C` is univalent. As
a benefit, the Book version of the SIP characterises the _homomorphisms_
of `S`-structures, not just the _isomorphisms_. As a downside, it only
applies to [[set-level|set]] structures.

```agda
record
  Structure {ℓ₁ ℓ₂} (ℓ₃ : _) (S : Type ℓ₁ → Type ℓ₂) : Type (lsuc (ℓ₁ ⊔ ℓ₃) ⊔ ℓ₂)
  where

  constructor HomT→Str
  field
```

The material on this page, especially the definition of
`is-univalent`{.Agda} and `is-transport-str`{.Agda}, is adapted from
<cite>[Internalizing Representation Independence with
Univalence]</cite>. The SIP formalised here says, very generically, that
a `Structure`{.Agda} is a family of types `S : Type → Type`, and a `type
with`{.Agda ident=Type-with} structure is an inhabitant of the `total
space`{.Agda ident=Σ} `Σ S`.

[Internalizing Representation Independence with Univalence]: https://arxiv.org/abs/2009.05547

What sets a `Structure`{.Agda} apart from a type family is a notion of
_homomorphic equivalence_: Given an equivalence of the underlying types,
the predicate `is-hom (A , x) (B , y) eqv` should represent what it
means for `eqv` to take the `x`-structure on `A` to the `y`-structure on
`B`.

```agda
   is-hom : (A B : Σ _ S) → (A .fst ≃ B .fst) → Type ℓ₃
```

As a grounding example, consider equipping types with group structure:
If `(A , _⋆_)` and `(B , _*_)` are types with group structure (with many
fields omitted!), and `f : A → B` is the underlying map of an
equivalence `A ≃ B`, then `is-hom`{.Agda} would be $\forall (x y\colon
A) f(x \star y) = f(x) * f(y)$ - the "usual" definition of group
homomorphism.

```agda
open Structure public

Type-with : ∀ {ℓ ℓ₁ ℓ₂} {S : Type ℓ → Type ℓ₁} → Structure ℓ₂ S → Type _
Type-with {S = S} _ = Σ _ S
```

<!--
```agda
private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A : Type ℓ
  S T : Type ℓ → Type ℓ₁
```
-->

A structure is said to be **univalent** if a homomorphic equivalence of
structures `A`, `B` induces a path of the structures, over the
[[univalence axiom]] --- that is, if `is-hom`{.Agda} agrees with what it
means for "S X" and "S Y" to be identified, where this identification is
dependent on one induced by univalence.

```agda
is-univalent : Structure ℓ S → Type _
is-univalent {S = S} ι =
  ∀ {X Y}
  → (f : X .fst ≃ Y .fst)
  → ι .is-hom X Y f ≃ PathP (λ i → S (ua f i)) (X .snd) (Y .snd)
```

The notation `A ≃[ σ ] B`{.Agda ident=_≃[_]_} stands for the type of
σ-homomorphic equivalences, i.e. those equivalences of the types
underlying `A` and `B` that σ identifies as being homomorphic.

```agda
_≃[_]_ : Σ _ S → Structure ℓ S → Σ _ S → Type _
A ≃[ σ ] B =
  Σ[ f ∈ A .fst ≃ B .fst ]
   (σ .is-hom A B f)
```

## The principle

The **structure identity principle** says that, if `S` is a `univalent
structure`{.Agda ident=is-univalent}, then the path space of `Σ S` is
equivalent to the space of S-homomorphic equivalences of types. Again
using groups as a grounding example: identification of groups is group
isomorphism.

```agda
SIP : {σ : Structure ℓ S} → is-univalent σ → {X Y : Σ _ S} → (X ≃[ σ ] Y) ≃ (X ≡ Y)
SIP {S = S} {σ = σ} is-univ {X} {Y} =
  X ≃[ σ ] Y                                                       ≃⟨⟩
  Σ[ e ∈ X .fst ≃ Y .fst ] (σ .is-hom X Y e)                       ≃⟨ Σ-ap (ua , univalence⁻¹) is-univ ⟩
  Σ[ p ∈ X .fst ≡ Y .fst ] PathP (λ i → S (p i)) (X .snd) (Y .snd) ≃⟨ Iso→Equiv Σ-pathp-iso ⟩
  (X ≡ Y)                                                          ≃∎
```

The proof of the `SIP`{.Agda} follows essentially from
`univalence`{.Agda ident=univalence⁻¹}, and the fact that `Σ types
respect equivalences`{.Agda ident=Σ-ap}. In one fell swoop, we convert
from the type of homomorphic equivalences to a dependent pair of paths.
By the characterisation of `path spaces of Σ types`{.Agda
ident=Σ-pathp-iso}, this latter pair is equivalent to `X ≡ Y`.

```agda
sip : {σ : Structure ℓ S} → is-univalent σ → {X Y : Σ _ S} → (X ≃[ σ ] Y) → (X ≡ Y)
sip σ = SIP σ .fst
```

# Structure combinators

Univalent structures can be built up in an algebraic manner through the
use of _structure combinators_. These express closure of structures
under a number of type formers. For instance, if `S` and `T` are
univalent structures, then so is `λ X → S X → T X`.

The simplest case of univalent structure is the _constant structure_,
which is what you get when you equip a type `X` with a choice of
inhabitant of some other type `Y`, unrelated to `X`. Since the given
function is `f : A → B`, it can't act on `T`, so the notion of
homomorphism is independent of `f`.

```agda
Constant-str : (A : Type ℓ) → Structure {ℓ₁} ℓ (λ X → A)
Constant-str T .is-hom (A , x) (B , y) f = x ≡ y

Constant-str-univalent : {A : Type ℓ} → is-univalent (Constant-str {ℓ₁ = ℓ₁} A)
Constant-str-univalent f = _ , id-equiv
```

The next simplest case is considering the identity function as a
structure. In that case, the resulting structured type is that of a
_pointed type_, whence the name `Pointed-str`{.Agda}.

The name `Pointed-str`{.Agda} breaks down when it is used with some of
the other combinators: A type equipped with the `product`{.Agda
ident=Product-str} of two `pointed structures`{.Agda ident=Pointed-str} is
indeed a "bipointed structure", but a type equipped with `maps
between`{.Agda ident=Function-str} two `pointed structures`{.Agda
ident=Pointed-str} is a type equipped with an endomorphism, which does
not necessitate a point.

```agda
Pointed-str : Structure ℓ (λ X → X)
Pointed-str .is-hom (A , x) (B , y) f = f .fst x ≡ y
```

This is univalent by `ua-pathp≃path`{.Agda}, which says `PathP (ua f) x
y` is equivalent to `f .fst x ≡ y`.

```agda
Pointed-str-univalent : is-univalent (Pointed-str {ℓ})
Pointed-str-univalent f = ua-pathp≃path _
```

If `S` and `T` are univalent structures, then so is their pointwise
product. The notion of a `S × T`-homomorphism is that of a function
homomorphic for both `S` and `T`, simultaneously:

```agda
Product-str : Structure ℓ S → Structure ℓ₂ T → Structure _ (λ X → S X × T X)
Product-str S T .is-hom (A , x , y) (B , x' , y') f =
  S .is-hom (A , x) (B , x') f × T .is-hom (A , y) (B , y') f

Product-str-univalent : {σ : Structure ℓ₁ S} {τ : Structure ℓ₂ T}
                      → is-univalent σ → is-univalent τ
                      → is-univalent (Product-str σ τ)
Product-str-univalent {S = S} {T = T} {σ = σ} {τ} θ₁ θ₂ {X , x , y} {Y , x' , y'} f =
  (σ .is-hom (X , x) (Y , x') _ × τ .is-hom (X , y) (Y , y') _) ≃⟨ Σ-ap (θ₁ f) (λ _ → θ₂ f) ⟩
  (PathP _ _ _ × PathP _ _ _)                                   ≃⟨ Iso→Equiv Σ-pathp-iso ⟩
  PathP (λ i → S (ua f i) × T (ua f i)) (x , y) (x' , y')       ≃∎
```

If `S` and `T` are univalent structures, then so are the families of
functions between them. For reasons we'll see below, this is called
`Str-function-str`{.Agda} (a rather redundant name!) instead of
`Function-str`{.Agda}.

```agda
Str-function-str : Structure ℓ₁ S → Structure ℓ₂ T → Structure _ (λ X → S X → T X)
Str-function-str {S = S} σ τ .is-hom (A , f) (B , g) h =
  {s : S A} {t : S B} → σ .is-hom (A , s) (B , t) h
                      → τ .is-hom (A , f s) (B , g t) h

Str-function-str-univalent : {σ : Structure ℓ₁ S} {τ : Structure ℓ₂ T}
                           → is-univalent σ → is-univalent τ
                           → is-univalent (Str-function-str σ τ)
Str-function-str-univalent {S = S} {T = T} {σ = σ} {τ} θ₁ θ₂ eqv =
  Π-impl-cod≃ (λ s → Π-impl-cod≃ λ t → function≃ (θ₁ eqv) (θ₂ eqv)) ∙e funext-dep≃
```

## Example: magmas

We provide an example of applying the SIP, and the structure
combinators: **$\infty$-magmas**. Recall that a [[magma]] is a [[set]]
equipped with a binary operation, with no further conditions imposed. In
HoTT, we can relax this even further: An $\infty$-magma is a
`Type`{.Agda} - that is, an $\infty$-groupoid - equipped with a binary
operation.

```agda
private
  binop : Type → Type
  binop X = X → X → X
```

We can impose a `Structure`{.Agda} on `binop`{.Agda} by applying nested
`Function-str`{.Agda} and `Pointed-str`{.Agda}. Since this structure is
built out of structure combinators, it's automatically univalent:

```agda
  ∞-Magma : Structure lzero binop
  ∞-Magma = Str-function-str Pointed-str (Str-function-str Pointed-str Pointed-str)

  ∞-Magma-univ : is-univalent ∞-Magma
  ∞-Magma-univ =
    Str-function-str-univalent {τ = Str-function-str Pointed-str Pointed-str}
      Pointed-str-univalent
      (Str-function-str-univalent {τ = Pointed-str}
        Pointed-str-univalent
        Pointed-str-univalent)
```

The type of `∞-Magma`{.Agda} homomorphisms generated by this equivalence
is slightly inconvenient: Instead of getting $f (x \star y) = f x * f
y$, we get something that is parameterised over two paths:

```agda
  _ : {A B : Type-with ∞-Magma} {f : A .fst ≃ B .fst}
    → ∞-Magma .is-hom A B f
    ≡ ( {s : A .fst} {t : B .fst} → f .fst s ≡ t
      → {x : A .fst} {y : B .fst} → f .fst x ≡ y
      → f .fst (A .snd s x) ≡ B .snd t y)
  _ = refl
```

This condition, although it looks a lot more complicated, is essentially
the same as the standard notion:

```agda
  fixup : {A B : Type-with ∞-Magma} {f : A .fst ≃ B .fst}
        → ((x y : A .fst) → f .fst (A .snd x y) ≡ B .snd (f .fst x) (f .fst y))
        → ∞-Magma .is-hom A B f
  fixup {A = A} {B} {f} path {s} {t} p {s₁} {t₁} q =
    f .fst (A .snd s s₁)     ≡⟨ path _ _ ⟩
    B .snd (f .fst s) (f .fst s₁) ≡⟨ ap₂ (B .snd) p q ⟩
    B .snd t     t₁     ∎
```

As an example, we equip the type of booleans with two ∞-magma
structures, one given by conjunction, one by disjunction, and prove that
`not`{.Agda} identifies them, as ∞-magmas:

<div class=mathpar>
```agda
  open import Data.Bool
```
</pre></div>

<div class=mathpar>
```agda
  Conj : Type-with ∞-Magma
  Conj .fst = Bool
  Conj .snd false false = false
  Conj .snd false true  = false
  Conj .snd true  false = false
  Conj .snd true  true  = true
```

```agda
  Disj : Type-with ∞-Magma
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
  not-iso .fst = not , not-is-equiv
  not-iso .snd = fixup {A = Conj} {B = Disj} {f = _ , not-is-equiv} λ where
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

We have a similar phenomenon that happens with NAND and NOR:

<div class=mathpar>
```agda
  Nand : Type-with ∞-Magma
  Nand .fst = Bool
  Nand .snd false false = true
  Nand .snd false true  = true
  Nand .snd true  false = true
  Nand .snd true  true  = false
```

```agda
  Nor : Type-with ∞-Magma
  Nor .fst = Bool
  Nor .snd false false = true
  Nor .snd false true  = false
  Nor .snd true  false = false
  Nor .snd true  true  = false
```
</div>

```agda
  not-iso' : Nand ≃[ ∞-Magma ] Nor
  not-iso' .fst = not , not-is-equiv
  not-iso' .snd = fixup {A = Nand} {B = Nor} {f = _ , not-is-equiv} λ where
    false false → refl
    false true → refl
    true false → refl
    true true → refl
```

# Transport structures

As an alternative to equipping a type family `S : Type → Type` with a
notion of S-homomorphism, we can equip it with a notion of _action_.
Equipping a structure with a notion of action canonically equips it with
a notion of homomorphism:

```agda
Equiv-action : (S : Type ℓ → Type ℓ₁) → Type _
Equiv-action {ℓ = ℓ} S = {X Y : Type ℓ} → (X ≃ Y) → (S X ≃ S Y)

Action→Structure : {S : Type  ℓ → Type ℓ₁} → Equiv-action S → Structure _ S
Action→Structure act .is-hom (A , x) (B , y) f = act f .fst x ≡ y
```

A **transport structure** is a structure `S : Type → Type` with a choice
of equivalence action `α : Equiv-action S` which agrees with the
“intrinsic” notion of equivalence action that is induced by [the
computation rules for transport].

[the computation rules for transport]: 1Lab.Path.html#computation

```agda
is-transport-str : {S : Type ℓ → Type ℓ₁} → Equiv-action S → Type _
is-transport-str {ℓ = ℓ} {S = S} act =
  {X Y : Type ℓ} (e : X ≃ Y) (s : S X) → act e .fst s ≡ subst S (ua e) s
```

While the above definition of `transport structure`{.Agda} is natural,
it can sometimes be unwieldy to work with. Using `univalence`{.Agda
ident=EquivJ}, the condition for being a transport structure can be
weakened to "preserves the identity equivalence", with no loss of
generality:

```agda
preserves-id : {S : Type ℓ → Type ℓ} → Equiv-action S → Type _
preserves-id {ℓ = ℓ} {S = S} act =
  {X : Type ℓ} (s : S X) → act (id , id-equiv) .fst s ≡ s
```

The proof is by equivalence induction: To show something about all `Y :
Type, x : X ≃ Y` (with X fixed), it suffices to cover the case where `Y`
is `X` and `e` is the identity equivalence. This case is by the
assumption that `σ preserves id`{.Agda ident=preserves-id}.

```agda
preserves-id→is-transport-str
  : (σ : Equiv-action S)
  → preserves-id σ → is-transport-str σ
preserves-id→is-transport-str {S = S} σ pres-id e s =
  EquivJ (λ _ e → σ e .fst s ≡ subst S (ua e) s) lemma' e
  where
```

Unfortunately we can not directly use the assumption that `σ` preserves
`id`{.Agda} in the proof, but it can be used as the final step in an
equational proof:

```agda
    lemma' : σ (id , id-equiv) .fst s ≡ subst S (ua (id , id-equiv)) s
    lemma' =
      sym (
        subst S (ua (id , id-equiv)) s ≡⟨ ap (λ p → subst S p s) ua-id-equiv ⟩
        transport refl s               ≡⟨ transport-refl _ ⟩
        s                              ≡⟨ sym (pres-id s) ⟩
        σ (id , id-equiv) .fst s       ∎
      )
```

<!--
```agda
sym-transport-str :
  {S : Type ℓ → Type ℓ₂} (α : Equiv-action S) (τ : is-transport-str α)
  {X Y : Type ℓ} (e : X ≃ Y) (t : S Y)
  → equiv→inverse (α e .snd) t ≡ subst S (sym (ua e)) t
sym-transport-str {S = S} α τ e t =
     sym (transport⁻transport (ap S (ua e)) (ae.from t))
  ·· sym (ap (subst S (sym (ua e))) (τ e (ae.from t)))
  ·· ap (subst S (sym (ua e))) (ae.ε t)
  where module ae = Equiv (α e)
```
-->

If `S` is a `transport structure`{.Agda id=is-transport-str}, then its
canonical equipment as a `Structure`{.Agda} is univalent:

```agda
is-transport→is-univalent : {S : Type ℓ → Type ℓ₁} (a : Equiv-action S)
                          → is-transport-str a
                          → is-univalent (Action→Structure a)
is-transport→is-univalent {S = S} act is-tr {X , s} {Y , t} eqv =
  act eqv .fst s ≡ t              ≃⟨ path→equiv (ap (_≡ t) (is-tr eqv s)) ⟩
  subst S (ua eqv) s ≡ t          ≃⟨ path→equiv (sym (PathP≡Path (λ i → S (ua eqv i)) s t)) ⟩
  PathP (λ i → S (ua eqv i)) s t  ≃∎
```

We can mix and match these different notions of structure at will. For
example, a more convenient definition of function univalent structure
uses an equivalence action on the domain:

```agda
Function-str : Equiv-action S → Structure ℓ T → Structure _ (λ X → S X → T X)
Function-str {S = S} act str .is-hom (A , f) (B , g) e =
  (s : S A) → str .is-hom (A , f s) (B , g (act e .fst s)) e
```

This alternative definition of structure is univalent when `T` is a
univalent structure and `S` is a transport structure:

```agda
Function-str-univalent
  : (α : Equiv-action S) → is-transport-str α
  → (τ : Structure ℓ T) → is-univalent τ
  → is-univalent (Function-str α τ)
Function-str-univalent {S = S} {T = T} α α-tr τ τ-univ {X , f} {Y , g} eqv =
  ((s : S X) → τ .is-hom (X , f s) (Y , _) eqv)     ≃⟨ Π-cod≃ (λ s → τ-univ eqv ∙e path→equiv (ap (PathP (λ i → T (ua eqv i)) (f s) ∘ g) (α-tr _ _))) ⟩
  ((s : S X) → PathP (λ i → T (ua eqv i)) (f s) _)  ≃⟨ (hetero-homotopy≃homotopy e⁻¹) ∙e funext-dep≃ ⟩
  _                                                 ≃∎
```

To see why `Function-str`{.Agda ident=Function-str} is more convenient
than `the previous definition`{.Agda ident=Str-function-str} - which is
why it gets the shorter name - it's convenient to consider how the
`pointed structure`{.Agda ident=Pointed-str} acts on equivalences: _not
at all_. Recall the definition of ∞-magma equivalence generated by
`Str-function-str`{.Agda}:

```agda
private
  _ : {A B : Type-with ∞-Magma} {f : A .fst ≃ B .fst}
    → ∞-Magma .is-hom A B f
    ≡ ( {s : A .fst} {t : B .fst} → f .fst s ≡ t
      → {x : A .fst} {y : B .fst} → f .fst x ≡ y
      → f .fst (A .snd s x) ≡ B .snd t y)
  _ = refl
```

Let's rewrite `∞-Magma`{.Agda} using `Function-str`{.Agda} to see how it
compares:

```agda
  ∞-Magma' : Structure lzero binop
  ∞-Magma' = Function-str id (Function-str id Pointed-str)

  _ : {A B : Type-with ∞-Magma} {f : A .fst ≃ B .fst}
    → ∞-Magma' .is-hom A B f
    ≡ ( (x y : A .fst) → f .fst (A .snd x y) ≡ B .snd (f .fst x) (f .fst y))
  _ = refl
```

Much better! This gets rid of all those redundant paths that were
previously present, using the fact that `λ X → X` _does not need to act
on equivalences_.

In general, transport structures are closed under all of the same
operations as univalent structures, which begs the question: Why mention
univalent structures at all? The reason is that a definition of
structure homomorphism is very often needed, and the data of a univalent
structure is perfect to use in the definition of `SIP`{.Agda}.

<details>
<summary>The closure properties of transport structures are in this
`<details>` tag to keep the length of the page shorter </summary>

```agda
Constant-action : (A : Type ℓ) → Equiv-action {ℓ = ℓ₁} (λ X → A)
Constant-action A eqv = _ , id-equiv

Constant-action-is-transport
  : {A : Type ℓ} → is-transport-str {ℓ = ℓ₁} (Constant-action A)
Constant-action-is-transport f s = sym (transport-refl _)

Id-action-is-transport : is-transport-str {ℓ = ℓ} {ℓ₁ = ℓ} id
Id-action-is-transport f s = sym (transport-refl _)

Product-action : Equiv-action S → Equiv-action T → Equiv-action (λ X → S X × T X)
Product-action actx acty eqv = Σ-ap (actx eqv) λ x → acty eqv

Product-action-is-transport
  : {α : Equiv-action S} {β : Equiv-action T}
  → is-transport-str α → is-transport-str β
  → is-transport-str (Product-action α β)
Product-action-is-transport α-tr β-tr e s =
  Σ-pathp (α-tr e (s .fst)) (β-tr e (s .snd))

Function-action : Equiv-action S → Equiv-action T → Equiv-action (λ X → S X → T X)
Function-action actx acty eqv = function≃ (actx eqv) (acty eqv)

Function-action-is-transport
  : {α : Equiv-action S} {β : Equiv-action T}
  → is-transport-str α → is-transport-str β
  → is-transport-str (Function-action α β)
Function-action-is-transport {S = S} {α = α} {β = β} α-tr β-tr eqv f =
  funext λ x → ap (β eqv .fst ∘ f) (sym-transport-str α α-tr eqv x)
             ∙ β-tr eqv (f (subst S (sym (ua eqv)) x))
```
</details>

# Adding axioms

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
notion of structure with _axioms_, then identification of structures
with axioms is still isomorphism of the underlying structures. For this,
we require that the axioms are valued in [[propositions]].

```agda
module _
  (σ : Structure ℓ S)
  (axioms : (X : _) → S X → Type ℓ₃)
  where
```

First, the notion of structure that you get is just a lifting of the
underlying structure `σ` to ignore the witnesses for the axioms:

```agda
  Axiom-str : Structure ℓ (λ X → Σ[ s ∈ S X ] (axioms X s))
  Axiom-str .is-hom (A , s , a) (B , t , b) f =
    σ .is-hom (A , s) (B , t) f
```

Then, if the axioms are propositional, a calculation by equivalence
reasoning concludes what we wanted: `Axiom-str`{.Agda} is univalent.

```agda
  module _
    (univ : is-univalent σ)
    (axioms-prop : ∀ {X} {s} → is-prop (axioms X s)) where

    Axiom-str-univalent : is-univalent Axiom-str
    Axiom-str-univalent {X = A , s , a} {Y = B , t , b} f =
      σ .is-hom (A , s) (B , t) f
        ≃⟨ univ f ⟩
      PathP (λ i → S (ua f i)) s t
        ≃⟨ Σ-contract (λ x → PathP-is-hlevel 0 (contr b (axioms-prop b))) e⁻¹ ⟩
      Σ[ p ∈ PathP (λ i → S (ua f i)) s t ] PathP (λ i → axioms (ua f i) (p i)) a b
        ≃⟨ Iso→Equiv Σ-pathp-iso ⟩
      _
        ≃∎
```

Here, another facet of the trade-offs between transport and univalent
structures make themselves clear: It's possible (albeit less than
straightforward) to add axioms to a _univalent_ structure, but without
imposing further structure on the axioms themselves, it is not clear how
to add axioms to a _transport_ structure.

Regardless, a very useful consequence of the SIP is that axioms can be
lifted from equivalent underlying structures. For instance: $\bb{N}$
can be defined as both unary numbers (the construction of `Nat`{.Agda}),
or as binary numbers. If you prove that `Nat`{.Agda} is a monoid, and
`Nat ≃ Bin` as pointed ∞-magmas, then `Bin` inherits the monoid
structure.

```agda
transfer-axioms
  : {σ : Structure ℓ S} {univ : is-univalent σ}
    {axioms : (X : _) → S X → Type ℓ₃}
  → (A : Type-with (Axiom-str σ axioms)) (B : Type-with σ)
  → (A .fst , A .snd .fst) ≃[ σ ] B
  → axioms (B .fst) (B .snd)
transfer-axioms {univ = univ} {axioms = axioms} A B eqv =
  subst (λ { (x , y) → axioms x y }) (sip univ eqv) (A .snd .snd)
```

# A language for structures

The structure combinators can be abstracted away into a _language_ for
defining structures. A `Str-term`{.Agda} describes a structure, that may be
interpreted into a family of types, and defines
both transport and univalent structures.

```agda
data Str-term ℓ : (ℓ₁ : Level) → (Type ℓ → Type ℓ₁) → Typeω where
  s-const : ∀ {ℓ₁} (A : Type ℓ₁) → Str-term ℓ ℓ₁ (λ X → A)
  s∙ : Str-term ℓ ℓ (λ X → X)

  _s→_ : ∀ {ℓ₁ ℓ₂} {S} {T} → Str-term ℓ ℓ₁ S → Str-term ℓ ℓ₂ T
       → Str-term ℓ (ℓ₁ ⊔ ℓ₂) (λ X → S X → T X)
  _s×_ : ∀ {ℓ₁ ℓ₂} {S} {T} → Str-term ℓ ℓ₁ S → Str-term ℓ ℓ₂ T
       → Str-term ℓ (ℓ₁ ⊔ ℓ₂) (λ X → S X × T X)

infixr 30 _s→_ _s×_
```

Since each term of the language corresponds to one of the combinators
for building univalent structures, a pair of _mutually recursive_
functions lets us derive a `Structure`{.Agda} and an `action on
equivalences`{.Agda ident=Equiv-action} from a term, at the same time.

```agda
Term→structure : (s : Str-term ℓ ℓ₁ S) → Structure ℓ₁ S
Term→action : (s : Str-term ℓ ℓ₁ S) → Equiv-action S

Term→structure (s-const x) = Constant-str x
Term→structure s∙ = Pointed-str
Term→structure (s s→ s₁) = Function-str (Term→action s) (Term→structure s₁)
Term→structure (s s× s₁) = Product-str (Term→structure s) (Term→structure s₁)

Term→action (s-const x₁) x = _ , id-equiv
Term→action s∙ x = x
Term→action (s s→ s₁) = Function-action (Term→action s) (Term→action s₁)
Term→action (s s× s₁) = Product-action (Term→action s) (Term→action s₁)
```

The reason for this mutual recursion is the same reason that transport
structures are considered in the first place: `Function-str`{.Agda} gives
much better results for the definition of homomorphism than can be
gotten directly using `Str-function-str`{.Agda}. As an example of using
the language, and the generated definition of homomorphism, consider
pointed ∞-magmas:

```agda
private
  Pointed∞Magma : Structure lzero _
  Pointed∞Magma = Term→structure (s∙ s× (s∙ s→ (s∙ s→ s∙)))

  _ : {A B : Type-with Pointed∞Magma} {f : A .fst ≃ B .fst}
    → Pointed∞Magma .is-hom A B f
    ≡ ( (f .fst (A .snd .fst) ≡ B .snd .fst)
      × ((x y : A .fst) → f .fst (A .snd .snd x y)
                        ≡ B .snd .snd (f .fst x) (f .fst y)))
  _ = refl
```

A homomorphic equivalence of pointed ∞-magmas is an equivalence of their
underlying types that preserves the basepoint and is homomorphic over
the operation. The use of `Term→action`{.Agda} in contravariant positions
is responsible for making sure the computed `is-hom`{.Agda} doesn't have
any redundant paths in argument positions.

A mutually _inductive_ argument proves that `Term→action`{.Agda} produces
transport structures, and that `Term→structure`{.Agda} produces univalent
structures. At every case, the proof is by appeal to a lemma that was
proved above.

```agda
Term→structure-univalent : (s : Str-term ℓ ℓ₁ S) → is-univalent (Term→structure s)
Term→action-is-transport : (s : Str-term ℓ ℓ₁ S) → is-transport-str (Term→action s)

Term→structure-univalent (s-const x) = Constant-str-univalent
Term→structure-univalent s∙ = Pointed-str-univalent
Term→structure-univalent (s s→ s₁) =
  Function-str-univalent
    (Term→action s) (Term→action-is-transport s)
    (Term→structure s₁) (Term→structure-univalent s₁)
Term→structure-univalent (s s× s₁) =
  Product-str-univalent {σ = Term→structure s} {τ = Term→structure s₁}
    (Term→structure-univalent s) (Term→structure-univalent s₁)

Term→action-is-transport (s-const x) = Constant-action-is-transport
Term→action-is-transport s∙ = Id-action-is-transport
Term→action-is-transport (s s→ s₁) =
  Function-action-is-transport {α = Term→action s} {β = Term→action s₁}
    (Term→action-is-transport s) (Term→action-is-transport s₁)
Term→action-is-transport (s s× s₁) =
  Product-action-is-transport {α = Term→action s} {β = Term→action s₁}
    (Term→action-is-transport s) (Term→action-is-transport s₁)
```

## Descriptions of structures

To make convenient descriptions of structures-with-axioms, we introduce
a record type, `Str-desc`{.Agda}, which packages together the structure
term and the properties that are imposed:

```agda
record Str-desc ℓ ℓ₁ S ax : Typeω where
  field
    descriptor : Str-term ℓ ℓ₁ S

    axioms : ∀ X → S X → Type ax
    axioms-prop : ∀ X s → is-prop (axioms X s)

Desc→Fam : ∀ {ax} → Str-desc ℓ ℓ₁ S ax → Type ℓ → Type (ℓ₁ ⊔ ax)
Desc→Fam {S = S} desc X =
  Σ[ S ∈ S X ]
    (desc .Str-desc.axioms _ S)

Desc→Str : ∀ {ax} → (S : Str-desc ℓ ℓ₁ S ax) → Structure _ (Desc→Fam S)
Desc→Str desc = Axiom-str (Term→structure descriptor) axioms
  where open Str-desc desc

Desc→is-univalent : ∀ {ax} → (S : Str-desc ℓ ℓ₁ S ax) → is-univalent (Desc→Str S)
Desc→is-univalent desc =
  Axiom-str-univalent
    (Term→structure descriptor) axioms
    (Term→structure-univalent descriptor) (λ {X} {s} → axioms-prop X s)
  where open Str-desc desc
```
