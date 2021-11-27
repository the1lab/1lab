---
description: |
  The structure identity principle characterises equality in
  "types-with-structure" as being exactly the equivalences that preserve
  that structure. In a sense, it augments univalence with the notion of
  preservation of structure.
---

```agda
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
identification is simply a shorthand --- nothing _prevents_ you from
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

In reality, we need slightly more:

```agda
record Structure {ℓ₁ ℓ₂ : _} (S : Type ℓ₁ → Type ℓ₂) : Type (ℓ₂ ⊔ lsuc ℓ₁) where
  field
```

First, we need a way of picking out, of all the equivalences of the
underlying types, which preserve the `S`-structure. For example, this
would pick out the group (iso)morphisms out from all the equivalences.

```agda
   is-hom : (A B : Σ S) → A .fst ≃ B .fst → Type ℓ₁
```

Furthermore, we require that the identity equivalence always preserves
any structure:

```agda
   is-hom-id : {A : Σ S} → is-hom A A (_ , idEquiv)
```

This data lets us define a binary relation - embedding of structures -
by comparing them with the identity equivalence:

```agda
  [_]_∼_ : {X : _} (x y : S X) → Type _
  [_]_∼_ a b = is-hom (_ , a) (_ , b) (_ , idEquiv)

open Structure public
```

<!--
```
private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A : Type ℓ
  S : Type ℓ → Type ℓ₁
```
-->

We can then show that, if `s ≡ t`, then `s ∼ t` as structures on `X`.
This is done with `J`{.Agda}: By induction, we may assume `t = s`, after
which the goal is reduced to proving that `[ ST ] s ∼ s`. But this is
guaranteed by `is-hom-id`{.Agda}, so we are done.

```agda
structure-path→structure-equiv
  : {X : Type ℓ}
    {S : Type ℓ → Type ℓ₁}
  → (ST : Structure S)
  → {s t : S X}
  → s ≡ t → [ ST ] s ∼ t
structure-path→structure-equiv {X = X} ST {s} {t} path =
  J (λ y _ → [ ST ] s ∼ y)
    (ST .is-hom-id)
    path
```

If this map is an equivalence, we call S a **standard notion of
structure**, abbreviated `SNS`{.Agda}. A `SNS`{.Agda} is a
`Structure`{.Agda} in which related structures are equal, in a coherent
manner:

```agda
isSNS : {ℓ₁ ℓ₂ : _} (S : Type ℓ₁ → Type ℓ₂) → Structure S → Type _
isSNS S ST = {X : _} {s t : S X}
           → isEquiv (structure-path→structure-equiv ST {s} {t})

SNS : {ℓ₁ ℓ₂ : _} (S : Type ℓ₁ → Type ℓ₂) → Type _
SNS S = Σ[ ST ∈ Structure S ] (isSNS _ ST)
```

There are also _two_ abbreviations for packaging together the data that
a given equivalence of underlying types is a homomorphism according to a
`SNS`{.Agda}. The first, `_≃[_]_`{.Agda}, is convenient:

```agda
_≃[_]_ : {S : Type ℓ₁ → Type ℓ₂} → Σ S → SNS S → Σ S → Type ℓ₁
_≃[_]_ {ℓ₁ = ℓ₁} A σ B =
  Σ[ f ∈ A .fst ≃ B .fst ]
   (σ .fst .is-hom A B f)
```

The second, `_≃L[_]_`{.Agda}, is slightly more complicated, and
inconvenient: It's `Lift`{.Agda}ed.

```agda
_≃L[_]_ : {S : Type ℓ₁ → Type ℓ₂} → Σ S → SNS S → Σ S → Type (lsuc ℓ₁)
_≃L[_]_ {ℓ₁ = ℓ₁} A σ B =
  Σ[ f ∈ Lift (lsuc ℓ₁) (A .fst ≃ B .fst) ]
   (σ .fst .is-hom A B (f .Lift.lower))
```

The difference is that `the lifted version`{.Agda ident=_≃L[_]_} lives
in the same universe as `_≡_`{.Agda} for `Type ℓ`{.Agda ident=Type}.
This is a technical concern that will help make the proof of
`SIP`{.Agda} simpler. These are nevertheless related by a simple
isomorphism:

```agda
≃[]-unlift : {S : Type ℓ₁ → Type ℓ₂} {A B : Σ S} {σ : SNS S}
           → (A ≃L[ σ ] B) ≃ (A ≃[ σ ] B)
≃[]-unlift {A = A} {B} {σ} = Iso→Equiv morp where
  morp : Iso (A ≃L[ σ ] B) (A ≃[ σ ] B)
  morp .fst (lift f , h) = f , h
  morp .snd .isIso.g (f , h) = lift f , h
  morp .snd .isIso.right-inverse x = refl
  morp .snd .isIso.left-inverse x = refl
```

## The principle

We fix a standard notion of structure, `S`, and prove that the identity
type on the total space of S is equivalent to the type of homomorphic
equivalences over S.

```agda
module _ {S : Type ℓ₁ → Type ℓ₂} (σ : SNS S) where
  private
    homomorphism-lemma : {A B : Σ S}
                       → (path : A .fst ≡ B .fst)
                       → (subst S path (A .snd) ≡ B .snd)
                       ≃ σ .fst .is-hom A B (pathToEquiv path)
    homomorphism-lemma {A , s} {B , t} path =
```

First we prove, in steps, a lemma characterising when _paths_ induce
homomorphic structures: Given a path `path : A .fst ≡ B .fst`, it
induces a homomorphic equivalence if, and only if, `A .snd ≡ B .snd`
_over `path`_.

```agda
      J (λ B path' → (t : S B)
                   → (subst S path' s ≡ t)
                   ≃ σ .fst .is-hom (A , s) (B , t) (pathToEquiv path'))
        helper
        path t
```
The construction of `helper`{.Agda} is done in stages. Since `J`{.Agda}
(and `subst`{.Agda}) does not compute nicely in Cubical Type Theory, we
can not prove directly the goal `helper`{.Agda}; What we _can_ prove is
`helper''`{.Agda}.

```agda
      where
        helper'' : (t : S A)
                 → (s ≡ t) ≃ σ .fst .is-hom (A , s) (A , t) (_ , idEquiv)
        helper'' t = structure-path→structure-equiv (σ .fst) , σ .snd

        helper' : (t : S A)
                → (s ≡ t) ≃ σ .fst .is-hom (A , s) (A , t) (pathToEquiv refl)

        helper : (t : S A)
               → (subst S refl s ≡ t) ≃ σ .fst .is-hom (A , s) (A , t)
                                          (pathToEquiv refl)
```

With each step, we get progressively closer to something we can give
`J`. `helper''`{.Agda} is the actual proof: It directly constructs an
equivalence out of the canonical map
`structure-path→structure-equiv`{.Agda} and the proof that `σ` is a
`SNS`{.Agda}.

Next, we adjust the type slightly by "fixing" `(_ , idEquiv)` to be
`pathToEquiv`{.Agda}, and `s ≡ t` to be a dependent path over
`refl`{.Agda}. After these rather technical adjustments,
`helper''`{.Agda} is exactly what we need to give `J`{.Agda}. Again,
this is necessary because `J`{.Agda} does not definitionally compute in
Cubical Type Theory.

<!--
```
        helper' t = subst (λ x → (s ≡ t) ≃ σ .fst .is-hom (A , s) (A , t) x)
                          lemma (helper'' t)
          where
            lemma : _
            lemma = Σ-Path (λ i → transp (λ _ → A → A) (~ i) (λ x → x))
                           (isProp-isEquiv _ _ _)
        helper t = subst (λ x → x ≃ _)
                         (ap₂ _≡_ (sym (transport-refl _)) refl)
                         (helper' t)

```
-->

The `SIP`{.Agda} says that `A ≡ B` is equivalent to the type of
homomorphic equivalences. The path is built using [equivalence
reasoning], and it relates `_≡_`{.Agda} and `_≃[_]_`{.Agda}. Note that
the equivalence contained in the latter type is _lifted_ to be in the
same level as `A ≡ B`.

[equivalence reasoning]: 1Lab.Equiv.html#equivalence-reasoning

```agda
  ℓ-SIP : {A B : Σ S} → (A ≡ B) ≃ (A ≃L[ σ ] B)
  ℓ-SIP {A} {B} =
    (A ≡ B)                                                                ≃⟨ Iso→Equiv (_ , isIso.inverse (Σ-Path-iso .snd)) ⟩
    Σ[ p ∈ A .fst ≡ B .fst ] (subst S p (A .snd) ≡ B .snd)                 ≃⟨ Σ-ap homomorphism-lemma ⟩
    Σ[ p ∈ A .fst ≡ B .fst ] (σ .fst .is-hom A B (pathToEquiv p))          ≃⟨ change-of-vars e¯¹ ⟩
    Σ[ p ∈ Lift _ (A .fst ≃ B .fst) ] (σ .fst .is-hom A B (p .Lift.lower)) ≃⟨⟩
    (A ≃L[ σ ] B)                                                          ≃∎
    where
      change-of-vars = Σ-change-of-variables {A = A .fst ≡ B .fst}
                                             {B = Lift _ (A .fst ≃ B .fst)}
                                             (λ x → lift (pathToEquiv x))
                                             univalence-lift
  ℓ-SIP← : {A B : Σ S} → A ≃L[ σ ] B → A ≡ B
  ℓ-SIP← = isEquiv→isIso (ℓ-SIP .snd) .isIso.g
```

With the `ℓ-SIP`{.Agda} - the _lifted Structure Identity Principle_ - we
can prove the `SIP`{.Agda} which does not involve this `lift`{.Agda}.
This is simpler than proving directly that `(A ≡ B) ≃ (A ≃[ σ ] B)`.

```agda
  SIP : {A B : Σ S} → (A ≡ B) ≃ (A ≃[ σ ] B)
  SIP {A} {B} = 
    (A ≡ B)       ≃⟨ ℓ-SIP ⟩
    (A ≃L[ σ ] B) ≃⟨ ≃[]-unlift {A = A} {B = B} {σ = σ} ⟩
    (A ≃[ σ ] B)  ≃∎

  SIP← : {A B : Σ S} → A ≃[ σ ] B → A ≡ B
  SIP← = isEquiv→isIso (SIP .snd) .isIso.g

  SIP→ : {A B : Σ S} → A ≡ B → A ≃[ σ ] B
  SIP→ = SIP .fst
```

# Example: $\infty$-magmas

We provide an example of applying the SIP: **$\infty$-magmas**. Recall
that a [magma] is a [Set] equipped with a binary operation, with no
further conditions imposed. In HoTT, we can relax this even further: An
$\infty$-magma is a `Type`{.Agda} - that is, an $\infty$-groupoid -
equipped with a binary operation.

[magma]: https://ncatlab.org/nlab/show/magma
[Set]: agda://1Lab.HLevel#Set

```agda
private
  binop : Type → Type
  binop X = X → X → X

  ∞-Magma = Σ binop
```

An equivalence of $\infty$-magmas is an equivalence of underlying types
that commutes with with the binary operation. 

```agda
  ∞-Magma-Structure : Structure binop
  ∞-Magma-Structure .is-hom (A , _·_) (B , _·'_) (f , eqv) =
    Path (A → A → B) (λ x y → f (x · y)) (λ x y → f x ·' f y)
  ∞-Magma-Structure .is-hom-id = refl
```

We'll prove that this is a `SNS`{.Agda}. The proof is indirect: Since
`structure-path→structure-equiv`{.Agda} is [homotopic] to the identity
function, and the latter is an equivalence, then so is the former.

[homotopic]: agda://1Lab.Path#funext

```agda
  ∞-Magma-SNS : SNS binop
  ∞-Magma-SNS .fst = ∞-Magma-Structure
  ∞-Magma-SNS .snd {s = s} {t = t} = goal where
    sp→se~id : {X : _} {s t : binop X} (p : _)
             → structure-path→structure-equiv ∞-Magma-Structure {s = s} {t = t} p
             ≡ p
    sp→se~id {X} {s} =
      J (λ y p → structure-path→structure-equiv
                 ∞-Magma-Structure {s = s} {t = y} p ≡ p)
        (transport-refl _)
```

We can do this by path induction. In that case, the goal amounts to
proving that transporting along the reflexivity path is the identity:
`transport-refl`{.Agda}.
    
```agda
    goal : isEquiv (structure-path→structure-equiv ∞-Magma-Structure {s = s} {t = t})
    goal = subst isEquiv (sym (funext sp→se~id)) idEquiv
```

Then, we can substitute the proof `idEquiv`{.Agda} backwards along the
path `sp→se~id`{.Agda} to get the proof we wanted. Thus,
`∞-Magma`{.Agda} extends to an `SNS`{.Agda}. We can now apply the
`SIP`{.Agda} to get a characterisation of equality in $\infty$-magmas:

```agda
  ∞-Magma-Path : {A B : ∞-Magma} → (A ≡ B) ≃ (A ≃[ ∞-Magma-SNS ] B)
  ∞-Magma-Path = SIP ∞-Magma-SNS
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
  Conj : ∞-Magma
  Conj .fst = Bool
  Conj .snd false false = false
  Conj .snd false true  = false
  Conj .snd true  false = false
  Conj .snd true  true  = true
```

```agda
  Disj : ∞-Magma
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
  not-iso : Conj ≃[ ∞-Magma-SNS ] Disj
  not-iso .fst = not , isEquiv-not
  not-iso .snd i false false = true
  not-iso .snd i false true  = true
  not-iso .snd i true false  = true
  not-iso .snd i true true   = false
```

It's not obvious that this should be the case, especially since the case
analysis makes it not immediately obvious what is going on. However,
writing $\land$ and $\lor$ for the actions of `Conj`{.Agda} and
`Disj`{.Agda} (as one should!), then we see that `not-iso`{.Agda} says
exactly that

$$
\neg (x \land y) = \neg x \lor \neg y
$$

From this and the SIP we get that `Conj`{.Agda} and `Disj`{.Agda} are the same
$\infty$-magma:

```agda
  Conj≡Disj : Conj ≡ Disj
  Conj≡Disj = SIP← ∞-Magma-SNS not-iso
```

# Adding Axioms

Of course, most mathematical objects of interest aren't merely sets with
structure. More often, the objects we're interested in have _stuff_ (the
underlying type), _structure_ (such as a `SNS`{.Agda}), and _properties_
- for instance, equations imposed on the structure. A concrete example
may help:

- A **pointed $\infty$-magma** is a pointed type equipped with a binary operation;
- A **monoid** is a pointed $\infty$-magma with additional data
witnessing that a) the type is a set; b) the operation is associative;
and c) the point acts as a left- and right- identity for the operation.

Fortunately, the SIP again applies here: If you augment a standard
notion of structure with _axioms_, then equality of structures with
axioms is still isomorphism. For this, we require that the axioms be
[valued in propositions](agda://1Lab.HLevel#isProp).

```agda
module _
  {S : Type ℓ₁ → Type ℓ₂}
  (σ : SNS S)
  (axioms : (X : _) → S X → Type ℓ₃)
  (axioms-prop : {X : _} {s : _} → isProp (axioms X s))
  where
```

First, there is a map that forgets the fact that the structure was
augmented with axioms:

```agda
  [_] : Σ[ x ∈ _ ] Σ[ s ∈ S x ] (axioms x s) → Σ S
  [ x , s , ax ] = _ , s
```

Then we can prove that including the original structures and the axioms
(which - recall - are valued in propositions!) into a big Σ also defines
a standard notion of structure. Let's look at it in parts:

```agda
  add-axioms : SNS (λ x → Σ[ s ∈ S x ] axioms x s)
  add-axioms = str , isequiv where
    S' : _ → Type _
    S' x = Σ[ s ∈ S x ] (axioms x s)
```

* First we have the carrier type, `S'`. It consists of the original
structure `S` and the new `axioms`.

```agda
    ish : _
    ish A B x = σ .fst .is-hom [ A ] [ B ] x

    idh : _
    idh = σ .fst .is-hom-id
```

* A homomorphism of S' is the same thing as a homomorphism of the
underlying S. This is because the `axioms` are valued in propositions,
so they can not meaningfully be "altered" by a homomorphism, and so do
not need to be preserved.

```agda
    str : Structure S'
    str = record { is-hom = ish ; is-hom-id = idh }
```

* This already assembles into a notion of `Structure`{.Agda}. We'll
prove that it's standard:

```agda
    π : {X : _} → S' X → S X
    π (fst , _) = fst

    new : {X : _} {s t : _} → s ≡ t → _
    new {X = X} {s = s} {t = t} = structure-path→structure-equiv {X = X} str {s} {t}

    old : {X : _} {s t : _} → s ≡ t → _
    old {X = X} {s = s} {t = t} =
      structure-path→structure-equiv {X = X} (σ .fst) {s} {t}
```

We'll show that the `new`{.Agda} way of turning structure-paths into
homomorphisms breaks down as a composition of two equivalences: The
`old`{.Agda} canonical map (the one from `σ`), and `ap π`{.Agda
ident=π}.

```agda
    isequiv : {X : _} {s t : S' X}
            → isEquiv (new {s = s} {t = t})
    isequiv {X} {s} {t} = hence-so-is-new where
      p : (x : s ≡ t) → new x ≡ old (ap π x)
      p = J (λ y p → new {s = s} {t = y} p ≡ old (ap π p))
            refl
```

With `J`{.Agda}, this is automatic, so the proof is `refl`{.Agda}! Then
we use the fact that `equivalences are closed under composition`{.Agda
ident=∙-isEquiv} to conclude that, since `old`{.Agda} and `ap π`{.Agda
ident=π} are equivalences, then so is their composite:

```agda
      composite-is-equivalence : isEquiv (λ (p : s ≡ t) → old (ap π p))
      composite-is-equivalence =
        ∙-isEquiv
          {f = ap π}
          {g = structure-path→structure-equiv (σ .fst)}
          (Subset-proj-embedding (λ _ → axioms-prop))
          (σ .snd)
```

Since maps [homotopic] to equivalences are equivalences, `new`{.Agda} is
an equivalence, and we are done. The map `ap π`{.Agda ident=π} is an
equivalence because `π`{.Agda} is a projection from a _subset_: an
[embedding], as witnessed by `Subset-proj-embedding`{.Agda}.

[embedding]: agda://1Lab.Equiv.Embedding#isEmbedding

```agda
      hence-so-is-new : isEquiv new
      hence-so-is-new = subst isEquiv (sym (funext p)) composite-is-equivalence
```
