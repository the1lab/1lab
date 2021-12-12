```agda
open import 1Lab.Prelude

module Algebra.Semigroup where
```

<!--
```agda
private variable
  ℓ ℓ₁ : Level
  A : Type ℓ
```
-->

# ∞-Magmas

In common mathematical parlance, a **magma** is a set equipped with a
binary operation. In HoTT, we free ourselves from considering sets as a
primitive, and generalise to ∞-groupoids: An **∞-magma** is a _type_
equipped with a binary operation.

```agda
is∞Magma : Type ℓ → Type ℓ
is∞Magma X = X → X → X
```

Since we can canonically identify the predicate `is∞Magma`{.Agda} with a
`Structure`{.Agda} built with the structure language, we automatically
get a notion of ∞-Magma homomorphism, and a proof that
`∞MagmaStr`{.Agda} is a `univalent structure`{.Agda ident=isUnivalent}.

```
∞MagmaStr : Structure ℓ is∞Magma
∞MagmaStr = tm→Structure (s∙ s→ (s∙ s→ s∙))

∞MagmaStr-univ : isUnivalent (∞MagmaStr {ℓ = ℓ})
∞MagmaStr-univ = tm→Structure-univalent (s∙ s→ (s∙ s→ s∙))
```

Generalising magmas to ∞-magmas does not pose a problem because ∞-magmas
do not have any _paths_. However, when considering structures with
equalities, like semigroups, we must restrict ourselves to sets to get a
coherent object, hence the field `smg-isSet`{.Agda}.

# Semigroups

```
record isSemigroup {A : Type ℓ} (_⋆_ : A → A → A) : Type ℓ where
```

A **semigroup** is a `set`{.Agda ident=isSet} equipped with a choice of
_associative_ binary operation `⋆`.

```
  field
    smg-isSet       : isSet A
    smg-associative : {x y z : A} → x ⋆ (y ⋆ z) ≡ (x ⋆ y) ⋆ z

open isSemigroup public
```

To see why the set truncation is really necessary, it helps to
explicitly describe the expected structure of a "∞-semigroup" in terms
of the language of higher categories:

- An ∞-groupoid `A`, equipped with

- A map `_⋆_ : A → A → A`, such that

- `⋆` is _associative_: there exists an invertible 2-morphism `α : A ⋆
(B ⋆ C) ≡ (A ⋆ B) ⋆ C` (called the associator), satisfying

- The _pentagon identity_, i.e. there is an equality `π` (the
pentagonator) witnessing commutativity of the diagram below, where all
the faces are `α`:
~~~{.quiver .tall-2}
\[\begin{tikzcd}
  & {(a \star b) \star (c\star d)} \\
  {((a \star b) \star c)\star d} && {a\star(b\star(c\star d)))} \\
  \\
  {(a\star(b\star c))\star d} && {a\star((b\star c)\star d)}
  \arrow[Rightarrow, no head, from=2-1, to=1-2]
  \arrow[Rightarrow, no head, from=1-2, to=2-3]
  \arrow[Rightarrow, no head, from=2-3, to=4-3]
  \arrow[Rightarrow, no head, from=4-3, to=4-1]
  \arrow[Rightarrow, no head, from=4-1, to=2-1]
\end{tikzcd}\]
~~~

- The pentagonator satisfies its own coherence law, which looks like the
Stasheff polytope $K_5$, and so on, "all the way up to infinity".

By explicitly asking that `A` be truncated at the level of sets, we have
that the associator automatically satisfies the pentagon identity -
because all parallel paths in a set are equal. Furthermore, by the
upwards closure of h-levels, any further coherence condition you could
dream up and write down for these morphisms is automatically satisfied.

As a consequence of this truncation, we get that being a semigroup
operator is a _property_ of the operator:

```
isProp-isSemigroup : {_⋆_ : A → A → A} → isProp (isSemigroup _⋆_)
isProp-isSemigroup x y i .smg-isSet =
  isProp-isHLevel 2 (x .smg-isSet) (y .smg-isSet) i
isProp-isSemigroup {_⋆_ = _⋆_} x y i .smg-associative {a} {b} {c} =
  x .smg-isSet (a ⋆ (b ⋆ c)) ((a ⋆ b) ⋆ c)
               (x .smg-associative) (y .smg-associative) i
```

A **semigroup structure on** a type packages up the binary operation and
the axiom in a way equivalent to a `structure`{.Agda ident=Structure}.

```
SemigroupOn : Type ℓ → Type ℓ
SemigroupOn X = Σ (isSemigroup {A = X})
```

`SemigroupOn`{.Agda} is a univalent structure, because it is equivalent
to a structure expressed as a `structure term`{.Agda}. This is only the
case because `isSemigroup`{.Agda} is a proposition, i.e.
`SemigroupOn`{.Agda} can be expressed as a "structure part" (the binary
operation) and an "axiom part" (the associativity)!

```
module _ where
  private
    sg-term : StrTm ℓ
    sg-term =
      axioms
        (s∙ s→ (s∙ s→ s∙))
        (λ X f → isSemigroup f)
        λ X s → isProp-isSemigroup

  SemigroupStr : Structure ℓ (SemigroupOn {ℓ = ℓ})
  SemigroupStr = tm→Structure sg-term

  SemigroupStr-univ : isUnivalent (SemigroupStr {ℓ = ℓ})
  SemigroupStr-univ = tm→Structure-univalent sg-term
```

## The "min" semigroup

An example of a naturally-occuring semigroup are the natural numbers
under taking `minimums`{.Agda ident=min}.

```
Nat-min : isSemigroup min
Nat-min .smg-isSet = isSet-Nat
Nat-min .smg-associative = min-assoc _ _ _
```

What is meant by "naturally occuring" is that this semigroup can not be
made into a monoid: There is no natural number `unit` such that, for all
`y`, `min unit y ≡ y` and `min y unit ≡ y`.

```
private
  min-no-id : (unit : Nat) → ((y : Nat) → min unit y ≡ y) → ⊥
  min-no-id x id =
    let
      sucx≤x : suc x ≤ x
      sucx≤x = subst (λ e → e ≤ x) (id (suc x)) (min-≤ˡ x (suc x))
    in ¬sucx≤x x sucx≤x
```

## Identities

In a magma, an element $e$ such that $x \star e = x$ and $e \star x = x$
is called a **two-sided identity**. Accordingly, dropping either of
these paths results in a right identity or a left identity. In
particular, this theorem can be weakened: If $l$ is a left identity and
$r$ is a right identity, then $l = r$.

```
isLeftId : (⋆ : A → A → A) → A → Type _
isLeftId _⋆_ l = ∀ y → l ⋆ y ≡ y

isRightId : (⋆ : A → A → A) → A → Type _
isRightId _⋆_ r = ∀ y → y ⋆ r ≡ y

isTwoSideId : (⋆ : A → A → A) → A → Type _
isTwoSideId ⋆ r = isLeftId ⋆ r × isRightId ⋆ r

left-right : {⋆ : A → A → A} (l r : A) → isLeftId ⋆ l → isRightId ⋆ r → l ≡ r
left-right {⋆ = _⋆_} l r lid rid =
  l     ≡⟨ sym (rid _) ⟩
  l ⋆ r ≡⟨ lid _ ⟩
  r     ∎
```

In a semigroup, since the underlying type is a set, we have that the
type of two-sided identities is a proposition. This is because
`left-right`{.Agda} shows the elements are equal, and the witnesses are
equal because they are propositions (they are `products`{.Agda
ident=isHLevel×} of `families`{.Agda ident=isHLevelΠ} of equalities in a
Set - thus they are propositions).

```
isProp-twoSideId : {⋆ : A → A → A} → isSemigroup ⋆
                 → isProp (Σ[ u ∈ A ] (isTwoSideId ⋆ u))
isProp-twoSideId semi x y =
  Σ≡Prop (λ u → isHLevel× 1 (isHLevelΠ 1 (λ _ → semi .smg-isSet _ _))
                            (isHLevelΠ 1 (λ _ → semi .smg-isSet _ _)))
    (left-right (x .fst) (y .fst) (x .snd .fst) (y .snd .snd))
```