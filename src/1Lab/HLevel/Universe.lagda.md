```
open import 1Lab.HLevel.Retracts
open import 1Lab.Type.Sigma
open import 1Lab.Univalence
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.HLevel.Universe where
```

<!--
```
private variable
  ℓ : Level
  A B C : Type ℓ
```
-->

# Universes of n-types

A common phenomenon in higher category theory is that the collection of
all $n$-categories in a given universe $\ell$ assembles into an
$(n+1)$-category in the successor universe $1+\ell$:

* The collection of all sets (0-categories) is a (1-)-category;
* The collection of all (1-)categories is a 2-category;
* The collection of all 2-categories is a 3-category;

Because of the univalence axiom, the same phenomenon can be observed in
homotopy type theory: The subuniverse of $\ell$ consisting of all
$n$-types is a $(n+1)$-type in $1+\ell$. That means: the universe of
propositions is a set, the universe of sets is a groupoid, the universe
of groupoids is a bigroupoid, and so on.

## h-Levels of Equivalences

As warmup, we prove that if $A$ and $B$ are $n$-types, then so is the
type of equivalences $A \simeq B$. For the case where $n$ is a
successor, this only depends on the h-level of $B$.

```agda
isHLevel-≃ : (n : Nat) → isHLevel A n → isHLevel B n → isHLevel (A ≃ B) n
isHLevel-≃ {A = A} {B = B} zero Ahl Bhl = contr (f , f-eqv) deform where
  f : A → B
  f _ = Bhl .centre

  f-eqv : isEquiv f
  f-eqv = isContr→isEquiv Ahl Bhl
```

For the `zero`{.Agda} case, we're asked to give a proof of
`contractibility`{.Agda ident=isContr} of `A ≃ B`. As the centre we pick
the canonical function sending $x$ to the `centre of contraction`{.Agda
ident=centre} of $B$, which is an equivalence because it is a
`map between contractible types`{.Agda ident=isContr→isEquiv}.

By `the characterisation of paths in Σ`{.Agda ident=Σ-Path} and the fact
that `being an equivalence is a proposition`{.Agda
ident=isProp-isEquiv}, we get the required family of paths deforming any
$A \simeq B$ to our `f`.

```agda
  deform : (g : A ≃ B) → (f , f-eqv) ≡ g
  deform (g , g-eqv) = Σ-Path (λ i x → Bhl .paths (g x) i)
                             (isProp-isEquiv _ _ _)
```

As mentioned before, the case for successors does not depend on the
proof that $A$ has the given h-level. This is because, for $n \ge 1$, $A
\simeq B$ has the same h-level as $A \to B$, which is the same as $B$.

```agda
isHLevel-≃ (suc n) _ Bhl =
  isHLevelΣ (suc n) (isHLevel→ (suc n) Bhl)
                    λ f → isProp→isHLevel-suc (isProp-isEquiv f)
```

## h-Levels of Paths

Univalence states that the type $X ≡ Y$ is equivalent to $X \simeq Y$.
Since the latter is of h-level $n$ when $X$ and $Y$ are $n$-types, then
so is the former:

```agda
isHLevel-≡ : (n : Nat) → isHLevel A n → isHLevel B n → isHLevel (A ≡ B) n
isHLevel-≡ n Ahl Bhl = isHLevel-equiv n ua univalence⁻¹ (isHLevel-≃ n Ahl Bhl)
```

## Universes

We refer to the dependent sum of the family `isHLevel - n`{.Agda
ident=isHLevel} as `n-Type`:

```agda
nType : (ℓ : Level) → Nat → Type (lsuc ℓ)
nType ℓ n = Σ[ T ∈ Type ℓ ] (isHLevel T n)
```

Like mentioned in the introduction, the main theorem of this section is
that `n-Type` is a type of h-level $n+1$. First, the base case: the
universe of all contractible types is a proposition.

```agda
isProp-hContr : isProp (nType ℓ 0)
isProp-hContr (A , ac) (B , bc) =
  Σ-PathP (ua (f , f-eqv))
          λ i → isProp→PathP (λ i → isProp-isContr {A = ua (f , f-eqv) i}) ac bc i
  where
    f : A → B
    f _ = bc .centre

    f-eqv : isEquiv f
    f-eqv = isContr→isEquiv ac bc
```

In reality, this can be strengthened: The type of all contractible types
relative to a universe is _itself_ contractible, because it is an
inhabited proposition:

```agda
isContr-hContr : isContr (nType ℓ 0)
isContr-hContr {ℓ = ℓ} = contr (Lift ℓ ⊤ , contr (lift tt) λ x i → lift tt)
                               (isProp-hContr _)
```

One of the properties of `Σ`{.Agda} types is that, when `B` is a family
of propositions, there is an equivalence $\mathrm{fst}(x) \equiv
\mathrm{fst}(y) \to x \equiv y$ --- `Σ≡Prop`{.Agda}. This lets us prove a
very useful intermediate step: `nType-univalence`{.Agda}, which says
that paths in `nType`{.Agda} are `equivalences`{.Agda ident=_≃_} of the
underlying types.

```agda
nType-ua : {n : Nat} {X Y : nType ℓ n} → (X .fst ≃ Y .fst) → (X ≡ Y)
nType-ua f = Σ≡Prop (λ _ → isProp-isHLevel _) (ua f)

nType-univalence : {n : Nat} {X Y : nType ℓ n} → (X ≡ Y) ≃ (X .fst ≃ Y .fst)
nType-univalence {X = X} {Y} =
  (X ≡ Y)           ≃⟨ Σ≡Prop≃ (λ _ → isProp-isHLevel _) e⁻¹ ⟩
  (X .fst ≡ Y .fst) ≃⟨ pathToEquiv , univalence ⟩
  (X .fst ≃ Y .fst) ≃∎
```

`This`{.Agda ident=nType-univalence}, and the classification of
`h-levels of equivalences`{.Agda ident=isHlevel-≃}, implies the promised
theorem: `nType`{.Agda} is a $(n+1)$-type.

```agda
isHLevel-nType : (n : Nat) → isHLevel (nType ℓ n) (suc n)
isHLevel-nType zero = isProp-hContr
isHLevel-nType (suc n) (A , a) (B , b) =
  isHLevel≃ (suc n) (nType-univalence e⁻¹) (isHLevel-≃ (suc n) a b)
```

Recall that we defined `Set`{.Agda} to be `nType ℓ 2`, just not with
those words.

```agda
_ : ∀ {ℓ} → Set ℓ ≡ nType ℓ 2
_ = refl
```

The theorem above implies that `Set`{.Agda} is a groupoid:

```agda
isGroupoid-Set : ∀ {ℓ} → isGroupoid (Set ℓ)
isGroupoid-Set = isHLevel-nType 2
```
