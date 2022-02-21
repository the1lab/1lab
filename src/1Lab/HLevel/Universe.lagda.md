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
is-hlevel-≃ : (n : Nat) → is-hlevel A n → is-hlevel B n → is-hlevel (A ≃ B) n
is-hlevel-≃ {A = A} {B = B} zero Ahl Bhl = contr (f , f-eqv) deform where
  f : A → B
  f _ = Bhl .centre

  f-eqv : is-equiv f
  f-eqv = is-contr→is-equiv Ahl Bhl
```

For the `zero`{.Agda} case, we're asked to give a proof of
`contractibility`{.Agda ident=is-contr} of `A ≃ B`. As the centre we pick
the canonical function sending $x$ to the `centre of contraction`{.Agda
ident=centre} of $B$, which is an equivalence because it is a
`map between contractible types`{.Agda ident=is-contr→is-equiv}.

By `the characterisation of paths in Σ`{.Agda ident=Σ-path} and the fact
that `being an equivalence is a proposition`{.Agda
ident=is-equiv-is-prop}, we get the required family of paths deforming any
$A \simeq B$ to our `f`.

```agda
  deform : (g : A ≃ B) → (f , f-eqv) ≡ g
  deform (g , g-eqv) = Σ-path (λ i x → Bhl .paths (g x) i)
                              (is-equiv-is-prop _ _ _)
```

As mentioned before, the case for successors does not depend on the
proof that $A$ has the given h-level. This is because, for $n \ge 1$, $A
\simeq B$ has the same h-level as $A \to B$, which is the same as $B$.

```agda
is-hlevel-≃ (suc n) _ Bhl =
  Σ-is-hlevel (suc n) 
    (fun-is-hlevel (suc n) Bhl)
    λ f → is-prop→is-hlevel-suc (is-equiv-is-prop f)
```

## h-Levels of Paths

Univalence states that the type $X ≡ Y$ is equivalent to $X \simeq Y$.
Since the latter is of h-level $n$ when $X$ and $Y$ are $n$-types, then
so is the former:

```agda
is-hlevel-≡ : (n : Nat) → is-hlevel A n → is-hlevel B n → is-hlevel (A ≡ B) n
is-hlevel-≡ n Ahl Bhl = equiv→is-hlevel n ua univalence⁻¹ (is-hlevel-≃ n Ahl Bhl)
```

## Universes

We refer to the dependent sum of the family `is-hlevel - n`{.Agda
ident=is-hlevel} as `n-Type`:

```agda
n-Type : (ℓ : Level) → Nat → Type (lsuc ℓ)
n-Type ℓ n = Σ[ T ∈ Type ℓ ] (is-hlevel T n)
```

Like mentioned in the introduction, the main theorem of this section is
that `n-Type` is a type of h-level $n+1$. First, the base case: the
universe of all contractible types is a proposition.

```agda
0-Type-is-prop : is-prop (n-Type ℓ 0)
0-Type-is-prop (A , ac) (B , bc) =
  Σ-pathp (ua (f , f-eqv))
          λ i → is-prop→pathp (λ i → is-contr-is-prop {A = ua (f , f-eqv) i}) ac bc i
  where
    f : A → B
    f _ = bc .centre

    f-eqv : is-equiv f
    f-eqv = is-contr→is-equiv ac bc
```

In reality, this can be strengthened: The type of all contractible types
relative to a universe is _itself_ contractible, because it is an
inhabited proposition:

```agda
0-Type-is-contr : is-contr (n-Type ℓ 0)
0-Type-is-contr {ℓ = ℓ} = contr (Lift ℓ ⊤ , contr (lift tt) λ x i → lift tt)
                                (0-Type-is-prop _)
```

One of the properties of `Σ`{.Agda} types is that, when `B` is a family
of propositions, there is an equivalence $\mathrm{fst}(x) \equiv
\mathrm{fst}(y) \to x \equiv y$ --- `Σ-prop-path`{.Agda}. This lets us prove a
very useful intermediate step: `n-Type-univalence`{.Agda}, which says
that paths in `n-Type`{.Agda} are `equivalences`{.Agda ident=_≃_} of the
underlying types.

```agda
n-Type-ua : {n : Nat} {X Y : n-Type ℓ n} → (X .fst ≃ Y .fst) → (X ≡ Y)
n-Type-ua f = Σ-prop-path (λ _ → is-hlevel-is-prop _) (ua f)

n-Type-univalence : {n : Nat} {X Y : n-Type ℓ n} → (X ≡ Y) ≃ (X .fst ≃ Y .fst)
n-Type-univalence {X = X} {Y} =
  (X ≡ Y)           ≃⟨ Σ-prop-path≃ (λ _ → is-hlevel-is-prop _) e⁻¹ ⟩
  (X .fst ≡ Y .fst) ≃⟨ path→equiv , univalence ⟩
  (X .fst ≃ Y .fst) ≃∎
```

`This`{.Agda ident=n-Type-univalence}, and the classification of
`h-levels of equivalences`{.Agda ident=isHlevel-≃}, implies the promised
theorem: `n-Type`{.Agda} is a $(n+1)$-type.

```agda
n-Type-is-hlevel : (n : Nat) → is-hlevel (n-Type ℓ n) (suc n)
n-Type-is-hlevel zero = 0-Type-is-prop
n-Type-is-hlevel (suc n) (A , a) (B , b) =
  is-hlevel≃ (suc n) (n-Type-univalence e⁻¹) (is-hlevel-≃ (suc n) a b)
```

Recall that we defined `Set`{.Agda} to be `n-Type ℓ 2`, just not with
those words.

```agda
_ : ∀ {ℓ} → Set ℓ ≡ n-Type ℓ 2
_ = refl
```

The theorem above implies that `Set`{.Agda} is a groupoid:

```agda
Set-is-groupoid : ∀ {ℓ} → is-groupoid (Set ℓ)
Set-is-groupoid = n-Type-is-hlevel 2
```
