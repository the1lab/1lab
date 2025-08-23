---
description: Using univalence, we compute the h-level of the universe of n types.
---
<!--
```agda
open import 1Lab.HLevel.Closure
open import 1Lab.Type.Sigma
open import 1Lab.Univalence
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.HLevel.Universe where
```

<!--
```agda
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

Because of the [[univalence axiom]], the same phenomenon can be observed
in homotopy type theory: The subuniverse of $\ell$ consisting of all
$n$-types is a $(n+1)$-type in $1+\ell$. That means: the universe of
propositions is a set, the universe of sets is a groupoid, the universe
of groupoids is a bigroupoid, and so on.

## h-Levels of equivalences

As warmup, we prove that if $A$ and $B$ are $n$-types, then so is the
type of equivalences $A \simeq B$. For the case where $n$ is a
successor, this only depends on the h-level of $B$.

<!--
```agda
_ = is-contr
```
-->

```agda
≃-is-hlevel : (n : Nat) → is-hlevel A n → is-hlevel B n → is-hlevel (A ≃ B) n
≃-is-hlevel {A = A} {B = B} zero Ahl Bhl = contr (f , f-eqv) deform where
  f : A → B
  f _ = Bhl .centre

  f-eqv : is-equiv f
  f-eqv = is-contr→is-equiv Ahl Bhl
```

For the `zero`{.Agda} case, we're asked to give a proof of
`contractibility`{.Agda ident=is-contr} of `A ≃ B`. As the centre we pick
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
≃-is-hlevel (suc n) _ Bhl =
  Σ-is-hlevel (suc n)
    (fun-is-hlevel (suc n) Bhl)
    λ f → is-prop→is-hlevel-suc (is-equiv-is-prop f)
```

<!--
```agda
≃-is-hlevelˡ : (n : Nat) → is-hlevel A (suc n) → is-hlevel (A ≃ B) (suc n)
≃-is-hlevelˡ n ahl = is-hlevel-join n λ e → ≃-is-hlevel (suc n) ahl (Equiv→is-hlevel (suc n) (Equiv.inverse e) ahl)

≃-is-hlevelʳ : (n : Nat) → is-hlevel B (suc n) → is-hlevel (A ≃ B) (suc n)
≃-is-hlevelʳ n bhl = is-hlevel-join n λ e → ≃-is-hlevel (suc n) (Equiv→is-hlevel (suc n) e bhl) bhl
```
-->

## h-Levels of paths

Univalence states that the type $X ≡ Y$ is equivalent to $X \simeq Y$.
Since the latter is of h-level $n$ when $X$ and $Y$ are $n$-types, then
so is the former:

```agda
≡-is-hlevel : (n : Nat) → is-hlevel A n → is-hlevel B n → is-hlevel (A ≡ B) n
≡-is-hlevel n Ahl Bhl = equiv→is-hlevel n ua univalence⁻¹ (≃-is-hlevel n Ahl Bhl)
```

## Universes

We refer to the dependent sum of the family `is-hlevel - n`{.Agda
ident=is-hlevel} as `n-Type`:

```agda
record n-Type ℓ n : Type (lsuc ℓ) where
  no-eta-equality
  constructor el
  field
    ∣_∣   : Type ℓ
    is-tr : is-hlevel ∣_∣ n
```

<!--
```agda
  infix 100 ∣_∣
  instance
    H-Level-n-type : ∀ {k} → H-Level ∣_∣ (n + k)
    H-Level-n-type = basic-instance n is-tr

open n-Type using (∣_∣ ; is-tr ; H-Level-n-type) public
```
-->

Like mentioned in the introduction, the main theorem of this section is
that `n-Type` is a type of h-level $n+1$. We take a detour first and
establish a characterisation of paths for `n-Type`{.Agda}: Since
`is-tr`{.Agda} is a proposition, paths in `n-Type`{.Agda} are determined
by paths of the underlying types. By univalence, these correspond to
_equivalences_ of the underlying type:

```agda
n-path : {n : Nat} {X Y : n-Type ℓ n} → ∣ X ∣ ≡ ∣ Y ∣ → X ≡ Y
n-path f i .∣_∣ = f i
n-path {n = n} {X} {Y} f i .is-tr =
  is-prop→pathp (λ i → is-hlevel-is-prop {A = f i} n) (X .is-tr) (Y .is-tr) i

n-ua : {n : Nat} {X Y : n-Type ℓ n} → ∣ X ∣ ≃ ∣ Y ∣ → X ≡ Y
n-ua f = n-path (ua f)

n-univalence : {n : Nat} {X Y : n-Type ℓ n} → (∣ X ∣ ≃ ∣ Y ∣) ≃ (X ≡ Y)
n-univalence {n = n} {X} {Y} = n-ua , is-iso→is-equiv isic where
  inv : ∀ {Y} → X ≡ Y → ∣ X ∣ ≃ ∣ Y ∣
  inv p = path→equiv (ap ∣_∣ p)

  linv : ∀ {Y} → is-left-inverse (inv {Y}) n-ua
  linv x = Σ-prop-path is-equiv-is-prop (funext λ x → transport-refl _)

  rinv : ∀ {Y} → is-right-inverse (inv {Y}) n-ua
  rinv = J (λ y p → n-ua (inv p) ≡ p) path where
    path : n-ua (inv {X} refl) ≡ refl
    path i j .∣_∣ = ua.ε {A = ∣ X ∣} refl i j
    path i j .is-tr = is-prop→squarep
      (λ i j → is-hlevel-is-prop
        {A = ua.ε {A = ∣ X ∣} refl i j} n)
      (λ j → X .is-tr) (λ j → n-ua {X = X} {Y = X} (path→equiv refl) j .is-tr)
      (λ j → X .is-tr) (λ j → X .is-tr)
      i j

  isic : is-iso n-ua
  isic = iso inv rinv (linv {Y})
```

Since h-levels are closed under equivalence, and we already have an
upper bound on the h-level of $X \simeq Y$ when $Y$ is an $n$-type, we
know that $n$-Type is a $(n+1)$-type:

```agda
abstract
  n-Type-is-hlevel : ∀ n → is-hlevel (n-Type ℓ n) (suc n)
  n-Type-is-hlevel zero x y = n-ua
    ((λ _ → y .is-tr .centre) , is-contr→is-equiv (x .is-tr) (y .is-tr))
  n-Type-is-hlevel (suc n) x y =
    Equiv→is-hlevel (suc n) (n-univalence e⁻¹) (≃-is-hlevel (suc n) (x .is-tr) (y .is-tr))
```

For 1-categorical mathematics, the important h-levels are the
_propositions_ and the _sets_, so they get short names:

```agda
Set : ∀ ℓ → Type (lsuc ℓ)
Set ℓ = n-Type ℓ 2

Prop : ∀ ℓ → Type (lsuc ℓ)
Prop ℓ = n-Type ℓ 1
```

<!--
```agda
¬Set-is-prop : ¬ is-prop (Set ℓ)
¬Set-is-prop prop =
  lower $
  transport (ap ∣_∣ (prop (el (Lift _ ⊤) (hlevel 2)) (el (Lift _ ⊥) (hlevel 2)))) (lift tt)
```
-->

<!--
```agda
n-Type-square
  : ∀ {ℓ} {n}
  → {w x y z : n-Type ℓ n}
  → {p : x ≡ w} {q : x ≡ y} {s : w ≡ z} {r : y ≡ z}
  → Square (ap ∣_∣ p) (ap ∣_∣ q) (ap ∣_∣ s) (ap ∣_∣ r)
  → Square p q s r
n-Type-square sq i j .∣_∣ = sq i j
n-Type-square {p = p} {q} {s} {r} sq i j .is-tr =
  is-prop→squarep (λ i j → is-hlevel-is-prop {A = sq i j} _)
    (ap is-tr p) (ap is-tr q) (ap is-tr s) (ap is-tr r) i j

n-ua-square
  : ∀ {ℓ} {n}
  → {w x y z : n-Type ℓ n}
  → {p : ∣ x ∣ ≃ ∣ w ∣} {q : ∣ x ∣ ≃ ∣ y ∣} {s : ∣ w ∣ ≃ ∣ z ∣} {r : ∣ y ∣ ≃ ∣ z ∣}
  → Path (∣ x ∣ → ∣ z ∣) (λ a → s .fst (p .fst a)) (λ a → r .fst (q .fst a))
  → Square (n-ua {X = x} {w} p) (n-ua {X = x} {y} q) (n-ua {X = w} {z} s) (n-ua r)
n-ua-square x = n-Type-square (ua-square x)

n-ua-triangle
  : ∀ {ℓ n} {A B C : n-Type ℓ n} {e : ∣ A ∣ ≃ ∣ B ∣} {f : ∣ A ∣ ≃ ∣ C ∣} {g : ∣ B ∣ ≃ ∣ C ∣}
  → Path (∣ A ∣ → ∣ C ∣) (f .fst) (λ x → g .fst (e .fst x))
  → Triangle (n-ua {X = A} {B} e) (n-ua {Y = C} f) (n-ua g)
n-ua-triangle α = n-Type-square (ua-triangle α)
```
-->
