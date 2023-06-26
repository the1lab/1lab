<!--
```agda
open import 1Lab.Prelude
open import Data.Sum

open import Data.Rel.Base

import Data.Nat as Nat
import Data.Nat.Order as Nat
```
-->

```agda
module Data.Rel.Closure where
```

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A B X : Type ℓ
  R R' S : A → A → Type ℓ
```
-->

# Closures of relations

A **closure operator** $-^{+}$ on relations takes a relation $R$ on a type
$A$ to a new relation $R^{+}$ on $A$, where $R^{+}$ is the smallest
relation containing $R$ that satisfies some property.

<!-- [TODO: Reed M, 01/06/2023] Talk about monads here. -->

## Reflexive Closure

The reflexive closure of a relation $R$ is the smallest reflexive
relation $R^{=}$ that contains $R$.

```agda
data Refl {A : Type ℓ} (R : Rel A A ℓ') (x : A) : A → Type (ℓ ⊔ ℓ') where
  reflexive : Refl R x x
  [_] : ∀ {y} → R x y → Refl R x y
  trunc : ∀ {y} → is-prop (Refl R x y)
```

<!--
```agda
instance
  Refl-H-Level : ∀ {x y} {n} → H-Level (Refl R x y) (suc n)
  Refl-H-Level = prop-instance trunc

Refl-elim
  : (P : ∀ (x y : A) → Refl R x y → Type ℓ'')
  → (∀ {x y} → (r : R x y) → P x y [ r ])
  → (∀ x → P x x reflexive)
  → (∀ {x y} → (r+ : Refl R x y) → is-prop (P x y r+))
  → ∀ {x y} → (r+ : Refl R x y) → P x y r+
Refl-elim {R = R} P prel prefl pprop r+ = go r+ where
  go : ∀ {x y} → (r+ : Refl R x y) → P x y r+
  go reflexive = prefl _
  go [ x ] = prel x
  go (trunc r+ r+' i) =
    is-prop→pathp (λ i → pprop (trunc r+ r+' i)) (go r+) (go r+') i
```
-->

The recursion principle for the reflexive closure of a relation witnesses
the aforementioned universal property: it is the smallest reflexive
relation containing $R$.

```agda
Refl-rec
  : (S : A → A → Type ℓ)
  → (∀ {x y} → R x y → S x y)
  → (∀ x → S x x)
  → (∀ {x y} → is-prop (S x y))
  → ∀ {x y} → Refl R x y → S x y
Refl-rec {R = R} S prel prefl pprop r+ = go r+ where
  go : ∀ {x y} → Refl R x y → S x y
  go reflexive = prefl _
  go [ r ] = prel r
  go (trunc r+ r+' i) = pprop (go r+) (go r+') i
```

<!--
```agda
Refl-rec₂
  : (S : A → A → A → Type ℓ)
  → (∀ {x y z} → R x y → R' y z → S x y z)
  → (∀ {x z} → R' x z → S x x z)
  → (∀ {x y} → R x y → S x y y)
  → (∀ x → S x x x)
  → (∀ {x y z} → is-prop (S x y z))
  → ∀ {x y z} → Refl R x y → Refl R' y z → S x y z
Refl-rec₂ {R = R} {R' = R'} S prel prefll preflr prefl2 pprop r+ r+' = go r+ r+' where
  go : ∀ {x y z} → Refl R x y → Refl R' y z → S x y z
  go reflexive reflexive = prefl2 _
  go reflexive [ r' ] = prefll r'
  go reflexive (trunc r+ r+' i) =
    pprop (go reflexive r+) (go reflexive r+') i
  go [ r ] reflexive = preflr r
  go [ r ] [ r' ] = prel r r'
  go [ r ] (trunc r+ r+' i) =
    pprop (go [ r ] r+) (go [ r ] r+') i
  go (trunc r+ r+' i) r+'' =
    pprop (go r+ r+'') (go r+' r+'') i
```
-->

If the original relation is symmetric or transitive, then so is the
reflexive closure.

```agda
refl-clo-symmetric
  : is-symmetric R
  → is-symmetric (Refl R)
refl-clo-symmetric {R = R} is-sym =
  Refl-rec (λ x y → Refl R y x)
    (λ r → [ is-sym r ])
    (λ _ → reflexive)
    trunc

refl-clo-transitive : is-transitive R → is-transitive (Refl R)
refl-clo-transitive {R = R} is-trans =
    Refl-rec₂ (λ x _ z → Refl R x z)
      (λ x~*y y~*z → [ is-trans x~*y y~*z ])
      [_]
      [_]
      (λ _ → reflexive)
      hlevel!
```


## Symmetric Closure

The symmetric closure of a relation $R$ is the smallest symmetric
relation $R^{\leftrightarrow}$ that contains $R$.

```agda
data Sym {A : Type ℓ} (R : A → A → Type ℓ') (x y : A) : Type (ℓ ⊔ ℓ') where
  symmetric : R y x → Sym R x y
  [_] : R x y → Sym R x y
  trunc : is-prop (Sym R x y)
```

<!--
```agda
instance
  Sym-H-Level : ∀ {x y} {n} → H-Level (Sym R x y) (suc n)
  Sym-H-Level = prop-instance trunc

Sym-elim
  : (P : ∀ (x y : A) → Sym R x y → Type ℓ'')
  → (∀ {x y} → (r : R x y) → P x y [ r ])
  → (∀ {x y} → (r : R y x) → P x y (symmetric r))
  → (∀ {x y} → (r+ : Sym R x y) → is-prop (P x y r+))
  → ∀ {x y} → (r+ : Sym R x y) → P x y r+
Sym-elim {R = R} P prel psym pprop r+ = go r+ where
  go : ∀ {x y} → (r+ : Sym R x y) → P x y r+
  go (symmetric x) = psym x
  go [ x ] = prel x
  go (trunc r+ r+' i) =
    is-prop→pathp (λ i → pprop (trunc r+ r+' i)) (go r+) (go r+') i
```
-->

Like the reflexive closure, the recursion principle for the symmetric
closure witnesses it's universal property; it is the smallest symmetric
relation containing $R$.

```agda
Sym-rec
  : (S : A → A → Type ℓ)
  → (∀ {x y} → R x y → S x y)
  → (∀ {x y} → R x y → S y x)
  → (∀ {x y} → is-prop (S x y))
  → ∀ {x y} → Sym R x y → S x y
Sym-rec {R = R} S prel psym pprop r+ = go r+ where
  go : ∀ {x y} → Sym R x y → S x y
  go (symmetric r) = psym r
  go [ r ] = prel r
  go (trunc r+ r+' i) = pprop (go r+) (go r+') i
```

If two elements $x$ and $y$ are related in the symmetric closure, then
either $R x y$ or $R y x$ in the original relation.

```agda
sym-clo-rel
  : ∀ {x y} → Sym R x y → ∥ (R x y) ⊎ (R y x) ∥
sym-clo-rel {R = R} =
  Sym-rec (λ x y → ∥ (R x y) ⊎ (R y x) ∥)
    (λ r → inc (inl r))
    (λ r → inc (inr r))
    squash
```

If the original relation is reflexive, then so is the symmetric closure.

```agda
sym-clo-reflexive : is-reflexive R → is-reflexive (Sym R)
sym-clo-reflexive is-refl x = [ is-refl x ]
```

Note that this is *not* true for transitivity! To see why, consider an
irreflexive transitive relation on a type with at least related 2
elements $R x y$ . If the symmetric closure of this relation was
transitive, we'd be able to create a loop $R^{\leftrightarrow} x x$ in
the symmetric closure by composing the relations $R^{\leftrightarrow} x
y$ and $R^{\leftrightarrow} y x$.  However, if two elements are related
in the symmetric closure, then they must be related in the original
relation, which leads directly to a contradiction, as the original
relation is irreflexive.

For simplicity, we show this for the strict ordering on the natural
numbers.

```agda
private
  ¬sym-clo-transitive
    : ¬ (is-transitive (Sym Nat._<_))
  ¬sym-clo-transitive sym-clo-trans =
    ∥-∥-rec! (⊎-rec (Nat.<-irrefl refl) (Nat.<-irrefl refl))
      (sym-clo-rel (sym-clo-trans [ 0<1 ] (symmetric 0<1)))
    where
      0<1 : 0 Nat.< 1
      0<1 = Nat.s≤s Nat.0≤x
```

As a corollary, we can see that the transitive closure of the symmetric closure
is not the same as the symmetric closure of the transitive closure.

However, the reflexive closure of the symmetric closure is equal to the
symmetric closure of the reflexive closure.

```agda
sym-clo-refl-clo⊆refl-clo-sym-clo : Sym (Refl R) ⊆r Refl (Sym R)
sym-clo-refl-clo⊆refl-clo-sym-clo {R = R} =
  Sym-rec (Refl (Sym R))
    (Refl-rec (Refl (Sym R))
      (λ x~y → [ [ x~y ] ])
      (λ _ → reflexive)
      hlevel!)
    (Refl-rec (flipr (Refl (Sym R)))
      (λ y~x →  [ symmetric y~x ] )
      (λ _ → reflexive)
      hlevel!)
    hlevel!

refl-clo-sym-clo⊆sym-clo-refl-clo : Refl (Sym R) ⊆r Sym (Refl R)
refl-clo-sym-clo⊆sym-clo-refl-clo {R = R} =
  Refl-rec (Sym (Refl R))
    (Sym-rec (Sym (Refl R))
      (λ x~y → [ [ x~y ] ])
      (λ x~y → symmetric [ x~y ])
      hlevel!)
    (λ _ → [ reflexive ])
    hlevel!

refl-clo-sym-clo≡sym-clo-refl-clo : Refl (Sym R) ≡ Sym (Refl R)
refl-clo-sym-clo≡sym-clo-refl-clo =
  prop-rel-ext trunc trunc
    refl-clo-sym-clo⊆sym-clo-refl-clo
    sym-clo-refl-clo⊆refl-clo-sym-clo
```


## Transitive Closure

The transitive closure of a relation $R$ is the smallest transitive
relation $R^{+}$ that contains $R$.

```agda
data Trans {A : Type ℓ} (_~_ : Rel A A ℓ') (x z : A) : Type (ℓ ⊔ ℓ') where
  [_] : x ~ z → Trans _~_ x z
  transitive : ∀ {y} → Trans _~_ x y → Trans _~_ y z → Trans _~_ x z
  trunc : is-prop (Trans _~_ x z)
```

<!--
```agda
instance
  Trans-H-Level : ∀ {x y} {n} → H-Level (Trans R x y) (suc n)
  Trans-H-Level = prop-instance trunc

Trans-elim
  : (P : ∀ (x y : A) → Trans R x y → Type ℓ)
  → (∀ {x y} → (r : R x y) → P x y [ r ])
  → (∀ {x y z} → (r+ : Trans R x y) → (s+ : Trans R y z)
     → P x y r+ → P y z s+
     → P x z (transitive r+ s+))
  → (∀ {x y} → (r+ : Trans R x y) → is-prop (P x y r+))
  → ∀ {x y} → (r+ : Trans R x y) → P x y r+
Trans-elim {R = R} P prel ptrans pprop r+ = go r+ where
  go : ∀ {x y} → (r+ : Trans R x y) → P x y r+
  go [ r ] = prel r
  go (transitive r+ s+) = ptrans r+ s+ (go r+) (go s+)
  go (trunc r+ r+' i) =
    is-prop→pathp (λ i → pprop (trunc r+ r+' i)) (go r+) (go r+') i
```
-->

The recursion principle for the transitive closure witnesses it's
universal property; it is the smallest transitive relation containing $R$.

```agda
Trans-rec
  : (S : A → A → Type ℓ)
  → (∀ {x y} → (r : R x y) → S x y)
  → (∀ {x y z} → S x y → S y z → S x z)
  → (∀ {x y} → is-prop (S x y))
  → ∀ {x y} → Trans R x y → S x y
Trans-rec {R = R} S prel ptrans pprop r+ = go r+ where
  go : ∀ {x y} → Trans R x y → S x y
  go [ r ] = prel r
  go (transitive r+ s+) = ptrans (go r+) (go s+)
  go (trunc r+ r+' i) = pprop (go r+) (go r+') i
```

If the original relation is reflexive or symmetric, then so is the
transitive closure.

```agda
trans-clo-reflexive : is-reflexive R → is-reflexive (Trans R)
trans-clo-reflexive is-refl x = [ is-refl x ]

trans-clo-symmetric : is-symmetric R → is-symmetric (Trans R)
trans-clo-symmetric {R = R} is-sym r+ =
  Trans-rec (λ x y → Trans R y x)
    (λ r → [ is-sym r ])
    (λ r+ s+ → transitive s+ r+)
    trunc
    r+
```

## Reflexive-Transitive Closure

The reflexive-transitive closure of a relation $R$ is the smallest
reflexive and transitive relation $R^{*}$ that contains $R$.

```agda
data Refl-trans {A : Type ℓ} (R : A → A → Type ℓ') (x : A) : A → Type (ℓ ⊔ ℓ') where
  [_] : ∀ {y} → R x y → Refl-trans R x y
  reflexive : Refl-trans R x x
  transitive : ∀ {y z} → Refl-trans R x y → Refl-trans R y z → Refl-trans R x z
  trunc : ∀ {y} → is-prop (Refl-trans R x y)
```

<!--
```agda
instance
  Refl-trans-H-Level : ∀ {x y} {n} → H-Level (Refl-trans R x y) (suc n)
  Refl-trans-H-Level = prop-instance trunc

Refl-trans-elim
  : (P : ∀ (x y : A) → Refl-trans R x y → Type ℓ'')
  → (∀ {x y} → (r : R x y) → P x y [ r ])
  → (∀ {x} → P x x reflexive)
  → (∀ {x y z} → (r+ : Refl-trans R x y) → (s+ : Refl-trans R y z)
     → P x y r+ → P y z s+
     → P x z (transitive r+ s+))
  → (∀ {x y} → (r+ : Refl-trans R x y) → is-prop (P x y r+))
  → ∀ {x y} → (r+ : Refl-trans R x y) → P x y r+
Refl-trans-elim {R = R} P prel prefl ptrans pprop r+ = go r+ where
  go : ∀ {x y} → (r+ : Refl-trans R x y) → P x y r+
  go [ r ] = prel r
  go reflexive = prefl
  go (transitive r+ s+) = ptrans r+ s+ (go r+) (go s+)
  go (trunc r+ r+' i) =
    is-prop→pathp (λ i → pprop (trunc r+ r+' i)) (go r+) (go r+') i
```
-->

Following the general theme, the recursion principle for the reflexive
transitive closure witnesses it's universal property; it is the smallest
reflexive and transitive relation containing $R$.

```agda
Refl-trans-rec
  : (S : A → A → Type ℓ)
  → (∀ {x y} → (r : R x y) → S x y)
  → (∀ {x} → S x x)
  → (∀ {x y z} → S x y → S y z → S x z)
  → (∀ {x y} → is-prop (S x y))
  → ∀ {x y} → Refl-trans R x y → S x y
Refl-trans-rec {R = R} S prel prefl ptrans pprop r+ = go r+ where
  go : ∀ {x y} → Refl-trans R x y → S x y
  go [ r ] = prel r
  go reflexive = prefl
  go (transitive r+ s+) = ptrans (go r+) (go s+)
  go (trunc r+ r+' i) = pprop (go r+) (go r+') i
```

We also provide a recursion principle that inducts down the length of the
chain of relations.

```agda
Refl-trans-rec-chain
  : (S : A → A → Type ℓ)
  → (∀ {x} → S x x)
  → (∀ {x y z} → R x y → Refl-trans R y z → S y z → S x z)
  → (∀ {x y} → is-prop (S x y))
  → ∀ {x y} → Refl-trans R x y → S x y
Refl-trans-rec-chain {R = R} S pnil pstep pprop r+ = go r+ reflexive pnil where
  go : ∀ {x y z} → Refl-trans R x y → Refl-trans R y z → S y z → S x z
  go [ x→y ] y→*z acc = pstep x→y y→*z acc
  go reflexive y→*z acc = acc
  go (transitive x→*x' x'→*y) y→*z acc =
    go x→*x' (transitive x'→*y y→*z) (go x'→*y y→*z acc)
  go (trunc x→*y x→*y' i) y→*z acc =
    pprop (go x→*y y→*z acc) (go x→*y' y→*z acc) i
```

We also provide an eliminator for inspecting forks.

```agda
Refl-trans-case-fork
  : (S : A → A → A → Type ℓ)
  → (∀ {a y} → Refl-trans R' a y → S a a y)
  → (∀ {a x} → Refl-trans R a x → S a x a)
  → (∀ {a x y x' y'}
     → R a x' → Refl-trans R x' x
     → R' a y' → Refl-trans R' y' y
     → S a x y)
  → (∀ {a x y} → is-prop (S a x y))
  → ∀ {a x y} → Refl-trans R a x → Refl-trans R' a y → S a x y
Refl-trans-case-fork {R' = R'} {R = R} S refll reflr fork prop {a} {x} {y} a→*x a→*y =
  Refl-trans-rec-chain (λ a x → Refl-trans R' a y → S a x y)
    refll
    (λ {a} {a'} {x} a→a' a'→*x _ a→*y →
      Refl-trans-rec-chain
        (λ a y → R a a' → Refl-trans R a' x → S a x y)
        (λ a→a' a'→*x → reflr (transitive [ a→a' ] a'→*x))
        (λ a→a' a'→*y _ a→a'' a''→*x → fork a→a'' a''→*x a→a' a'→*y)
        (Π-is-hlevel 1 (λ _ → Π-is-hlevel 1 λ _ → prop))
        a→*y a→a' a'→*x)
    (Π-is-hlevel 1 (λ _ → prop))
    a→*x a→*y
```

If the underlying relation is symmetric, then so is the
reflexive-transitive closure.

```agda
refl-trans-clo-symmetric : is-symmetric R → is-symmetric (Refl-trans R)
refl-trans-clo-symmetric {R = R} is-sym r+ =
  Refl-trans-rec (λ x y → Refl-trans R y x)
    (λ r → [ is-sym r ])
    reflexive
    (λ r+ s+ → transitive s+ r+)
    trunc
    r+
```

The reflexive closure and the transitive closure are contained in
the reflexive transitive closure.

```agda
refl-clo⊆refl-trans-clo : Refl R ⊆r Refl-trans R
refl-clo⊆refl-trans-clo {R = R} =
  Refl-rec (Refl-trans R) [_] (λ _ → reflexive) hlevel!

trans-clo⊆refl-trans-clo : Trans R ⊆r Refl-trans R
trans-clo⊆refl-trans-clo {R = R} =
  Trans-rec (Refl-trans R) [_] transitive hlevel!
```


Note that the reflexive-transitive closure is equivalent to taking
the reflexive closure of the transitive closure.

```agda
refl-clo-trans-clo⊆refl-trans-clo : Refl (Trans R) ⊆r Refl-trans R
refl-clo-trans-clo⊆refl-trans-clo {R = R} =
  Refl-rec (Refl-trans R)
    trans-clo⊆refl-trans-clo
    (λ _ → reflexive)
    hlevel!

refl-trans-clo⊆refl-clo-trans-clo : Refl-trans R ⊆r Refl (Trans R)
refl-trans-clo⊆refl-clo-trans-clo {R = R} =
  Refl-trans-rec (Refl (Trans R))
    (λ x~y → [ [ x~y ] ])
    reflexive
    (refl-clo-transitive transitive)
    hlevel!

refl-clo-trans-clo≡refl-trans-clo : Refl (Trans R) ≡ Refl-trans R
refl-clo-trans-clo≡refl-trans-clo {R = R} =
  prop-rel-ext trunc trunc
    refl-clo-trans-clo⊆refl-trans-clo
    refl-trans-clo⊆refl-clo-trans-clo
```

The same can be said for the transitive closure of the reflexive closure.

```agda
trans-clo-refl-clo⊆refl-trans-clo : Trans (Refl R) ⊆r Refl-trans R
trans-clo-refl-clo⊆refl-trans-clo {R = R} =
  Trans-rec (Refl-trans R)
    refl-clo⊆refl-trans-clo
    transitive
    hlevel!

refl-trans-clo⊆trans-clo-refl-clo : Refl-trans R ⊆r Trans (Refl R)
refl-trans-clo⊆trans-clo-refl-clo {R = R} =
  Refl-trans-rec (Trans (Refl R))
    (λ x~y → [ [ x~y ] ])
    [ reflexive ]
    transitive
    hlevel!

trans-clo-refl-clo≡refl-trans-clo : Trans (Refl R) ≡ Refl-trans R
trans-clo-refl-clo≡refl-trans-clo {R = R} =
  prop-rel-ext trunc trunc
    trans-clo-refl-clo⊆refl-trans-clo
    refl-trans-clo⊆trans-clo-refl-clo
```


## Reflexive-Symmetric-Transitive Closure

Finally, the reflexive-symmetric-transitive closure of a relation $R$ is
the smallest reflexive, symmetric, and transitive relation
$R^{\leftrightarrow*}$ that contains $R$.

```agda
data Refl-sym-trans {A : Type ℓ} (R : A → A → Type ℓ') (x : A) : A → Type (ℓ ⊔ ℓ') where
  [_] : ∀ {y} → R x y → Refl-sym-trans R x y
  reflexive : Refl-sym-trans R x x
  symmetric : ∀ {y} → Refl-sym-trans R y x → Refl-sym-trans R x y
  transitive : ∀ {y z} → Refl-sym-trans R x y → Refl-sym-trans R y z → Refl-sym-trans R x z
  trunc : ∀ {y} → is-prop (Refl-sym-trans R x y)
```

<!--
```agda
instance
  Refl-sym-trans-H-Level : ∀ {x y} {n} → H-Level (Refl-sym-trans R x y) (suc n)
  Refl-sym-trans-H-Level = prop-instance trunc

Refl-sym-trans-elim
  : (P : ∀ (x y : A) → Refl-sym-trans R x y → Type ℓ'')
  → (∀ {x y} → (r : R x y) → P x y [ r ])
  → (∀ {x} → P x x reflexive)
  → (∀ {x y} → (r+ : Refl-sym-trans R x y)
     → P x y r+ → P y x (symmetric r+))
  → (∀ {x y z} → (r+ : Refl-sym-trans R x y) → (s+ : Refl-sym-trans R y z)
     → P x y r+ → P y z s+
     → P x z (transitive r+ s+))
  → (∀ {x y} → (r+ : Refl-sym-trans R x y) → is-prop (P x y r+))
  → ∀ {x y} → (r+ : Refl-sym-trans R x y) → P x y r+
Refl-sym-trans-elim {R = R} P prel prefl psym ptrans pprop r+ = go r+ where
  go : ∀ {x y} → (r+ : Refl-sym-trans R x y) → P x y r+
  go [ r ] = prel r
  go reflexive = prefl
  go (symmetric r) = psym r (go r)
  go (transitive r+ s+) = ptrans r+ s+ (go r+) (go s+)
  go (trunc r+ r+' i) =
    is-prop→pathp (λ i → pprop (trunc r+ r+' i)) (go r+) (go r+') i
```
-->

Yet again, the recursion principle for the reflexive, symmetric,
transitive closure witnesses it's universal property; it is the smallest
reflexive, symmetric, transitive relation containing $R$.

```agda
Refl-sym-trans-rec
  : (S : A → A → Type ℓ)
  → (∀ {x y} → (r : R x y) → S x y)
  → (∀ {x} → S x x)
  → (∀ {x y} → S x y → S y x)
  → (∀ {x y z} → S x y → S y z → S x z)
  → (∀ {x y} → is-prop (S x y))
  → ∀ {x y} → Refl-sym-trans R x y → S x y
Refl-sym-trans-rec {R = R} S prel prefl psym ptrans pprop r+ = go r+ where
  go : ∀ {x y} → Refl-sym-trans R x y → S x y
  go [ r ] = prel r
  go reflexive = prefl
  go (symmetric r) = psym (go r)
  go (transitive r+ s+) = ptrans (go r+) (go s+)
  go (trunc r+ r+' i) = pprop (go r+) (go r+') i
```

We also define an alternative recursion principle for inducting down
the length of the chain of relations.

```agda
Refl-sym-trans-rec-chain
  : (S : A → A → Type ℓ)
  → (∀ {x} → S x x)
  → (∀ {x y z} → R x y → Refl-sym-trans R y z → S y z → S x z)
  → (∀ {x y z} → R y x → Refl-sym-trans R y z → S y z → S x z)
  → (∀ {x y} → is-prop (S x y))
  → ∀ {x y} → Refl-sym-trans R x y → S x y
Refl-sym-trans-rec-chain {R = R} S pnil pstep pinv pprop r+ = go r+ reflexive pnil where
  go : ∀ {x y z} → Refl-sym-trans R x y → Refl-sym-trans R y z → S y z → S x z
  go-sym : ∀ {x y z} → Refl-sym-trans R y x → Refl-sym-trans R y z → S y z → S x z

  go [ x→y ] y→*z acc = pstep x→y y→*z acc
  go reflexive y→*z acc = acc
  go (symmetric y→*x) y→*z acc = go-sym y→*x y→*z acc
  go (transitive x→*x' x'→*y) y→*z acc =
    go x→*x' (transitive x'→*y y→*z) (go x'→*y y→*z acc)
  go (trunc x→*y x→*y' i) y→*z acc =
    pprop (go x→*y y→*z acc) (go x→*y' y→*z acc) i

  go-sym [ y→x ] y→*z acc = pinv y→x y→*z acc
  go-sym reflexive y→*z acc = acc
  go-sym (symmetric x→*y) y→*z acc = go x→*y y→*z acc
  go-sym (transitive y→*y' y'→*x) y→*z acc =
    go-sym y'→*x (transitive (symmetric y→*y') y→*z) (go-sym y→*y' y→*z acc)
  go-sym (trunc y→*x y→*x' i) y→*z acc =
    pprop (go-sym y→*x y→*z acc) (go-sym y→*x' y→*z acc) i
```

The reflexive-transitive closure embeds into the reflexive symmetric
transitive closure.

```agda
refl-trans⊆refl-sym-trans
  : Refl-trans R ⊆r Refl-sym-trans R
refl-trans⊆refl-sym-trans =
  Refl-trans-rec (Refl-sym-trans _) [_] reflexive transitive trunc
```
