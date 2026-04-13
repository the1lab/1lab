<!--
```agda
open import 1Lab.Reflection.Induction
open import 1Lab.Prelude

open import Data.Nat.Base
open import Data.Sum.Base
open import Data.Dec

import 1Lab.Reflection

open 1Lab.Reflection using (Idiom-TC ; lit ; nat ; con₀)
```
-->

```agda
module Data.Finset.Base where
```

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A B C : Type ℓ
```
-->

# Finitely indexed subsets

We define a type of Kuratowski-finite subsets of a type $A$, as a
higher inductive type mirroring the definition of lists, but with
generating equations which allow removing duplicates and reordering
elements. Note that we must also truncate the resulting type to make
sure we end up with something homotopically coherent.

As the name of the module implies, this is an alternative presentation
of [[Kuratowski finite subsets]] of $A$, i.e. subsets of $A$ whose total
space admits a surjection from some [[standard finite set]], which makes
working with the elements more convenient --- as long as we can express
the operation we're doing with the subsets is invariant under repetition
and swapping (i.e. we're mapping into a [[join semilattice]]).

```agda
infixr 20 _∷_

data Finset {ℓ} (A : Type ℓ) : Type ℓ where
  []    : Finset A
  _∷_   : (x : A) (xs : Finset A) → Finset A

  ∷-dup  : ∀ x xs   → (x ∷ x ∷ xs) ≡ (x ∷ xs)
  ∷-swap : ∀ x y xs → (x ∷ y ∷ xs) ≡ (y ∷ x ∷ xs)

  squash : is-set (Finset A)
```

Note that, since these are *equations* (rather than a separate
equivalence relation on lists), we do not need to add path constructors
saying that we can reorder elements deep in the list:

<!--
```agda
private module _ {A : Type ℓ} {w x y z : A} where
```
-->

```agda
  _ : Path (Finset A) (w ∷ x ∷ y ∷ z ∷ []) (w ∷ x ∷ y ∷ y ∷ z ∷ [])
  _ = ap (λ e → w Finset.∷ x Finset.∷ e) (sym (∷-dup y (z ∷ [])))
```

<!--
```agda
Finset-elim-prop
  : ∀ {ℓ ℓ'} {A : Type ℓ} (P : Finset A → Type ℓ')
  → ⦃ ∀ {x} → H-Level (P x) 1 ⦄
  → P []
  → (∀ x {xs} → P xs → P (x ∷ xs))
  → ∀ x → P x
Finset-elim-prop P p[] p∷ [] = p[]
Finset-elim-prop P p[] p∷ (x ∷ xs) = p∷ x (Finset-elim-prop P p[] p∷ xs)
Finset-elim-prop P p[] p∷ (∷-dup x xs i) =
  is-prop→pathp (λ i → hlevel {T = P (∷-dup x xs i)} 1) (p∷ _ (p∷ _ (Finset-elim-prop P p[] p∷ xs))) (p∷ _ (Finset-elim-prop P p[] p∷ xs)) i
Finset-elim-prop P p[] p∷ (∷-swap x y xs i) =
  is-prop→pathp (λ i → hlevel {T = P (∷-swap x y xs i)} 1)
    (p∷ _ (p∷ _ (Finset-elim-prop P p[] p∷ xs)))
    (p∷ _ (p∷ _ (Finset-elim-prop P p[] p∷ xs))) i
Finset-elim-prop P p[] p∷ (squash x y p q i j) =
  let go = Finset-elim-prop P p[] p∷ in
    is-prop→squarep (λ i j → hlevel {T = P (squash x y p q i j)} 1)
      (λ i → go x) (λ i → go (p i)) (λ i → go (q i)) (λ i → go y) i j

unquoteDecl Finset-rec = make-rec-n 2 Finset-rec (quote Finset)

instance
  H-Level-Finset : ∀ {n} → H-Level (Finset A) (2 + n)
  H-Level-Finset = basic-instance 2 squash

open 1Lab.Reflection using (List ; [] ; _∷_)
```
-->

Of course, since finite sets and lists have the same point constructors,
we can turn any list into a finite set.

```agda
from-list : List A → Finset A
from-list []       = []
from-list (x ∷ xs) = x ∷ from-list xs
```

Moreover, we can show that this function is surjective; this implies
that the type of finite sets (over a set $A$) is a quotient of the type
of lists of $A$.

```agda
from-list-is-surjective : is-surjective (from-list {A = A})
from-list-is-surjective = Finset-elim-prop _
  (inc ([] , refl))
  (λ x → rec! λ xs p → inc (x ∷ xs , ap (x ∷_) p))
```

## Basic operations

We can replicate the definition of basic list operations on finite sets
essentially as-is, as long as we can prove that they respect the
generating paths --- that is, as long as whatever we choose to "replace
`_∷_`{.Agda} with" is also idempotent and allows swapping on the left.
For a basic example, we can swap conses with conses, to implement
`map`{.Agda}:

```agda
mapᶠˢ : (A → B) → Finset A → Finset B
mapᶠˢ f []                   = []
mapᶠˢ f (x ∷ xs)             = f x ∷ mapᶠˢ f xs
mapᶠˢ f (∷-dup  x   xs i)    = ∷-dup (f x) (mapᶠˢ f xs) i
mapᶠˢ f (∷-swap x y xs i)    = ∷-swap (f x) (f y) (mapᶠˢ f xs) i
mapᶠˢ f (squash x y p q i j) = squash (mapᶠˢ f x) (mapᶠˢ f y) (λ i → mapᶠˢ f (p i)) (λ i → mapᶠˢ f (q i)) i j
```

<!--
```agda
instance
  Map-Finset : Map (eff Finset)
  Map-Finset = record { map = mapᶠˢ }
{-# DISPLAY mapᶠˢ f xs = map f xs #-}
```
-->

We can also implement `filter`{.Agda}, since at the end of the day we're
once again replacing conses with conses.

```agda
cons-if : Dec B → A → Finset A → Finset A
cons-if (yes _) x xs = x ∷ xs
cons-if (no _)  x xs = xs

filter : (P : A → Type ℓ) ⦃ _ : ∀ {x} → Dec (P x) ⦄ → Finset A → Finset A
filter f [] = []
filter f (x ∷ xs) = cons-if (holds? (f x)) x (filter f xs)
filter f (∷-dup x xs i) with holds? (f x)
... | yes _ = ∷-dup x (filter f xs) i
... | no _ = filter f xs
filter f (∷-swap x y xs i) with holds? (f x) | holds? (f y)
... | yes _ | yes _  = ∷-swap x y (filter f xs) i
... | yes _ | no _   = x ∷ filter f xs
... | no _  | yes _  = y ∷ filter f xs
... | no _  | no _   = filter f xs
filter f (squash x y p q i j) = squash (filter f x) (filter f y) (λ i → filter f (p i)) (λ i → filter f (q i)) i j
```

Finally, we can implement an append operation --- called `union` because
of its semantics as a subset --- since we're keeping all the conses and
replacing `[]`{.Agda} with a different finset.

```agda
union : Finset A → Finset A → Finset A
union []                     ys = ys
union (x ∷ xs)               ys = x ∷ union xs ys
union (∷-dup  x   xs i)      ys = ∷-dup x (union xs ys) i
union (∷-swap x y xs i)      ys = ∷-swap x y (union xs ys) i
union (squash xs ys p q i j) zs = squash (union xs zs) (union ys zs) (λ i → union (p i) zs) (λ i → union (q i) zs) i j
```

<!--
```agda
instance
  Append-Sub : Append (Finset A)
  Append-Sub = record { _<>_ = union ; mempty = [] }
```
-->

### Properties of union

One downside of the higher-inductive definition is that if we want to
define operations on finsets which use `union`{.Agda}, we'll have to
prove that it behaves sufficiently like `_∷_`{.Agda}. In particular, we
prove that it's a *semilattice*, which is sufficient (though more than
necessary) to imply it is idempotent and allows swapping on the left.

All of these proofs are by induction on the leftmost finite set. Since
we're showing a proposition, it suffices to consider the point
constructors, in which case we essentially have the same proofs as for
lists (though written in higher-order style).

```agda
abstract
  union-assoc : (xs ys zs : Finset A) → xs <> (ys <> zs) ≡ (xs <> ys) <> zs
  union-assoc = Finset-elim-prop _
    (λ ys zs → refl)
    (λ x ih ys zs → ap (x ∷_) (ih ys zs))

  union-idr : (xs : Finset A) → xs <> [] ≡ xs
  union-idr = Finset-elim-prop _ refl λ x p → ap (x ∷_) p

  union-consr : (x : A) (xs ys : Finset A) → xs <> (x ∷ ys) ≡ (x ∷ xs) <> ys
  union-consr x = Finset-elim-prop _ (λ ys → refl)
    λ y ih ys → ap (y ∷_) (ih ys) ∙ ∷-swap _ _ _

  union-comm : (xs ys : Finset A) → xs <> ys ≡ ys <> xs
  union-comm = Finset-elim-prop _ (λ ys → sym (union-idr ys))
    λ x {xs} ih ys → sym (union-consr x ys xs ∙ ap (x ∷_) (sym (ih ys)))

  union-idem : (xs : Finset A) → xs <> xs ≡ xs
  union-idem = Finset-elim-prop _ refl
    λ x {xs} ih → ap (x ∷_) (union-consr x xs xs) ∙∙ ∷-dup _ _ ∙∙ ap (x ∷_) ih

  union-dup : (xs ys : Finset A) → xs <> (xs <> ys) ≡ xs <> ys
  union-dup xs ys = union-assoc xs xs ys ∙ ap (_<> ys) (union-idem xs)

  union-swap : (xs ys zs : Finset A) → xs <> (ys <> zs) ≡ ys <> (xs <> zs)
  union-swap xs ys zs = union-assoc xs ys zs ∙∙ ap (_<> zs) (union-comm xs ys) ∙∙ sym (union-assoc ys xs zs)
```

### More basic operations

With these paths in hand, we can prove that `Finset`{.Agda} is a monad
on sets. First, we show how to flatten a finite set of finite sets, by
applying iterated unions.

```agda
concat : Finset (Finset A) → Finset A
concat []                = []
concat (x ∷ xs)          = x <> concat xs
concat (∷-dup x xs i)    = union-dup x (concat xs) i
concat (∷-swap x y xs i) = union-swap x y (concat xs) i
concat (squash x y p q i j) = squash
  (concat x) (concat y) (λ i → concat (p i)) (λ i → concat (q i)) i j
```

We can then define a couple more operations familiar to functional
programmers.

```agda
_<*>ᶠˢ_ : Finset (A → B) → Finset A → Finset B
[]                 <*>ᶠˢ xs = []
(f ∷ fs)           <*>ᶠˢ xs = mapᶠˢ f xs <> (fs <*>ᶠˢ xs)
∷-dup f fs i       <*>ᶠˢ xs = union-dup (map f xs) (fs <*>ᶠˢ xs) i
∷-swap f g fs i    <*>ᶠˢ xs = union-swap (map f xs) (map g xs) (fs <*>ᶠˢ xs) i
squash f g p q i j <*>ᶠˢ xs = squash
  (f <*>ᶠˢ xs) (g <*>ᶠˢ xs) (λ i → p i <*>ᶠˢ xs) (λ i → q i <*>ᶠˢ xs) i j

_>>=ᶠˢ_ : Finset A → (A → Finset B) → Finset B
[]                 >>=ᶠˢ f = []
(x ∷ xs)           >>=ᶠˢ f = f x <> (xs >>=ᶠˢ f)
∷-dup x xs i       >>=ᶠˢ f = union-dup (f x) (xs >>=ᶠˢ f) i
∷-swap x y xs i    >>=ᶠˢ f = union-swap (f x) (f y) (xs >>=ᶠˢ f) i
squash x y p q i j >>=ᶠˢ f = squash
  (x >>=ᶠˢ f) (y >>=ᶠˢ f) (λ i → p i >>=ᶠˢ f) (λ i → q i >>=ᶠˢ f) i j
```

<!--
```agda
sigma : {P : A → Type ℓ} → Finset A → (∀ x → Finset (P x)) → Finset (Σ A P)
sigma []                   f = []
sigma (x ∷ xs)             f = map (x ,_) (f x) <> sigma xs f
sigma (∷-dup x xs i)       f = union-dup (map (x ,_) (f x)) (sigma xs f) i
sigma (∷-swap x y xs i)    f = union-swap (map (x ,_) (f x)) (map (y ,_) (f y)) (sigma xs f) i
sigma (squash x y p q i j) f = squash (sigma x f) (sigma y f) (λ i → sigma (p i) f) (λ i → sigma (q i) f) i j

instance
  Idiom-Finset : Idiom (eff Finset)
  Idiom-Finset = record { pure = _∷ [] ; _<*>_ = _<*>ᶠˢ_ }

  Bind-Sub : Bind (eff Finset)
  Bind-Sub .Bind._>>=_ xs f = snd <$> sigma xs f
  Bind-Sub .Bind.Idiom-bind = Idiom-Finset

{-# DISPLAY _<*>ᶠˢ_ fs xs = fs <*> xs #-}
```
-->

## Membership

<!--
```agda
private
  abstract
    dup  : (P Q : Type ℓ) → ∥ P ⊎ ∥ P ⊎ Q ∥ ∥ ≡ ∥ P ⊎ Q ∥
    dup P Q = ua $ prop-ext!
      (_>>= λ { (inl x) → inc (inl x) ; (inr x) → x })
      (_>>= λ { (inl x) → inc (inl x) ; (inr x) → inc (inr (inc (inr x))) })

    swap : (P Q R : Type ℓ) → ∥ P ⊎ ∥ Q ⊎ R ∥ ∥ ≡ ∥ Q ⊎ ∥ P ⊎ R ∥ ∥
    swap P Q R = ua $ prop-ext!
      (_>>= λ where
        (inl x) → inc (inr (inc (inl x)))
        (inr x) → x >>= λ where
          (inl x) → inc (inl x)
          (inr x) → inc (inr (inc (inr x))))
      (_>>= λ where
        (inl x) → inc (inr (inc (inl x)))
        (inr x) → x >>= λ where
          (inl x) → inc (inl x)
          (inr x) → inc (inr (inc (inr x))))
```
-->

We now show how to define membership for finite sets. Since we have to
map into a set (to handle the `squash`{.Agda} constructor), we have to
make the result a proposition. Therefore, the definition of $x \in (y ∷
xs)$ has to be truncated.

```agda
  finset-mem : A → Finset A → Prop (level-of A)
  finset-mem x []                .∣_∣ = Lift _ ⊥
  finset-mem x (y ∷ xs)          .∣_∣ = ∥ (x ≡ᵢ y) ⊎ ⌞ finset-mem x xs ⌟ ∥
  finset-mem x (∷-dup  y   xs i) .∣_∣ = dup (x ≡ᵢ y) ⌞ finset-mem x xs ⌟ i
  finset-mem x (∷-swap y z xs i) .∣_∣ = swap (x ≡ᵢ y) (x ≡ᵢ z) ⌞ finset-mem x xs ⌟ i
```

<!--
```agda
  finset-mem x [] .is-tr = hlevel 1
  finset-mem x (y ∷ xs) .is-tr = squash
  finset-mem x (∷-swap y z xs i) .is-tr = is-prop→pathp
    (λ i → is-prop-is-prop {A = swap (x ≡ᵢ y) (x ≡ᵢ z) ⌞ finset-mem x xs ⌟ i}) squash squash i
  finset-mem x (∷-dup y xs i) .is-tr = is-prop→pathp
    (λ i → is-prop-is-prop {A = dup (x ≡ᵢ y) ⌞ finset-mem x xs ⌟ i}) squash squash i
  finset-mem x (squash xs ys p q i j) =
    n-Type-is-hlevel 1
      (finset-mem x xs) (finset-mem x ys)
      (λ i → finset-mem x (p i)) (λ i → finset-mem x (q i)) i j

record _∈ᶠˢ_ (x : A) (xs : Finset A) : Type (level-of A) where
  constructor lift
  field
    lower : ⌞ finset-mem x xs ⌟

open _∈ᶠˢ_ public

instance unquoteDecl H-Level-∈ᶠˢ = declare-record-hlevel 1 H-Level-∈ᶠˢ (quote _∈ᶠˢ_)

hereₛ' : ∀ {x y : A} {xs} → x ≡ᵢ y → x ∈ᶠˢ (y ∷ xs)
hereₛ' p = lift (inc (inl p))

hereₛ : ∀ {x : A} {xs} → x ∈ᶠˢ (x ∷ xs)
hereₛ = hereₛ' reflᵢ

thereₛ : ∀ {x y : A} {xs} → y ∈ᶠˢ xs → y ∈ᶠˢ (x ∷ xs)
thereₛ (lift x) = lift (inc (inr x))

abstract
  ¬mem-[] : {x : A} → ¬ (x ∈ᶠˢ [])
  ¬mem-[] ()

instance
  Membership-Finset : Membership A (Finset A) _
  Membership-Finset = record { _∈_ = _∈ᶠˢ_ }

  Underlying-Finset : Underlying (Finset A)
  Underlying-Finset = record { ⌞_⌟ = ∫ₚ }
```
-->

We can then define a *case analysis* principle for membership in a
finite set, as long as we're showing a proposition.

```agda
∈ᶠˢ-split
  : ∀ {ℓp} {x y : A} {xs} {P : x ∈ᶠˢ (y ∷ xs) → Type ℓp} ⦃ _ : ∀ {x} → H-Level (P x) 1 ⦄
  → ((p : x ≡ᵢ y) → P (hereₛ' p))
  → ((w : x ∈ᶠˢ xs) → P (thereₛ w))
  → (w : x ∈ᶠˢ (y ∷ xs)) → P w
∈ᶠˢ-split {P = P} l r (lift x) = ∥-∥-elim {P = λ v → P (lift v)} (λ x → hlevel 1)
  (λ where
    (inl a) → l a
    (inr b) → r (lift b))
  x
```

<!--
```agda
there-cons-if : (d : Dec B) (x y : A) (xs : Finset A) → y ∈ xs → y ∈ cons-if d x xs
there-cons-if (yes a) x y xs p = thereₛ p
there-cons-if (no ¬a) x y xs p = p

∈ᶠˢ-case
  : ∀ {ℓp} {x y : A} {xs} {P : Type ℓp} ⦃ _ : H-Level P 1 ⦄
  → (w : x ∈ᶠˢ (y ∷ xs)) → ((p : x ≡ᵢ y) → P) → ((w : x ∈ᶠˢ xs) → P) → P
∈ᶠˢ-case {P = P} w f g = ∈ᶠˢ-split {P = λ _ → P} f g w
```
-->

Putting this together with induction over finite sets, we can show that
the membership type behaves as though it were an inductive family.

```agda
∈ᶠˢ-elim
  : ∀ {ℓp} {x : A} (P : ∀ xs → x ∈ᶠˢ xs → Type ℓp) ⦃ _ : ∀ {xs p} → H-Level (P xs p) 1 ⦄
  → (∀ {xs}              → P (x ∷ xs) hereₛ)
  → (∀ {y xs} q → P xs q → P (y ∷ xs) (thereₛ q))
  → ∀ xs w → P xs w
∈ᶠˢ-elim {x = x} P phere pthere xs w = Finset-elim-prop (λ xs → (w : x ∈ᶠˢ xs) → P xs w)
  (λ m → absurd (¬mem-[] m))
  (λ y {xs'} ind → ∈ᶠˢ-split {P = P (y ∷ xs')}
    (λ { reflᵢ → phere })
    λ w → pthere w (ind w))
  xs w
```

### Over discrete types

We'll show that membership in a finite set is decidable, as long as the
type of elements is [[discrete]]. First, note that we're showing a
[[proposition]], so all the path cases will be automatic.

```agda
instance
  Dec-∈ᶠˢ : ⦃ _ : Discrete A ⦄ {x : A} {xs : Finset A} → Dec (x ∈ xs)
  Dec-∈ᶠˢ {A = A} ⦃ eq ⦄ {x = x} {xs} = go xs where
    abstract
      p : (xs : Finset A) → is-prop (Dec (x ∈ xs))
      p xs = hlevel 1
```

We'll start with our inductive case: if we're looking at a finite set of
the form $y ∷ xs$, we can put together a decision for $x \in (y ∷ xs)$
out of a decision for whether $x = y$ and a decision for whether $x \in
xs$.

```agda
    cons-mem
      : (y : A) (xs : Finset A)
      → Dec (x ≡ᵢ y)
      → Dec ⌞ x ∈ xs ⌟
      → Dec ⌞ x ∈ (y ∷ xs) ⌟
```

Note that, even though $x$ may also appear in $xs$, if it's at the head
position, we'll always return the "earlier" proof of membership --- this
matters when computing, even though we're dealing with propositions!.

```agda
    cons-mem y xs (yes p) _       = yes (hereₛ' p)
    cons-mem y xs (no ¬p) (yes p) = yes (thereₛ p)
    cons-mem y xs (no ¬p) (no ¬q) = no (∈ᶠˢ-split ¬p ¬q)
```

Finally, the base case is automatic: there are no elements in the empty
finite set.

```agda
    go : (xs : Finset A) → Dec (x ∈ xs)
    go = Finset-elim-prop _
      (no ¬mem-[])
      (λ y {xs} rest → cons-mem y xs (x ≡ᵢ? y) rest)
```

## Cardinality

To close out this basic module, we show how to count the elements of a
finite set. In a list, you simply count the number of `_∷_`{.Agda}
constructors, but here, we must respect duplicates and swaps. This means
that, at each element, we must only add one to the count if the element
does not appear in the tail of the list. This implies that we can only
count the number of elements in a finite set with discrete carrier; it
also implies that computing the size of a `Finset` is *quadratic* in the
number of equality tests.

```agda
module _ {A : Type ℓ} ⦃ d : Discrete A ⦄ where
  count : Finset A → Nat

  private
    has : (x : A) (xs : Finset A) → Dec (x ∈ xs)
    has x xs = holds? (x ∈ xs)

    cons : A → Finset A → Nat
    cons x xs = Dec-rec (λ _ → count xs) (λ _ → suc (count xs)) (has x xs)

    cons-dup  : ∀ x xs → cons x (x ∷ xs) ≡ cons x xs
    cons-swap : ∀ x y xs → cons x (y ∷ xs) ≡ cons y (x ∷ xs)

  count []       = 0
  count (x ∷ xs) = cons x xs
  count (∷-dup x xs i) = cons-dup x xs i
  count (∷-swap x y xs i) = cons-swap x y xs i
  count (squash x y p q i j) = hlevel 2 (count x) (count y) (λ i → count (p i)) (λ i → count (q i)) i j
```

<details>
<summary>Showing the necessary respect for the generating equations
boils down to a billion case splits.</summary>

```agda
  cons-dup x xs with has x xs
  cons-dup x xs | yes p with has x (x ∷ xs)
  cons-dup x xs | yes p | yes q = refl
  cons-dup x xs | yes p | no ¬p = absurd (¬p hereₛ)
  cons-dup x xs | no ¬p with has x (x ∷ xs)
  cons-dup x xs | no ¬p | yes q = refl
  cons-dup x xs | no ¬p | no ¬q = absurd (¬q hereₛ)

  cons-swap x y xs with has x (y ∷ xs) | has y (x ∷ xs) | has x xs | has y xs
  ... | yes p | yes q | yes r | yes s = refl
  ... | yes p | yes q | no ¬r | no ¬s = refl
  ... | yes p | no ¬q | yes r | no ¬s = refl
  ... | no ¬p | yes q | no ¬r | yes s = refl
  ... | no ¬p | no ¬q | yes r | yes s = refl
  ... | no ¬p | no ¬q | no ¬r | no ¬s = refl
  ... | yes p | yes q | yes r | no ¬s = ∈ᶠˢ-split (λ { reflᵢ → absurd (¬s r) }) (λ w → absurd (¬s w)) q
  ... | yes p | yes q | no ¬r | yes s = ∈ᶠˢ-split (λ { reflᵢ → absurd (¬r s) }) (λ w → absurd (¬r w)) p
  ... | yes p | no ¬q | yes r | yes s = absurd (¬q (thereₛ s))
  ... | yes p | no ¬q | no ¬r | yes s = absurd (¬q (thereₛ s))
  ... | yes p | no ¬q | no ¬r | no ¬s = ∈ᶠˢ-split (λ { reflᵢ → absurd (¬q p) }) (λ w → absurd (¬r w)) p
  ... | no ¬p | yes q | yes r | yes s = ∈ᶠˢ-split (λ { reflᵢ → absurd (¬p q) }) (λ w → absurd (¬p ((thereₛ r)))) q
  ... | no ¬p | yes q | yes r | no ¬s = absurd (¬p (thereₛ r))
  ... | no ¬p | yes q | no ¬r | no ¬s = ∈ᶠˢ-split (λ { reflᵢ → absurd (¬p q) }) (λ w → absurd (¬s w)) q
  ... | no ¬p | no ¬q | yes r | no ¬s = absurd (¬p (thereₛ r))
  ... | no ¬p | no ¬q | no ¬r | yes s = absurd (¬q (thereₛ s))
```
</summary>

<!--
```agda
intersection : ⦃ _ : Discrete A ⦄ → Finset A → Finset A → Finset A
intersection [] ys = []
intersection (x ∷ xs) ys = cons-if (holds? (x ∈ ys)) x (intersection xs ys)
intersection (∷-dup x xs i) ys with holds? (x ∈ ys)
... | yes p = ∷-dup x (intersection xs ys) i
... | no ¬p = intersection xs ys
intersection (∷-swap x y xs i) ys with holds? (x ∈ ys) | holds? (y ∈ ys)
... | yes a | yes b = ∷-swap x y (intersection xs ys) i
... | yes a | no ¬b = x ∷ intersection xs ys
... | no ¬a | yes b = y ∷ intersection xs ys
... | no ¬a | no ¬b = intersection xs ys
intersection (squash a b p q i j) ys = squash (intersection a ys) (intersection b ys) (λ i → intersection (p i) ys) (λ i → intersection (q i) ys) i j

finset-all : (P : A → Type ℓ) ⦃ _ : ∀ {x} → H-Level (P x) 1 ⦄ → Finset A → Prop ℓ
finset-all P [] = el! (Lift _ ⊤)
finset-all P (x ∷ xs) = el! (P x × ⌞ finset-all P xs ⌟)
finset-all P (∷-dup x xs i) = n-ua {X = el! (P x × P x × ⌞ finset-all P xs ⌟)} {Y = el! (P x × ⌞ finset-all P xs ⌟)} (prop-ext! snd λ (a , b) → a , a , b) i
finset-all P (∷-swap x y xs i) = n-ua {X = el! (P x × P y × ⌞ finset-all P xs ⌟)} {Y = el! (P y × P x × ⌞ finset-all P xs ⌟)} (prop-ext! (λ (a , b , c) → b , a , c) (λ (a , b , c) → b , a , c)) i
finset-all P (squash x y p q i j) = hlevel 2 (finset-all P x) (finset-all P y) (λ i → finset-all P (p i)) (λ i → finset-all P (q i)) i j

opaque
  All : (P : A → Type ℓ) ⦃ _ : ∀ {x} → H-Level (P x) 1 ⦄ → Finset A → Type ℓ
  All P xs = ⌞ finset-all P xs ⌟

  private
    all-hlevel : ∀ {P : A → Type ℓ} ⦃ _ : ∀ {x} → H-Level (P x) 1 ⦄ {xs : Finset A} → ⊤ → is-prop (All P xs)
    all-hlevel {P = P} {xs = xs} tt = finset-all P xs .is-tr

instance
  hlevel-proj-all : hlevel-projection (quote All)
  hlevel-proj-all .hlevel-projection.has-level = quote all-hlevel
  hlevel-proj-all .hlevel-projection.get-level x = pure (lit (nat 1))
  hlevel-proj-all .hlevel-projection.get-argument x = pure (con₀ (quote tt))

module _ {P : A → Type ℓ} ⦃ _ : ∀ {x} → H-Level (P x) 1 ⦄ where opaque
  unfolding All

  all-cons : {x : A} {xs : Finset A} → P x → All P xs → All P (x ∷ xs)
  all-cons = _,_

  all-nil : All P []
  all-nil = lift tt

  to-all : (xs : Finset A) → (∀ x → x ∈ xs → P x) → All P xs
  to-all = Finset-elim-prop _ (λ _ → lift tt) (λ x {xs} ind w → w x hereₛ , ind (λ x xs → w x (thereₛ xs)))

  from-all : {x : A} (xs : Finset A) → All P xs → x ∈ xs → P x
  from-all {x = x} xs all elt =
    ∈ᶠˢ-elim (λ xs _ → All P xs → P x) fst (λ _ ind (_ , a) → ind a) xs elt all

{-# DISPLAY all-cons x xs = x ∷ xs #-}
{-# DISPLAY all-nil = [] #-}
```
-->
