<!--
```agda
open import 1Lab.Reflection.List
open import 1Lab.Path.Cartesian
open import 1Lab.Prelude

open import Data.Maybe.Properties
open import Data.List.Membership
open import Data.Set.Coequaliser
open import Data.Fin.Properties
open import Data.Fin.Closure
open import Data.Fin.Product
open import Data.List.Sigma
open import Data.Bool.Base
open import Data.List.Base
open import Data.Fin.Base
open import Data.Nat.Base
open import Data.List.Pi
open import Data.Maybe
open import Data.Dec
open import Data.Sum
```
-->

```agda
module Data.Fin.Finite where
```

<!--
```agda
private variable
  ℓ ℓ' : Level
  A B C : Type ℓ
  P Q : A → Type ℓ
```
-->

# Finite types

The notion of *finite set* in univalent mathematics is slightly more
subtle than even in ordinary constructive mathematics. While we have
defined the [[standard finite sets]] $[n]$, we can not immediately
extend that definition to a [[proposition]] "$A$ is finite" for a type
$A$. In particular, as is common in constructive mathematics, there are
many inequivalent ways that a type $A$ can be related to some
$\operatorname{Fin}(n)$ which all collapse when passing to classical
mathematics.

In particular, we say that a set $A$ is

* **(Bishop) finite** if we have an [[equivalence]] $e : A \simeq [n]$;

*
  [[**Finitely indexed**|kuratowski finite subset]] (or **Kuratowski
  finite**) if we have a [[surjection]] $s : [n] \epi A$, i.e. if $A$ is
  a [[quotient]] of a standard finite set;

*
  **Subfinite** if we have an [[embedding]] $s : A \mono [n]$, i.e. if
  $A$ is a subset of a standard finite set;

*
  **Subfinitely indexed** if we have a span

  ~~~{.quiver}
  \[\begin{tikzcd}[ampersand replacement=\&]
    B \&\& A \\
    \\
    {[n]\text{,}}
    \arrow[two heads, from=1-1, to=1-3]
    \arrow[hook, from=1-1, to=3-1]
  \end{tikzcd}\]
  ~~~

  that is if $A$ is a quotient of a subfinite set.

While informally we say might say "$A$ is Bishop-finite", it's important
when doing univalent mathematics to note that all the notions above
equip $A$ with extra *structure*. For example, we know that there are
$n!$ equivalences $A \simeq [n]$. This isn't an idle concern: if we
define the type of finite sets to be, e.g.,

$$
\sum_{X : \ty} \sum_{n : \NN}\ [n] \simeq X
$$

then we end up with something with the incorrect homotopy type! We'd
expect the type of finite sets (in a given universe) to be a subtype of
the type of sets (in that universe). In particular, we expect the
identity type $X \is X$ of a finite type $X$ to be a set with
$\operatorname{card}(X)!$ elements. But the type above is, by
univalence, equivalent to the natural numbers:

```agda
naïve-fin-is-nat : (Σ[ X ∈ Type ] Σ[ n ∈ Nat ] Fin n ≃ X) ≃ Nat
naïve-fin-is-nat =
  Σ[ X ∈ Type ] Σ[ n ∈ Nat ] Fin n ≃ X ≃⟨ Σ-swap₂ ⟩
  Σ[ n ∈ Nat ] Σ[ X ∈ Type ] Fin n ≃ X ≃⟨ Σ-contr-snd (λ x → Equiv-is-contr (Fin x)) ⟩
  Nat                                  ≃∎
```

The fix turns out to be simple. Instead of *equipping* a type with an
equivalence, we record that such an equivalence [[merely
exists|propositional truncation]]. Therefore, we could define the type
of finite sets as

$$
\sum_{X : Type} \left\| \sum_{n : \bN} [n] \simeq X \right\|\text{,}
$$

truncating the equivalence. However, this definition turns out to be
*computationally* inefficient, especially when we want to show closure
properties of finite sets, because of the iterated equivalences.
Instead, we'll define what it means for a type to be finite in terms of
[[lists]], which allows us to "flatten" a chain of equivalences.

## Listings

:::{.definition #listing}
A **listing** for a type $A$ consists of a list $u :
\operatorname{List}(A)$ and a proof that, for each $x : A$, the space $x
\in u$ is [[contractible]].
:::

```agda
record Listing {ℓ} (A : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    univ       : List A
    has-member : ∀ a → is-contr (a ∈ₗ univ)
```

Put another way, a listing of $A$ is a list of elements of $A$ which
contains each $x : A$ at most once, together with an operation which,
given an $x$, finds an index for it in the list. Any type with a listing
is a [[set]]: since there are as many proofs of (e.g.) $x \in [x]$ as
there are loops $x = x$, and we know there's exactly one of the former,
we conclude that there's exactly one of the latter. Moreover, since
witnesses $x \in u$ correspond to fibres of the lookup function over
$x$, we conclude that any listing generates an equivalence $A \simeq
[\operatorname{length} u]$.

```agda
  find : ∀ a → a ∈ₗ univ
  find a = has-member a .centre

  listing→is-equiv : is-equiv (univ !_)
  listing→is-equiv .is-eqv x = Equiv→is-hlevel 0
    (Σ-ap-snd (λ x → Equiv.inverse Id≃path) ∙e Equiv.inverse member≃lookup)
    (has-member x)

  index : A → Fin (length univ)
  index = equiv→inverse listing→is-equiv
```

<!--
```agda
  listing→fin-equiv : Fin (length univ) ≃ A
  listing→fin-equiv = record { snd = listing→is-equiv }

  opaque
    !-index : ∀ a → univ ! index a ≡ a
    !-index = Equiv.ε listing→fin-equiv

{-# INLINE Listing.constructor #-}

open Listing using (listing→fin-equiv)

listing→equiv-fin : (l : Listing A) → A ≃ Fin (length (Listing.univ l))
listing→equiv-fin l = Equiv.inverse (listing→fin-equiv l)
```
-->

In particular, any listed type is [[discrete]].

```agda
Listing→Discrete : Listing A → Discrete A
Listing→Discrete {A = A} li .decide x y = go auto where
  module ix = Equiv (listing→equiv-fin li)

  go : Dec (ix.to x ≡ ix.to y) → Dec (x ≡ y)
  go (yes p) = yes (ix.injective p)
  go (no ¬p) = no λ p → ¬p (ap ix.to p)
```

<!--
```agda
Listing→is-set : Listing A → is-set A
Listing→is-set x = Discrete→is-set (Listing→Discrete x)

Equiv→listing : A ≃ B → Listing A → Listing B
Equiv→listing {A = A} {B = B} f li = record
  { univ       = map f.to (li .Listing.univ)
  ; has-member = λ a → retract→is-contr (map-equiv-member f) (member-map-equiv f) (member-map-equiv-invl f) (li .Listing.has-member _)
  }
  where module f = Equiv f
```
-->

### Basic listed sets

The easiest types we can build listings for are the decidable
propositions. If the proposition holds (e.g. with witness $a : A$), then
we can take $[a]$ to be a listing. Otherwise, we have the empty listing.

```agda
Listing-prop : ⦃ _ : Dec A ⦄ ⦃ _ : H-Level A 1 ⦄ → Listing A
Listing-prop ⦃ yes a ⦄ = record
  { univ       = a ∷ []
  ; has-member = λ where
    a' .centre         → here (Id≃path.from prop!)
    a' .paths (here p) → ap here (is-set→is-setᵢ (is-prop→is-set (hlevel 1)) _ _ _ _)
  }
Listing-prop ⦃ no ¬a ⦄ = record
  { univ       = []
  ; has-member = λ a → absurd (¬a a)
  }
```

In particular, this is the case for the unit and empty types. We can
also build an explicit listing of the booleans, in either order.

```agda
instance
  Listing-⊥ : Listing ⊥
  Listing-⊥ = Listing-prop

  Listing-⊤ : Listing ⊤
  Listing-⊤ = Listing-prop

  Listing-Bool : Listing Bool
  Listing-Bool .Listing.univ = true ∷ false ∷ []
  Listing-Bool .Listing.has-member true = unique-member!
  Listing-Bool .Listing.has-member false = unique-member!
```

With a bit more effort, we can also list all the elements of $[n]$, by
recursion on the cardinality $n$. For the base case, the list is empty,
and for a successor, we add the element $0 : [1 + n]$ and shift the
universal list for $[n]$ up by 1.

```agda
  Listing-Fin : ∀ {n} → Listing (Fin n)
  Listing-Fin {n} = record { univ = all n ; has-member = has } where
    all : ∀ n → List (Fin n)
    all zero    = []
    all (suc n) = fzero ∷ map fsuc (all n)

    mem : ∀ {n} (x : Fin n) → x ∈ₗ all n
    mem x with fin-view x
    ... | zero  = here reflᵢ
    ... | suc i = there (map-member fsuc (mem i))
```

<details>
<summary>Proving that the list we've built contains every $x : [n]$
exactly once takes a bit of case analysis, but it's not
complicated.</summary>

```agda
    abstract
      uniq : ∀ {n} (x : Fin n) (p q : x ∈ₗ all n) → p ≡ q
      uniq x p q with fin-view x
      uniq _ (here p) (here q)  | zero = ap here prop!
      uniq _ (here p) (there q) | zero = absurd (fsuc≠fzero (Id≃path.to (member-map fsuc (all _) q .fst .snd)))
      uniq _ (there p) _        | zero = absurd (fsuc≠fzero (Id≃path.to (member-map fsuc (all _) p .fst .snd)))

      uniq _ (here ()) q         | suc i
      uniq _ (there p) (here ()) | suc i
      uniq {suc n} .(fsuc i) (there p) (there q) | suc i =
        let
          p' : i ∈ₗ all n
          p' = member-map-embedding fsuc fsuc-is-embedding {i} p

          q' : i ∈ₗ all n
          q' = member-map-embedding fsuc fsuc-is-embedding {i} q

          r =
            p                  ≡⟨ sym (member-map-embedding-invl fsuc fsuc-is-embedding {i} p) ⟩
            map-member fsuc p' ≡⟨ ap (map-member fsuc) (uniq {n} i p' q') ⟩
            map-member fsuc q' ≡⟨ member-map-embedding-invl fsuc fsuc-is-embedding {i} q ⟩
            q                  ∎
        in ap there r

    has : ∀ {n} (x : Fin n) → is-contr (x ∈ₗ all n)
    has x .centre = mem x
    has x .paths  = uniq x (mem x)
```

</details>

<!--
```agda
  Listing-∥∥ : ⦃ _ : Dec A ⦄ → Listing ∥ A ∥
  Listing-∥∥ = Listing-prop

  Listing-PathP : ∀ {A : I → Type ℓ} ⦃ _ : Listing (A i1) ⦄ {x y} → Listing (PathP A x y)
  Listing-PathP {A = A} ⦃ li ⦄ {x} {y} = Listing-prop ⦃ auto ⦄ ⦃ auto ⦄ where instance
    d : ∀ {x y} → Dec (PathP A x y)
    d {x} {y} with Listing→Discrete li .decide (coe A i0 i1 x) y
    ... | yes a = yes (to-pathp {A = A} a)
    ... | no ¬a = no λ a → ¬a (from-pathp a)

    abstract
      s : ∀ {i n} → H-Level (A i) (2 + n)
      s {i} = basic-instance 2 (Listing→is-set (coe (λ i → Listing (A i)) i1 i li))
```
-->

### Closure properties

To show that listed types are closed under operations like $\Sigma$,
we'll introduce a helper type which allows us to replace the list
membership $x \in xs$ by something specific to the type at hand, and
whose h-level we hopefully have an easier time establishing.

The data we require, in addition to the universal list $u :
\operatorname{List}(A)$, consists of a family of contractible types
$M(x)$ over $A$, and for each $x$, a split surjection $M(x) \epi (x \in
u)$.

```agda
record retract→listing {ℓ'} (A : Type ℓ) : Type (ℓ ⊔ lsuc ℓ') where
  no-eta-equality
  field
    univ   : List A
    member : A → n-Type ℓ' 0

    from  : ∀ {x} → x ∈ member → x ∈ₗ univ
    split : ∀ {x} (e : x ∈ₗ univ) → fibre from e
```

This is enough to imply that each $x \in u$ is contractible, and thus
that $u$ is a listing of $A$.

```agda
  has-member : ∀ a → is-contr (a ∈ₗ univ)
  has-member a = record
    { centre = from (member a .is-tr .centre)
    ; paths  = split-surjection→is-hlevel 0 from split (member a .is-tr) .paths
    }
```

<!--
```agda
{-# INLINE retract→listing.constructor #-}

open Listing using (univ ; has-member)
open retract→listing renaming (univ to members) hiding (has-member)
```
-->

An archetypal use of this helper is showing that listings are closed
under dependent sum. For if we have a listing $u_A$ of $A$ and, for each
$x : A$, a listing $u_{P(x)}$ of $P$, we can concatenate each $u_{P(x)}$
(tagging it with the corresponding $x \in u_A$) to obtain a list $s :
\operatorname{List}(\sum_{x : A} P(x))$, equipped with a split
surjection between witnesses $(x, y) \in s$ and pairs of $x \in u_X$ and
$y \in u_{P(x)}$.

```agda
instance
  Listing-Σ
    : {P : A → Type ℓ} ⦃ _ : Listing A ⦄ ⦃ _ : ∀ {x} → Listing (P x) ⦄
    → Listing (Σ A P)
  Listing-Σ {A = A} {P = P} ⦃ la ⦄ ⦃ lb ⦄ = record { retract→listing mk } where
    mk : retract→listing (Σ A P)
    mk .member (x , y) = record
      { is-tr = ×-is-hlevel 0 (la .has-member x) (lb .has-member y)
      }

    mk .members      = sigma (la .univ) (λ x → lb {x} .univ)
    mk .from (x , y) = sigma-member x y
    mk .split e      = member-sigma-view (la .univ) (λ _ → lb .univ) e
```

<details>
<summary>
```agda
  Listing-⊎     : ⦃ _ : Listing A ⦄ ⦃ _ : Listing B ⦄ → Listing (A ⊎ B)
  Listing-Maybe : ⦃ _ : Listing A ⦄ → Listing (Maybe A)
```

We can apply the same technique to show that listings are closed under
non-dependent sum, and under `Maybe`{.Agda}.
</summary>

```agda
  Listing-⊎ {A = A} {B = B} ⦃ la ⦄ ⦃ lb ⦄ = record { retract→listing mk } where
    mk : retract→listing (A ⊎ B)
    mk .member (inl x) = record
      { ∣_∣   = Lift (level-of B) (x ∈ₗ la .univ)
      ; is-tr = Lift-is-hlevel 0 (la .has-member x)
      }
    mk .member (inr x) = record
      { ∣_∣   = Lift (level-of A) (x ∈ₗ lb .univ)
      ; is-tr = Lift-is-hlevel 0 (lb .has-member x)
      }

    mk .members = map inl (la .univ) ++ map inr (lb .univ)

    mk .from {inl x} m = ++-memberₗ (map-member inl (m .lower))
    mk .from {inr x} m = ++-memberᵣ (map-member inr (m .lower))

    mk .split {x} e with member-++-view (map inl (la .univ)) (map inr (lb .univ)) e
    mk .split {inl x} _ | inl (i , p) = record
      { snd = ap ++-memberₗ (member-map-embedding-invl inl inl-is-embedding i) ∙ p }
    mk .split {inr x} _ | inr (i , p) = record
      { snd = ap ++-memberᵣ (member-map-embedding-invl inr inr-is-embedding i) ∙ p }
    mk .split {inr x} _ | inl (i , p) = absurd (inl≠inr (Id≃path.to (member-map inl (la .univ) i .fst .snd)))
    mk .split {inl x} _ | inr (i , p) = absurd (inr≠inl (Id≃path.to (member-map inr (lb .univ) i .fst .snd)))

  Listing-Maybe {A = A} ⦃ li ⦄ = record { retract→listing mk } where
    instance
      s : ∀ {n} → H-Level A (2 + n)
      s = basic-instance 2 (Discrete→is-set (Listing→Discrete li))

    mk : retract→listing (Maybe A)
    mk .members = nothing ∷ map just (li .univ)
    mk .member nothing = el! (Lift (level-of A) ⊤)
    mk .member (just x) = record { is-tr = li .has-member x }

    mk .from {nothing} _ = here reflᵢ
    mk .from {just x}  e = there (map-member just e)

    mk .split {nothing} (here p)  = lift tt , ap here prop!
    mk .split {just x}  (here p)  = absurd (just≠nothing (Id≃path.to p))

    mk .split {nothing} (there e) = absurd (just≠nothing (Id≃path.to (member-map just (li .univ) e .fst .snd)))
    mk .split {just x}  (there e) = record { snd = ap there (member-map-embedding-invl just just-is-embedding e) }
```

</details>

We can also show that listings are closed under dependent product, by
showing that dependent products over a listed type are equivalent to
*iterated* products over the list.


```agda
instance
  Listing-Π : {P : A → Type ℓ} ⦃ _ : Listing A ⦄ ⦃ _ : ∀ {x} → Listing (P x) ⦄ → Listing ((x : A) → P x)
  Listing-Π {A = A} {P = P} ⦃ la ⦄ ⦃ lb ⦄ = li where
    module la = Listing la

    r : retract→listing (Pi la.univ P)
    r .members  = pi la.univ (λ a → lb {a} .univ)
    r .member p = record
      { ∣_∣   = ∀ h → indexₚ p h ∈ₗ lb .univ
      ; is-tr = Π-is-hlevel 0 λ h → lb .has-member (indexₚ p h)
      }
    r .from  = pi-member' P la.univ (λ a → lb {a} .univ)
    r .split = member-pi' P la.univ (λ a → lb {a} .univ)

    li' : Listing (Pi la.univ P)
    li' = record { retract→listing r }

    eqv =
      Pi la.univ P                       ≃⟨ Iso→Equiv (to-pi' P , iso (from-pi' P) (from-to-pi' P) (to-from-pi' P)) ⟩
      ((x : A) (a : x ∈ₗ la.univ) → P x) ≃⟨ Π-ap-cod (λ x → Π-contr-eqv (la.has-member x)) ⟩
      ((x : A) → P x)                    ≃∎

    li : Listing (∀ x → P x)
    li = Equiv→listing eqv li'
```

<!--
```agda
instance
  Listing-Coeq : ⦃ _ : Listing A ⦄ ⦃ _ : Listing B ⦄ {f g : A → B} → Listing (Coeq f g)
  Listing-Coeq ⦃ la ⦄ ⦃ lb ⦄ {f} {g} = Equiv→listing (fn .snd ∙e eqv) Listing-Fin where
    ae = listing→fin-equiv la
    be = listing→fin-equiv lb

    f' = Equiv.from be ∘ f ∘ Equiv.to ae
    g' = Equiv.from be ∘ g ∘ Equiv.to ae

    fn : Σ[ n ∈ Nat ] Fin n ≃ Coeq f' g'
    fn = Finite-coequaliser f' g'

    eqv : Coeq f' g' ≃ Coeq f g
    eqv = Equiv.inverse (Coeq-ap (Equiv.inverse ae) (Equiv.inverse be) refl refl)

  Listing-Lift : ⦃ _ : Listing A ⦄ → Listing (Lift ℓ A)
  Listing-Lift = Equiv→listing l auto where
    l : A ≃ Lift _ A
    l = record { snd = is-iso→is-equiv (iso Lift.lower (λ x → refl) (λ x → refl)) }
```
-->

## Omniscience, exhaustibility, and choice

We now show that listed types are effectively searchable: if we have a
[[decidable]] predicate $P$ over some listed $A$, we can either find
some $x : A$ which satisfies $P$, or prove that no such $x$ exists.

```agda
Listing→exhaustible
  : {A : Type ℓ} ⦃ _ : Listing A ⦄ (P : A → Type ℓ') ⦃ _ : ∀ {x} → Dec (P x) ⦄
  → (Σ[ a ∈ A ] P a) ⊎ (∀ a → ¬ P a)
Listing→exhaustible {A = A} ⦃ li ⦄ P ⦃ dec ⦄ =
  search (li .univ) (λ a _ → li .has-member a .centre) where
```

We do this by abstracting, then applying induction, over the universal
list for $A$. To do this, we weaken universality to instead requiring
that the $u$ we recur over contains every $a : A$ with $P(a)$. That way,
if we find that an element does *not* satisfy $P$, we can safely remove
it from the list.

```agda
  search
    : (xs : List A) (f : ∀ a → P a → a ∈ₗ xs)
    → (Σ[ a ∈ A ] P a) ⊎ (∀ a → ¬ P a)
  search [] f = inr λ i p → case f i p of λ ()
  search (x ∷ xs) ix with dec {x}
  ... | yes Px = inl (x , Px)
  ... | no ¬Px = search xs λ a Pa → case ix a Pa of λ where
    (here a=x) → absurd (¬Px (substᵢ P a=x Pa))
    (there p)  → p
```

This implies that dependent sums and dependent products of decidable
families over listed types are decidable.

```agda
instance
  Listing→Σ-dec
    : {A : Type ℓ} ⦃ _ : Listing A ⦄ {P : A → Type ℓ'} ⦃ _ : ∀ {x} → Dec (P x) ⦄
    → Dec (Σ[ a ∈ A ] P a)
  Listing→Σ-dec {P = P} with Listing→exhaustible P
  ... | inl x = yes x
  ... | inr y = no λ (i , p) → y i p

  Listing→Π-dec
    : {A : Type ℓ} ⦃ _ : Listing A ⦄ {P : A → Type ℓ'} ⦃ _ : ∀ {x} → Dec (P x) ⦄
    → Dec (∀ a → P a)
  Listing→Π-dec {P = P} with Listing→exhaustible (¬_ ∘ P)
  ... | inl (i , ¬p) = no λ f → ¬p (f i)
  ... | inr f = yes λ x → dec→dne (f x)
```

<!--
```agda
  Listing→Π'-dec
    : {A : Type ℓ} ⦃ _ : Listing A ⦄ {P : A → Type ℓ'} ⦃ _ : ∀ {x} → Dec (P x) ⦄
    → Dec (∀ {a} → P a)
  Listing→Π'-dec {P = P} with holds? (∀ a → P a)
  ... | yes f = yes λ {x} → f x
  ... | no ¬f = no λ f → ¬f (λ x → f {x})

  {-# INCOHERENT Listing→Σ-dec Listing→Π-dec Listing→Π'-dec #-}
```
-->

Finally, recalling the equivalence between dependent products over a
listed type and iterated products over its universal list, we can also
show that any listed type is [[projective|set-projective]], i.e. that it
satisfies choice.

```agda
Listing→choice
  : ⦃ _ : Listing A ⦄ {P : A → Type ℓ'}
  → (∀ x → ∥ P x ∥) → ∥ (∀ x → P x) ∥

Listing→choice {A = A} ⦃ la ⦄ {P = P} has = done where
  choose : (xs : List A) → ∥ Pi xs P ∥
  cons   : ∀ {x} → ∥ P x ∥ → ∀ xs → ∥ Pi (x ∷ xs) P ∥

  choose []       = inc tt
  choose (x ∷ xs) = cons (has x) xs

  cons (inc x)        xs = map (x ,_) (choose xs)
  cons (squash x y i) xs = squash (cons x xs) (cons y xs) i

  done = map (λ f a → to-pi' P f a (la .has-member a .centre))
    (choose (la .univ))
```

## Finiteness {defines="finite-type finite"}

With a strong theory of listed types, we can now define finiteness: A
type is finite if it is merely listed. This is a proposition, and
(because listed types satisfy choice) inherits all the closure
properties above.

```agda
Finite : Type ℓ → Type ℓ
Finite A = ∥ Listing A ∥
```

```agda
instance
  Finite-Fin   : ∀ {n} → Finite (Fin n)
  Finite-⊎     : ⦃ Finite A ⦄ → ⦃ Finite B ⦄ → Finite (A ⊎ B)
  Finite-Maybe : ⦃ fa : Finite A ⦄ → Finite (Maybe A)
  Finite-Σ
    : ∀ {P : A → Type ℓ} ⦃ _ : Finite A ⦄ ⦃ _ : ∀ {x} → Finite (P x) ⦄
    → Finite (Σ A P)
  Finite-Π
    : ∀ {P : A → Type ℓ} ⦃ _ : Finite A ⦄ ⦃ _ : ∀ {x} → Finite (P x) ⦄
    → Finite (∀ a → P a)

  Finite-⊤    : Finite ⊤
  Finite-⊥    : Finite ⊥
  Finite-Bool : Finite Bool

  Finite-Lift : ⦃ Finite A ⦄ → Finite (Lift ℓ A)
  Finite-Coeq
    : ∀ ⦃ _ : Finite A ⦄ ⦃ _ : Finite B ⦄ {f g : A → B}
    → Finite (Coeq f g)
  Finite-PathP
    : ∀ {A : I → Type ℓ} ⦃ s : Finite (A i1) ⦄ {x y}
    → Finite (PathP A x y)

  Finite-∥-∥ : ⦃ _ : Dec A ⦄ → Finite ∥ A ∥
```

<!--
```agda
  Finite-Fin = inc auto
  Finite-∥-∥ = inc auto

  Finite-⊎ ⦃ fa ⦄ ⦃ fb ⦄ = do
    a ← fa
    b ← fb
    pure (Listing-⊎ ⦃ a ⦄ ⦃ b ⦄)

  Finite-Maybe ⦃ fa ⦄ = do
    a ← fa
    pure (Listing-Maybe ⦃ a ⦄)

  Finite-Σ ⦃ fa ⦄ ⦃ fp ⦄ = do
    fa ← fa
    let instance _ = fa
    fp ← Listing→choice λ x → fp {x}
    pure (Listing-Σ ⦃ fa ⦄ ⦃ λ {x} → fp x ⦄)

  Finite-Π ⦃ fa ⦄ ⦃ fp ⦄ = do
    fa ← fa
    let instance _ = fa
    fp ← Listing→choice λ x → fp {x}
    pure (Listing-Π ⦃ fa ⦄ ⦃ λ {x} → fp x ⦄)

  Finite-⊥ = inc auto

  Finite-⊤ = inc auto

  Finite-Bool = inc auto
  Finite-PathP ⦃ fa ⦄ = do
    a ← fa
    pure (Listing-PathP ⦃ a ⦄)

  Finite-Lift ⦃ fa ⦄ = do
    a ← fa
    pure (Listing-Lift ⦃ a ⦄)

  Finite-Coeq ⦃ fa ⦄ ⦃ fb ⦄ = do
    a ← fa
    b ← fb
    pure (Listing-Coeq ⦃ a ⦄ ⦃ b ⦄)

  Listing-So : ∀ {b} → Listing (So b)
  Listing-So = Listing-prop

  Finite-So : ∀ {b} → Finite (So b)
  Finite-So = inc auto

instance
  Discrete-listing-Π : ⦃ _ : Listing A ⦄ ⦃ _ : ∀ {x} → Discrete (P x) ⦄ → Discrete ((x : A) → P x)
  Discrete-listing-Π {A = A} ⦃ xa ⦄ ⦃ dp ⦄ .decide f g with Listing→exhaustible (λ i → ¬ f i ≡ g i)
  ... | inl (x , p) = no λ f=g → p (happly f=g x)
  ... | inr ¬p = yes (ext λ x → dec→dne (¬p x))
```
-->

Finally, we can define the cardinality of a *finite* type, not just a
listed type, since distinct listings of $A$ can differ only in their
order (and not their length).

```agda
cardinality : ⦃ fin : Finite A ⦄ → Nat
cardinality {A = A} ⦃ is ⦄ = ∥-∥-rec-set (hlevel 2) (λ l → length (l .univ)) con is where abstract
  con : (l1 l2 : Listing A) → length (l1 .univ) ≡ length (l2 .univ)
  con l1 l2 = Fin-injective $
    Fin (length (univ l1)) ≃⟨ Listing.listing→fin-equiv l1 ⟩
    A                      ≃˘⟨ Listing.listing→fin-equiv l2 ⟩
    Fin (length (univ l2)) ≃∎
```

<!--
```agda
enumeration : ⦃ f : Finite A ⦄ → ∥ A ≃ Fin (cardinality ⦃ f ⦄) ∥
enumeration ⦃ inc l ⦄ = pure (listing→equiv-fin l)
enumeration {A = A} ⦃ squash x y i ⦄ = is-prop→pathp
  (λ i → ∥_∥.squash {A = A ≃ Fin (cardinality ⦃ squash x y i ⦄)})
  (enumeration ⦃ x ⦄) (enumeration ⦃ y ⦄) i

Finite→H-Level : ∀ {n} ⦃ _ : Finite A ⦄ → H-Level A (2 + n)
Finite→H-Level ⦃ f ⦄ = basic-instance 2 (case f of Listing→is-set)

Finite→Discrete : ⦃ _ : Finite A ⦄ → Discrete A
Finite→Discrete ⦃ f ⦄ =
  let instance _ = Finite→H-Level {n = 0} ⦃ f ⦄
   in case f of λ l → Listing→Discrete l

module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} ⦃ fb : Finite B ⦄ (e : ∥ A ≃ B ∥) (f : A → B) where
  Finite-injection→equiv : injective f → is-equiv f
  Finite-injection→equiv inj = ∥-∥-out! do
    e ← e
    eb ← enumeration ⦃ fb ⦄
    pure
      $ equiv-cancell (eb .snd)
      $ equiv-cancelr ((eb e⁻¹ ∙e e e⁻¹) .snd)
      $ Fin-injection→equiv _
      $ Equiv.injective (eb e⁻¹ ∙e e e⁻¹) ∘ inj ∘ Equiv.injective eb

  Finite-surjection→equiv : is-surjective f → is-equiv f
  Finite-surjection→equiv surj = ∥-∥-out! do
    e ← e
    eb ← enumeration ⦃ fb ⦄
    pure
      $ equiv-cancell (eb .snd)
      $ equiv-cancelr ((eb e⁻¹ ∙e e e⁻¹) .snd)
      $ Fin-surjection→equiv _
      $ ∘-is-surjective (is-equiv→is-surjective (eb .snd))
      $ ∘-is-surjective surj
      $ is-equiv→is-surjective ((eb e⁻¹ ∙e e e⁻¹) .snd)
```
-->
