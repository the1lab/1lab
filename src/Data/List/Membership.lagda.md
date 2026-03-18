<!--
```agda
open import 1Lab.Prelude

open import Data.List.Properties
open import Data.Id.Properties
open import Data.List.NonEmpty
open import Data.List.Base
open import Data.Dec.Base
open import Data.Fin.Base hiding (_≤_)
open import Data.Nat.Base
open import Data.Sum.Base
open import Data.Id.Base
open import Data.Bool

open import Meta.Idiom
```
-->

```agda
module Data.List.Membership where
```

<!--
```agda
private variable
  ℓ ℓ' : Level
  A B : Type ℓ
  P Q : A → Type ℓ'
  x y : A
  xs ys : List A
```
-->

# Membership in lists

We can inductively define a notion of membership between elements $a :
A$ and lists $as : \List{A}$; we write $a \in_l as$. However, note that
this notion of membership is **not** a [[proposition]]! The type $a
\in_l as$ has at least as many inhabitants as there are occurrences of
$a$ in $as$; and if the type $A$ is not a set, then each proof of $a \in
as$ can be acted on by a loop on $a$ to give a new proof.

```agda
data _∈ₗ_ {ℓ} {A : Type ℓ} (x : A) : List A → Type ℓ where
  here  : ∀ {x'} (p : x ≡ᵢ x') → x ∈ₗ (x' ∷ xs)
  there : (p : x ∈ₗ xs)        → x ∈ₗ (y ∷ xs)
```

<!--
```agda
here≠there : ∀ {A : Type ℓ} {xs : List A} {x y : A} {p : x ≡ᵢ y} {q : x ∈ₗ xs} → here p ≠ there q
here≠there p = subst (λ { (here _) → ⊤ ; (there _) → ⊥ }) p tt

there-injective : ∀ {A : Type ℓ} {xs : List A} {x y : A} {p q : x ∈ₗ xs} → Path (x ∈ₗ (y ∷ xs)) (there p) (there q) → p ≡ q
there-injective {xs = xs} {x} {y} {p} = ap unthere where
  unthere : (x ∈ₗ (y ∷ xs)) → x ∈ₗ xs
  unthere (there p) = p
  unthere _ = p
```
-->

<!--
```agda
instance
  Membership-List : ∀ {ℓ} {A : Type ℓ} → Membership A (List A) ℓ
  Membership-List = record { _∈_ = _∈ₗ_ }
```
-->

There is a more (homotopically) straightforward characterisation of
membership in lists: the [[fibres]] of the lookup function `xs !
i`{.Agda ident=!_}. These are given by an index $i :
[\operatorname{length}(xs)]$, living in the [[standard finite set]] with
as many elements as the list has positions, together with a proof that
$xs \mathbin{!} i = x$.

The inverse equivalences between these notions is defined below; the
proof that they are _are_ inverses is a straightforward induction in
both cases, so it's omitted for space.

```agda
member→lookup : ∀ {x : A} {xs} → x ∈ xs → fibreᵢ (xs !_) x
member→lookup (here p) = fzero , symᵢ p
member→lookup (there prf) with member→lookup prf
... | ix , p = fsuc ix , p

lookup→member : ∀ {x : A} {xs} → fibreᵢ (xs !_) x → x ∈ xs
lookup→member {A = A} {x = x} = λ (ix , p) → go ix p module lookup→member where
  go : ∀ {xs} (ix : Fin (length xs)) → (xs ! ix) ≡ᵢ x → x ∈ xs
  go ix _  with fin-view ix
  go {xs = x ∷ xs} _ p | zero     = here  (symᵢ p)
  go {xs = x ∷ xs} _ p | (suc ix) = there (go ix p)
```

The equivalence between these definitions explains why $a \in_l as$ can
be so complicated. First, it's at least a set, since it stores the
index. Second, it stores a path, which can be arbitrarily complicated
depending on the type $A$.

<!--
```agda
lookup→member→lookup : ∀ {x : A} {xs} (f : fibreᵢ (xs !_) x) → member→lookup (lookup→member f) ≡ f
lookup→member→lookup {A = A} {x = x} (ix , p) = go ix p where
  go : ∀ {xs} (ix : Fin (length xs)) (p : xs ! ix ≡ᵢ x) → member→lookup (lookup→member.go {xs = xs} ix p) ≡ (ix , p)
  go ix p with fin-view ix
  go {xs = x ∷ xs} _ reflᵢ | zero   = refl
  go {xs = x ∷ xs} _ p     | suc ix = Σ-pathp (ap fsuc (ap fst p')) (ap snd p')
    where p' = go {xs = xs} ix p

member→lookup→member
  : {x : A} {xs : List A} (p : x ∈ xs) → p ≡ lookup→member (member→lookup p)
member→lookup→member (here reflᵢ) = refl
member→lookup→member (there p)    = ap there (member→lookup→member p)

member≃lookup : ∀ {x : A} {xs} → (x ∈ₗ xs) ≃ fibreᵢ (xs !_) x
member≃lookup .fst = member→lookup
member≃lookup .snd = is-iso→is-equiv λ where
  .is-iso.from p → lookup→member p
  .is-iso.rinv p → lookup→member→lookup p
  .is-iso.linv p → sym (member→lookup→member p)
```
-->

Explicitly, if $A$ is an [[$3+n$-type|n-type]], then the type of membership
proofs for lists of $A$s are an [[$2+n$-type|n-type]].

```agda
∈ₗ-is-hlevel
  : ∀ {A : Type ℓ} {x : A} {xs : List A}
  → (n : Nat)
  → is-hlevel A (3 + n)
  → is-hlevel (x ∈ xs) (2 + n)
∈ₗ-is-hlevel {x = x} {xs = xs} n ahl =
  Equiv→is-hlevel (2 + n) (member≃lookup ∙e Σ-ap-snd (λ i → Id≃path)) $
  Σ-is-hlevel (2 + n) (hlevel (2 + n)) λ i → ahl (xs ! i) x
```

<!--
```agda
instance
  H-Level-∈ₗ
    : ∀ {A : Type ℓ} {x : A} {xs : List A} {n : Nat}
    → ⦃ _ : 2 ≤ n ⦄
    → ⦃ _ : H-Level A (suc n) ⦄
    → H-Level (x ∈ₗ xs) n
  H-Level-∈ₗ {n = suc (suc n)} ⦃ 2≤n ⦄ ⦃ ahl ⦄ = hlevel-instance (∈ₗ-is-hlevel n (ahl .H-Level.has-hlevel))
```
-->

<!--
```agda
index-of : ∀ {x : A} {xs : List A} → x ∈ₗ xs → Nat
index-of x∈xs = lower (member→lookup x∈xs .fst)
{-# NOINLINE index-of #-}
```
-->

Despite the potential complexity of $a \in_l as$, we do note that if $A$
is a [[set]], then all that matters is the index; If $A$ is moreover
[[discrete]], then $a \in_l as$ is [[decidable]].

```agda
elem? : ⦃ _ : Discrete A ⦄ (x : A) (xs : List A) → Dec (x ∈ xs)
elem? x [] = no λ ()
elem? x (y ∷ xs) with x ≡ᵢ? y
... | yes p = yes (here p)
... | no ¬p with elem? x xs
... | yes p = yes (there p)
... | no ¬q = no λ { (here p) → ¬p p ; (there q) → ¬q q }
```

<!--
```agda
instance
  Dec-∈ₗ : ⦃ _ : Discrete A ⦄ {x : A} {xs : List A} → Dec (x ∈ xs)
  Dec-∈ₗ {x = x} {xs} = elem? x xs
```
-->

## Removing duplicates

Still working with a discrete type, we can define a function
`nub`{.Agda} which removes duplicates from a list. It is constructed by
inductively deciding whether or not to keep the head of the list,
discarding those which already appear further down. This has terrible
the terrible time complexity $O(n^2)$, but it works for an arbitrary
discrete type, which is the best possible generality.

```agda
nub-cons : (x : A) (xs : List A) → Dec (x ∈ xs) → List A
nub-cons x xs (yes _) = xs
nub-cons x xs (no _)  = x ∷ xs

nub : ⦃ _ : Discrete A ⦄ → List A → List A
nub []       = []
nub (x ∷ xs) = nub-cons x (nub xs) (elem? x (nub xs))
```

The function `nub`{.Agda} is characterised by the following two facts.
First, membership in `nub`{.Agda} is a proposition --- each element
appears at most once. Second, membership is (logically) preserved when
`nub`{.Agda}bing a list --- note that the function mapping old indices
to new indices is not injective, since all occurrences of an element
will be mapped to the same (first) occurrence in the deduplicated list.

<!--
```agda
is-nubbed : List A → Type _
is-nubbed xs = ∀ e → is-prop (e ∈ₗ xs)
```
-->

```agda
nub-is-nubbed
  : ∀ ⦃ _ : Discrete A ⦄ (xs : List A) → is-nubbed (nub xs)
member→member-nub
  : ∀ ⦃ _ : Discrete A ⦄ {x : A} {xs : List A} → x ∈ xs → x ∈ nub xs
```

<details>
<summary>The proofs here are also straightforward inductive arguments.</summary>

```agda
nub-is-nubbed (x ∷ xs) e p1 p2 with elem? x (nub xs) | p1 | p2
... | yes p | p1 | p2 = nub-is-nubbed xs _ p1 p2
... | no ¬p | here  p1 | here  p2 = ap _∈ₗ_.here (is-set→is-setᵢ (Discrete→is-set auto) _ _ p1 p2)
... | no ¬p | here  p1 | there p2 = absurd (¬p (substᵢ (_∈ nub xs) p1 p2))
... | no ¬p | there p1 | here  p2 = absurd (¬p (substᵢ (_∈ nub xs) p2 p1))
... | no ¬p | there p1 | there p2 = ap there (nub-is-nubbed xs _ p1 p2)

member→member-nub {xs = x ∷ xs} (here p) with elem? x (nub xs)
... | yes x∈nub = substᵢ (_∈ nub xs) (symᵢ p) x∈nub
... | no ¬x∈nub = here p
member→member-nub {xs = x ∷ xs} (there α) with elem? x (nub xs)
... | yes x∈nub = member→member-nub α
... | no ¬x∈nub = there (member→member-nub α)
```

</details>

## Properties

A list $xs$ is nonempty if and only if there [[merely]] exists
some $x \in xs$.

```agda
has-member→nonempty
  : ∀ {x : A} {xs : List A}
  → x ∈ xs
  → is-nonempty xs
has-member→nonempty {xs = x ∷ xs} x∈xs = nonempty

nonempty→has-member
  : ∀ {A : Type ℓ} {xs : List A}
  → is-nonempty xs
  → Σ[ x ∈ A ] (x ∈ xs)
nonempty→has-member {xs = x ∷ xs} ne = x , here reflᵢ

nonempty≃has-member
  : ∀ {A : Type ℓ} (xs : List A)
  → is-nonempty xs ≃ (∃[ x ∈ A ] (x ∈ xs))
nonempty≃has-member xs = prop-ext!
  (λ ne → inc (nonempty→has-member ne))
  (rec! λ x x∈xs → has-member→nonempty x∈xs)
```

<!-- [TODO: Reed M, 26/08/2025] Prose for these. -->

<!--
```agda
lookup-tabulate : ∀ {n} (f : Fin n → A) (i : Fin n) (j : Fin _) → i .lower ≡ j .lower → tabulate f ! j ≡ f i
lookup-tabulate {n = zero}  f i j p = absurd (Fin-absurd i)
lookup-tabulate {n = suc n} f i j p with fin-view j
... | zero  = ap f (fin-ap (sym p))
... | suc j with fin-view i
... | zero  = absurd (zero≠suc p)
... | suc i = lookup-tabulate (f ∘ fsuc) i j (suc-inj p)

lookup-tabulate' : ∀ {n} (f : Fin n → A) i → tabulate f ! i ≡ f (subst Fin (length-tabulate f) i)
lookup-tabulate' f i = lookup-tabulate f (subst Fin (length-tabulate f) i) i refl

lookup-tabulate-fibre : ∀ {n} (f : Fin n → A) x → fibreᵢ (tabulate f !_) x ≃ fibreᵢ f x
lookup-tabulate-fibre f x = Σ-ap (path→equiv (ap Fin (length-tabulate f))) λ i →
  path→equiv (ap (_≡ᵢ x) (lookup-tabulate' f i))

member-tabulate : ∀ {n} (f : Fin n → A) x → (x ∈ tabulate f) ≃ fibreᵢ f x
member-tabulate f x = member≃lookup ∙e lookup-tabulate-fibre f x
```
-->

<!--
```agda
map-member
  : ∀ {A : Type ℓ} {B : Type ℓ'} (f : A → B) {x : A} {xs : List A}
  → x ∈ xs → f x ∈ map f xs
map-member f (here p)  = here (apᵢ f p)
map-member f (there x) = there (map-member f x)

member-map-inj
  : ∀ {A : Type ℓ} {B : Type ℓ'} (f : A → B) (inj : injective f)
  → {x : A} {xs : List A} → f x ∈ map f xs → x ∈ xs
member-map-inj f inj {xs = x' ∷ xs} (here p)  = here (Id≃path.from (inj (Id≃path.to p)))
member-map-inj f inj {xs = x' ∷ xs} (there i) = there (member-map-inj f inj i)

member-map-embedding
  : ∀ {A : Type ℓ} {B : Type ℓ'} (f : A → B) (emb : is-embedding f)
  → {x : A} {xs : List A} → f x ∈ map f xs → x ∈ xs
member-map-embedding f emb = member-map-inj f (has-prop-fibres→injective f emb)

member-map-embedding-invl
  : ∀ {A : Type ℓ} {B : Type ℓ'} (f : A → B) (emb : is-embedding f)
  → {x : A} {xs : List A} → is-left-inverse (map-member f {x} {xs}) (member-map-embedding f emb)
member-map-embedding-invl f emb {xs = x' ∷ xs} (here p) = ap _∈ₗ_.here coh where
  coh : apᵢ f (Id≃path.from (has-prop-fibres→injective f emb (Id≃path.to p))) ≡ p
  coh = apᵢ-from f _ ∙ ap Id≃path.from (equiv→counit (embedding→cancellable emb) _) ∙ Id≃path.η _

member-map-embedding-invl f emb {xs = x' ∷ xs} (there h) = ap there (member-map-embedding-invl f emb h)

module _ {A : Type ℓ} {B : Type ℓ'} (f : A ≃ B) where
  private module f = Equiv f

  map-equiv-member : ∀ {x : B} {xs} → f.from x ∈ₗ xs → x ∈ₗ map f.to xs
  map-equiv-member (here p)  = here (Id≃path.from (sym (f.adjunctr (sym (Id≃path.to p)))))
  map-equiv-member (there p) = there (map-equiv-member p)

  member-map-equiv : ∀ {x : B} {xs} → x ∈ₗ map f.to xs → f.from x ∈ₗ xs
  member-map-equiv {xs = y ∷ xs} (here p)  = here (Id≃path.from (sym (f.adjunctl (sym (Id≃path.to p)))))
  member-map-equiv {xs = y ∷ xs} (there x) = there (member-map-equiv x)

  member-map-equiv-invl : ∀ {x : B} {xs} → is-left-inverse map-equiv-member (member-map-equiv {x} {xs})
  member-map-equiv-invl {xs = x ∷ xs} (here p)  = ap _∈ₗ_.here
    ( ap Id≃path.from (ap sym (ap f.adjunctr (ap sym (Id≃path.ε _)) ∙ Equiv.η f.adjunct _))
    ∙ Id≃path.η p
    )

  member-map-equiv-invl {xs = x ∷ xs} (there p) = ap there (member-map-equiv-invl p)

module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) where
  member-map : ∀ {y} xs → y ∈ₗ map f xs → Σ[ f ∈ fibreᵢ f y ] (f .fst ∈ₗ xs)
  member-map (x ∷ xs) (here p)  = (x , symᵢ p) , here reflᵢ
  member-map (x ∷ xs) (there p) =
    let (f , ix) = member-map xs p
      in f , there ix

  map-member' : ∀ {y} xs (fb : Σ[ f ∈ fibreᵢ f y ] (f .fst ∈ₗ xs)) → y ∈ₗ map f xs
  map-member' (_ ∷ xs) ((x , p) , here q)  = here (symᵢ p ∙ᵢ apᵢ f q)
  map-member' (_ ∷ xs) ((x , p) , there i) = there (map-member' xs ((x , p) , i))

  member-map→fibre→member : ∀ {y} xs (p : y ∈ₗ map f xs) → map-member' xs (member-map xs p) ≡ p
  member-map→fibre→member (x ∷ xs) (here reflᵢ) = ap here refl
  member-map→fibre→member (x ∷ xs) (there p)    = ap there (member-map→fibre→member xs p)

++-memberₗ : x ∈ₗ xs → x ∈ₗ (xs ++ ys)
++-memberₗ (here p)  = here p
++-memberₗ (there p) = there (++-memberₗ p)

++-memberᵣ : x ∈ₗ ys → x ∈ₗ (xs ++ ys)
++-memberᵣ {xs = []}     p = p
++-memberᵣ {xs = x ∷ xs} p = there (++-memberᵣ p)

Member-++-view
  : ∀ {ℓ} {A : Type ℓ} (x : A) (xs : List A) (ys : List A)
  → (p : x ∈ₗ (xs ++ ys)) → Type _
Member-++-view x xs ys p = (Σ[ q ∈ x ∈ₗ xs ] (++-memberₗ q ≡ p)) ⊎ (Σ[ q ∈ x ∈ₗ ys ] (++-memberᵣ q ≡ p))

member-++-view
  : ∀ {ℓ} {A : Type ℓ} {x : A} (xs : List A) (ys : List A)
  → (p : x ∈ₗ (xs ++ ys)) → Member-++-view x xs ys p
member-++-view []       _ p         = inr (p , refl)
member-++-view (x ∷ xs) _ (here p)  = inl (here p , refl)
member-++-view (x ∷ xs) _ (there p) with member-++-view xs _ p
... | inl (p , q) = inl (there p , ap there q)
... | inr (p , q) = inr (p , ap there q)
```
-->

<!--
```agda
uncons-is-nubbed : {x : A} {xs : List A} (hxs : is-nubbed (x ∷ xs)) → (x ∉ xs) × is-nubbed xs
uncons-is-nubbed hxs = record
  { fst = λ x∈xs  → absurd (here≠there (hxs _ (here reflᵢ) (there x∈xs)))
  ; snd = λ e a b → there-injective (hxs e (there a) (there b))
  }

++-is-nubbed
  : {xs ys : List A} (hxs : is-nubbed xs) (hys : is-nubbed ys)
  → ((e : A) → e ∈ xs → e ∉ ys)
  → is-nubbed (xs <> ys)
++-is-nubbed {xs = xs} hxs hys disj e a b with member-++-view xs _ a | member-++-view xs _ b
... | inl (a , α) | inl (b , β) = sym α ∙∙ ap ++-memberₗ (hxs _ a b) ∙∙ β
... | inr (a , α) | inr (b , β) = sym α ∙∙ ap ++-memberᵣ (hys _ a b) ∙∙ β
... | inl (a , α) | inr (b , β) = absurd (disj _ a b)
... | inr (a , α) | inl (b , β) = absurd (disj _ b a)

-- For `map f xs` to be nubbed when `xs` is, it suffices that `f` be an
-- embedding on fibres which belong to `xs`.

map-is-nubbed
  : {A : Type ℓ} {B : Type ℓ'} {xs : List A} (f : A → B)
  → ((b : B) (f f' : fibreᵢ f b) → f .fst ∈ₗ xs → f' .fst ∈ₗ xs → f ≡ f')
  → is-nubbed xs → is-nubbed (map f xs)
map-is-nubbed {xs = xs} f hf hxs e a b =
     sym (member-map→fibre→member f xs a)
  ∙∙ ap (map-member' f xs) (Σ-prop-path (λ _ → hxs _) (hf e (member-map f xs a .fst) (member-map f xs b .fst) (member-map f xs a .snd) (member-map f xs b .snd)))
  ∙∙ member-map→fibre→member f xs b
```
-->

<!--
```agda
any-one-of
  : ∀ {ℓ} {A : Type ℓ}
  → (f : A → Bool) (x : A) (xs : List A)
  → x ∈ xs → f x ≡ true
  → any-of f xs ≡ true
any-one-of f x (y ∷ xs) (here x=y) x-true =
  ap₂ or (substᵢ (λ e → f e ≡ true) x=y x-true) refl
any-one-of f x (y ∷ xs) (there x∈xs) x-true =
  ap₂ or refl (any-one-of f x xs x∈xs x-true) ∙ or-truer _
```
-->
