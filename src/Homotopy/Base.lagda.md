```agda
open import 1Lab.Prelude

open import Algebra.Group.Homotopy

open import Homotopy.Space.Suspension
open import Homotopy.Space.Sphere

open import Data.List using (_∷_ ; [])

module Homotopy.Base where
```

# Synthetic homotopy theory

This module contains the basic definitions for the study of synthetic
homotopy theory. Synthetic homotopy theory is the name given to studying
$\infty$-groupoids in their own terms, i.e., the application of homotopy
theory to computing homotopy invariants of spaces. Central to the theory
is the concept of _pointed type_ and _pointed map_. After all, [homotopy
groups] are no more than the set-truncations of n-fold iterated loop
spaces, and loop spaces are always relative to a basepoint.

[homotopy groups]: Algebra.Group.Homotopy.html

If we have pointed types $(A, a)$ and $(B, b)$, the most natural notion
of function between them is not simply the type of functions $A \to B$,
but rather those functions $A \to B$ which _preserve the basepoint_,
i.e. the functions $f : A \to B$ equipped with paths $f(a) \equiv b$.

```agda
_→∙_ : ∀ {ℓ ℓ′} → Type∙ ℓ → Type∙ ℓ′ → Type _
(A , a) →∙ (B , b) = Σ[ f ∈ (A → B) ] (f a ≡ b)
```

A helper that will come in handy is `Σ∙`{.Agda}, which attaches the
north pole as the basepoint of the suspended space.

```agda
Σ∙ : ∀ {ℓ} → Type∙ ℓ → Type∙ ℓ
Σ∙ A = Susp (A .fst) , N

Ω∙ : ∀ {ℓ} → Type∙ ℓ → Type∙ ℓ
Ω∙ (A , a) = Path A a a , refl
```

## The suspension-loop space adjunction

An important stepping stone in calculating loop spaces of higher types
is the _suspension-loop space_ [adjunction]: basepoint-preserving maps
_from_ a suspension are the same thing as basepoint-preserving maps
_into_ a loop space. We construct the equivalence in two steps, but both halves are constructed in elementary terms.

First, we'll prove that

$$
(\Sigma A \to_* B) \simeq \left(\sum_{b_s : B} A \to b_0 \equiv b_s\right),
$$

which is slightly involved, but not too much. The actual equivalence is
very straightforward to construct, but proving that the two maps
`Σ-map→loops` and `loops→Σ-map` are inverses involves nontrivial path
algebra.

[adjunction]: Cat.Functor.Adjoint.html

```agda
module _ {ℓ ℓ′} {A : Type∙ ℓ} {B : Type∙ ℓ′} where
  Σ-map∙→loops : (Σ∙ A →∙ B) → (Σ _ λ bs → A .fst → B .snd ≡ bs)
  Σ-map∙→loops f .fst = f .fst S
  Σ-map∙→loops f .snd a = sym (f .snd) ∙ ap (f .fst) (merid a)

  loops→Σ-map∙ : (Σ _ λ bs → A .fst → B .snd ≡ bs) → (Σ∙ A →∙ B)
  loops→Σ-map∙ pair .fst N           = B .snd
  loops→Σ-map∙ pair .fst S           = pair .fst
  loops→Σ-map∙ pair .fst (merid x i) = pair .snd x i
  loops→Σ-map∙ pair .snd = refl
```

The construction for turning a family of loops into a
basepoint-preserving map into $\Omega B$ is even simpler, perhaps
because these are almost definitionally the same thing.

```agda
  loops→map∙-Ω : (Σ _ λ bs → A .fst → B .snd ≡ bs) → (A →∙ Ω∙ B)
  loops→map∙-Ω (b , x) .fst a = x a ∙ sym (x (A .snd))
  loops→map∙-Ω (b , x) .snd   = ∙-inv-r (x (A .snd))

  map∙-Ω→loops : (A →∙ Ω∙ B) → (Σ _ λ bs → A .fst → B .snd ≡ bs)
  map∙-Ω→loops pair .fst = B .snd
  map∙-Ω→loops pair .snd = pair .fst
```

<details>
<summary>The path algebra for showing these are both pairs of inverse equivalences is not very interesting, so I've kept it hidden.</summary>

```agda
  Σ-map∙≃loops : (Σ∙ A →∙ B) ≃ (Σ _ λ b → A .fst → B .snd ≡ b)
  Σ-map∙≃loops = Iso→Equiv (Σ-map∙→loops , iso loops→Σ-map∙ invr invl) where
    invr : is-right-inverse loops→Σ-map∙ Σ-map∙→loops
    invr (p , q) = Σ-pathp refl
      (to-pathp (funext (λ a → subst-path-right _ _ ∙ ∙-id-r _ ∙ ∙-id-l _ ∙ ap q (transport-refl _))))

    lemma : ∀ (f : Σ∙ A →∙ B) x → Square
      (sym (f .snd) ∙ ap (f .fst) (merid x))
      (sym (f .snd)) refl (ap (f .fst) (merid x))
    lemma f x = transport (sym Square≡double-composite-path) $
      sym (sym (f .snd) ∙ ap (f .fst) (merid x)) ·· sym (f .snd) ·· ap (f .fst) (merid x)    ≡⟨ double-composite (sym _) _ _ ⟩
      ⌜ sym (sym (f .snd) ∙ ap (f .fst) (merid x)) ⌝ ∙ sym (f .snd) ∙ ap (f .fst) (merid x)  ≡⟨ ap! (sym-∙ (sym _) _) ⟩
      (ap (f .fst) (sym (merid x)) ∙ (f .snd)) ∙ sym (f .snd) ∙ ap (f .fst) (merid x)        ≡˘⟨ ∙-assoc _ _ _ ⟩
      ap (f .fst) (sym (merid x)) ∙ ⌜ (f .snd) ∙ sym (f .snd) ∙ ap (f .fst) (merid x) ⌝      ≡⟨ ap! (∙-cancel-l (sym (f .snd)) _) ⟩
      ap (f .fst) (sym (merid x)) ∙ ap (f .fst) (merid x)                                    ≡⟨ ∙-inv-l _ ⟩
      refl                                                                                   ∎

    invl : is-left-inverse loops→Σ-map∙ Σ-map∙→loops
    invl f = Σ-pathp (funext (λ { N → sym (f .snd)
                                ; S → refl
                                ; (merid x i) → λ j → lemma f x i j }))
                      (to-pathp (subst-path-left _ _ ∙ ∙-id-r _ ∙ refl))

  loops≃map∙-Ω : (Σ _ λ bs → A .fst → B .snd ≡ bs) ≃ (A →∙ Ω∙ B)
  loops≃map∙-Ω = Iso→Equiv (loops→map∙-Ω , iso map∙-Ω→loops invr invl) where
    lemma′ : ∀ {ℓ} {A : Type ℓ} {x : A} (q : x ≡ x) (r : refl ≡ q)
           → ap (λ p → q ∙ sym p) r ∙ ∙-inv-r q ≡ ∙-id-r q ∙ sym r
    lemma′ q r =
      J (λ q′ r → ap (λ p → q′ ∙ sym p) r ∙ ∙-inv-r q′ ≡ ∙-id-r q′ ∙ sym r)
        (∙-id-l _ ∙ sym (∙-id-r _))
        r

    invr : is-right-inverse map∙-Ω→loops loops→map∙-Ω
    invr (b , x) = Σ-pathp (funext (λ a → ap₂ _∙_ refl (ap sym x) ∙ ∙-id-r _))
      (to-pathp (subst-path-left _ _ ∙ lemma))
      where
        lemma =
          ⌜ sym (ap₂ _∙_ refl (ap sym x) ∙ ∙-id-r (b (A .snd))) ⌝ ∙ ∙-inv-r (b (A .snd))               ≡⟨ ap! (sym-∙ (sym _) _) ⟩
          (sym (∙-id-r (b (A .snd))) ∙ ap (b (A .snd) ∙_) (ap sym (sym x))) ∙ ∙-inv-r (b (A .snd))     ≡⟨ sym (∙-assoc _ _ _) ⟩
          sym (∙-id-r (b (A .snd))) ∙ ⌜ ap (λ p → b (A .snd) ∙ sym p) (sym x) ∙ ∙-inv-r (b (A .snd)) ⌝ ≡⟨ ap! (lemma′ (b (A .snd)) (sym x)) ⟩
          sym (∙-id-r (b (A .snd))) ∙ ∙-id-r (b (A .snd)) ∙ x                                          ≡⟨ ∙-cancel-l _ _ ⟩
          x                                                                                            ∎

    invl : is-left-inverse map∙-Ω→loops loops→map∙-Ω
    invl (f , p) = Σ-pathp (p (A .snd)) $ to-pathp $ funext $ λ x →
        subst-path-right _ _ ∙ sym (∙-assoc _ _ _)
      ∙ ap₂ _∙_ refl (∙-inv-l (p (A .snd))) ∙ ∙-id-r _
      ∙ ap p (transport-refl x)
```
</details>

Composing these equivalences, we get the adjunction:

$$
(\Sigma A \to_* B) \simeq (A \to* \Omega B).
$$

```agda
  Σ-map∙≃map∙-Ω : (Σ∙ A →∙ B) ≃ (A →∙ Ωⁿ 1 B)
  Σ-map∙≃map∙-Ω = Σ-map∙≃loops ∙e loops≃map∙-Ω
```

### Loop spaces are equivalently based maps out of spheres

Repeatedly applying the equivalence we just built, we can build an
equivalence

$$
(S^n \to_* A) \simeq (\Sigma S^{n - 1} \to_* \Omega A) \simeq ... \simeq \Omega^n A,
$$

thus characterising $n$-fold loop spaces as basepoint-preserving maps
out of $S^n$, the $n$-dimensional sphere.

<!--
```agda
reassoc-Ω : ∀ {ℓ} {A : Type∙ ℓ} n → Ωⁿ n (Ω∙ A) ≡ Ωⁿ (suc n) A
reassoc-Ω zero = refl
reassoc-Ω {A = A} (suc n) =
  Ωⁿ 1 (Ωⁿ n (Ωⁿ 1 A)) ≡⟨ ap (Ωⁿ 1) (reassoc-Ω n) ⟩
  Ωⁿ 1 (Ωⁿ (suc n) A)  ∎

Sⁿ : Nat → Type∙ lzero
Sⁿ n = Sⁿ⁻¹ (suc n) , N
```
-->

As a special case, in the zeroth dimension, we conclude that $(2 \to_*
A) \equiv A$, i.e., basepoint-preserving maps from the booleans (based
at either point) are the same thing as points of $A$.

```agda
Ωⁿ≃Sⁿ-map : ∀ {ℓ} {A : Type∙ ℓ} n → (Sⁿ n →∙ A) ≃ Ωⁿ n A .fst
Ωⁿ≃Sⁿ-map {A = A} zero    = Iso→Equiv (from , iso to (λ _ → refl) invr) where
  to : A .fst → ((Susp ⊥ , N) →∙ A)
  to x .fst N = A .snd
  to x .fst S = x
  to x .snd = refl

  from : ((Susp ⊥ , N) →∙ A) → A .fst
  from f = f .fst S

  invr : is-right-inverse from to
  invr (x , p) =
    Σ-pathp (funext (λ { N → sym p
                       ; S → refl }))
            λ i j → p (~ i ∨ j)
Ωⁿ≃Sⁿ-map {A = A} (suc n) =
  (Σ∙ (Susp _ , N) →∙ A)          ≃⟨ Σ-map∙≃map∙-Ω ⟩
  ((Susp (Sⁿ⁻¹ n) , N) →∙ Ωⁿ 1 A) ≃⟨ Ωⁿ≃Sⁿ-map n ⟩
  Ωⁿ n (Ωⁿ 1 A) .fst              ≃⟨ path→equiv (ap fst (reassoc-Ω n)) ⟩
  Ωⁿ (suc n) A .fst               ≃∎
```

## Hubs and spokes

Inspired by the equivalence built above, although _not_ using it
directly, we can characterise [h-levels] in terms of maps of spheres,
too. The idea is that, since a map $f : S^n \to A$ is equivalently
_some_ loop in $A$[^someloop], we can characterise the _trivial_ loops as
the constant functions $S^n \to A$. Correspondingly, if every function
$S^n \to A$ is trivial, this means that all $n$-loops in $A$ are
trivial, so that $A$ is $(n+1)$-truncated!

[h-levels]: 1Lab.HLevel.html
[^someloop]: Any map $f : S^n \to A$ can be made basepoint-preserving by
letting $A$ be based at $f(N)$.

We refer to a trivialisation of a map $f : S^n \to A$ as being a
"hubs-and-spokes" construction. Geometrically, a trivial loop $f : S^n
\to A$ can be understood as a map from the $n$-_disc_ rather than the
$n$-sphere, where the $n$-disc is the type generated by attaching a new
point to the sphere (the "hub"), and paths connecting the hub to each
point along the sphere (the "spokes"). The resulting type is
contractible, whence every function out of it is constant.

```agda
hlevel→hubs-and-spokes
  : ∀ {ℓ} {A : Type ℓ} (n : Nat) → is-hlevel A (suc n)
  → (sph : Sⁿ n .fst → A)
  → Σ[ hub ∈ A ] (∀ x → sph x ≡ hub)

hubs-and-spokes→hlevel
  : ∀ {ℓ} {A : Type ℓ} (n : Nat)
  → ((sph : Sⁿ n .fst → A) → Σ[ hub ∈ A ] (∀ x → sph x ≡ hub))
  → is-hlevel A (suc n)
```

<!--
```agda
hlevel→hubs-and-spokes 0 prop sph = sph N , λ x → prop (sph x) (sph N)
hlevel→hubs-and-spokes {A = A} (suc n) h =
  helper λ x y → hlevel→hubs-and-spokes n (h x y)
  where
  helper
    : ((a b : A) → (sph : Sⁿ⁻¹ (1 + n) → a ≡ b) → Σ _ λ hub → ∀ x → sph x ≡ hub)
    → (sph : Sⁿ⁻¹ (2 + n) → A)
    → Σ _ λ hub → ∀ x → sph x ≡ hub
  helper h f = f N , sym ∘ r where
    r : (x : Sⁿ⁻¹ (2 + n)) → f N ≡ f x
    r N = refl
    r S = h (f N) (f S) (λ x i → f (merid x i)) .fst
    r (merid x i) j = hcomp (∂ i ∨ ∂ j) λ where
       k (i = i0) → f N
       k (i = i1) → h (f N) (f S) (λ x i → f (merid x i)) .snd x k j
       k (j = i0) → f N
       k (j = i1) → f (merid x i)
       k (k = i0) → f (merid x (i ∧ j))

hubs-and-spokes→hlevel {A = A} zero spheres x y
  = spheres map .snd N ∙ sym (spheres map .snd S) where
    map : Sⁿ⁻¹ 1 → A
    map N = x
    map S = y
hubs-and-spokes→hlevel {A = A} (suc n) spheres x y =
  hubs-and-spokes→hlevel n $ helper spheres x y where
  helper
    : ((sph : Sⁿ⁻¹ (2 + n) → A) → Σ _ λ hub → ∀ x → sph x ≡ hub)
    → ∀ a b
    → (sph : Sⁿ⁻¹ (1 + n) → a ≡ b)
    → Σ _ λ hub → ∀ x → sph x ≡ hub
  helper h x y f = _ , r  where
    f' : Sⁿ⁻¹ (2 + n) → A
    f' N = x
    f' S = y
    f' (merid u i) = f u i

    r : (s : Sⁿ⁻¹ (1 + n)) → f s ≡ h f' .snd N ∙ sym (h f' .snd S)
    r s i j = hcomp (∂ i ∨ ∂ j) λ where
      k (k = i0) → h f' .snd N (~ i ∨ j)
      k (i = i0) → h f' .snd (merid s j) (~ k)
      k (i = i1) → hfill (∂ j) k λ where
        l (j = i0) → x
        l (j = i1) → h f' .snd S (~ l)
        l (l = i0) → h f' .snd N j
      k (j = i0) → h f' .snd N (~ i ∧ ~ k)
      k (j = i1) → h f' .snd S (~ k)
```
-->

Using this idea, we can define a general _$n$-truncation_ type, as a
joint generalisation of the [propositional] and [set] truncations. While
can not _directly_ build a type with a constructor saying the type is
$n$-truncated, what we _can_ do is freely generate `hub`{.Agda}s and
`spokes`{.Agda} for any $n$-sphere drawn on the $n$-truncation of $A$.
The result is the universal $n$-type admitting a map from $A$.

[propositional]: 1Lab.HIT.Truncation.html
[set]: Data.Set.Truncation.html

```agda
data n-Tr {ℓ} (A : Type ℓ) n : Type ℓ where
  inc    : A → n-Tr A n
  hub    : (r : Sⁿ⁻¹ n → n-Tr A n) → n-Tr A n
  spokes : (r : Sⁿ⁻¹ n → n-Tr A n) → ∀ x → r x ≡ hub r
```

For both proving that the $n$-truncation has the right h-level, and
proving that one can eliminate from it to $n$-types, we use the
characterisations of truncation in terms of hubs-and-spokes.

```agda
n-Tr-is-hlevel
  : ∀ {ℓ} {A : Type ℓ} n → is-hlevel (n-Tr A (suc n)) (suc n)
n-Tr-is-hlevel n = hubs-and-spokes→hlevel n λ sph → hub sph , spokes sph

instance
  n-tr-decomp : ∀ {ℓ} {A : Type ℓ} {n} → Decomposition (n-Tr A (suc n))
  n-tr-decomp = decomp (quote n-Tr-is-hlevel) (`level-minus 1 ∷ [])

n-Tr-elim
  : ∀ {ℓ ℓ′} {A : Type ℓ} {n}
  → (P : n-Tr A (suc n) → Type ℓ′)
  → (∀ x → is-hlevel (P x) (suc n))
  → (∀ x → P (inc x))
  → ∀ x → P x
n-Tr-elim {A = A} {n} P ptrunc pbase = go where
  module _ (r : Sⁿ n .fst → n-Tr A (1 + n))
           (w : (x : Sⁿ n .fst) → P (r x))
    where
      circle : Sⁿ⁻¹ (1 + n) → P (hub r)
      circle x = subst P (spokes r x) (w x)

      hub′ = hlevel→hubs-and-spokes n (ptrunc (hub r)) circle .fst

      spokes′ : ∀ x → PathP (λ i → P (spokes r x i)) (w x) hub′
      spokes′ x = to-pathp $
        hlevel→hubs-and-spokes n (ptrunc (hub r)) circle .snd x

  go : ∀ x → P x
  go (inc x)        = pbase x
  go (hub r)        = hub′ r (λ x → go (r x))
  go (spokes r x i) = spokes′ r (λ x → go (r x)) x i
```

As a simpler case of `n-Tr-elim`{.Agda}, we have the recursion
principle, where the type we are eliminating into is constant.

```agda
n-Tr-rec
  : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′} {n}
  → is-hlevel B (suc n) → (A → B) → n-Tr A (suc n) → B
n-Tr-rec hl = n-Tr-elim (λ _ → _) (λ _ → hl)
```

An initial application of the induction principle for $n$-truncation of
$A$ is characterising its path spaces, at least for the inclusions of
points from $A$. Identifications between (the images of) points in $A$
in the $(n+1)$-truncation are equivalently $n$-truncated identifications
in $A$:

```agda
n-Tr-path-equiv
  : ∀ {ℓ} {A : Type ℓ} {n} {x y : A}
  → Path (n-Tr A (2 + n)) (inc x) (inc y) ≃ n-Tr (x ≡ y) (suc n)
n-Tr-path-equiv {A = A} {n} {x = x} {y} = Iso→Equiv isom where
```

The proof is an application of the encode-decode method. We would like
to characterise the space

$$
\id{inc}(x) \equiv_{\|A\|_{2+n}} y,
$$

so we will, for every $x : A$, define a type family $\mathrm{code}(x) :
\|A\|_{2+n} \to \ty$, where the fibre of $\mathrm{code}(x)$ over
$\id{inc}(y)$ should be $\|x \equiv y\|_{1+n}$. However, induction
principle for $\|A\|_{2+n}$ only allows us to map into $(2+n)$-types,
while $\ty$ itself is not an $n$-type for any $n$. We salvage our
definition by instead mapping into $(1+n)\text{-}\ty$, which _is_ a
$(2+n)$-type.

```agda
  code : (x : A) (y′ : n-Tr A (2 + n)) → n-Type _ (suc n)
  code x =
    n-Tr-elim
      (λ y′ → n-Type _ (suc n))
      (λ y′ → n-Type-is-hlevel (suc n))
      (λ y′ → el! (n-Tr (Path A x y′) (suc n)))
```

The rest of the proof boils down to applications of `path
induction`{.Agda id=J} and the induction principle for $\|A\|_{n+2}$.

```agda
  encode′ : ∀ x y → inc x ≡ y → ∣ code x y ∣
  encode′ x _ = J (λ y _ → ∣ code x y ∣) (inc refl)

  decode′ : ∀ x y → ∣ code x y ∣ → inc x ≡ y
  decode′ x =
    n-Tr-elim _ (λ _ → hlevel!)
      λ x → n-Tr-rec (Path-is-hlevel' (1 + n) hlevel! _ _) (ap inc)

  rinv : ∀ x y → is-right-inverse (decode′ x y) (encode′ x y)
  rinv x = n-Tr-elim _
    (λ y → Π-is-hlevel (2 + n)
      (λ c → Path-is-hlevel (2 + n) (is-hlevel-suc (suc n) (code x y .is-tr))))
    λ x → n-Tr-elim _ (λ x → hlevel!)
      λ p → ap n-Tr.inc (subst-path-right _ _ ∙ ∙-id-l _)

  linv : ∀ x y → is-left-inverse (decode′ x y) (encode′ x y)
  linv x _ = J (λ y p → decode′ x y (encode′ x y p) ≡ p)
    (ap (decode′ x (inc x)) (transport-refl (inc refl)) ∙ refl)

  isom : Iso (inc x ≡ inc y) (n-Tr (x ≡ y) (suc n))
  isom = encode′ _ (inc _)
       , iso (decode′ _ (inc _)) (rinv _ (inc _)) (linv _ (inc _))
```
