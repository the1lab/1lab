<!--
```agda
{-# OPTIONS -vtactic.hlevel:10 #-}
open import 1Lab.Prelude

open import Algebra.Group.Homotopy

open import Data.List using (_∷_ ; [])

open import Homotopy.Space.Suspension
open import Homotopy.Space.Sphere
open import Homotopy.Conjugation
open import Homotopy.Loopspace
```
-->

```agda
module Homotopy.Base where
```

# Synthetic homotopy theory

This module contains the basic definitions for the study of synthetic
homotopy theory. Synthetic homotopy theory is the name given to studying
$\infty$-groupoids in their own terms, i.e., the application of homotopy
type theory to computing homotopy invariants of spaces. Central to the
theory is the concept of [[pointed type]] and [[pointed map]]. After
all, [[homotopy groups]] are no more than the set-truncations of n-fold
iterated loop spaces, and loop spaces are always relative to a
basepoint.

## The suspension–loop space adjunction {defines="suspension-loop-space-adjunction suspensionloop-space-adjunction"}

An important stepping stone in calculating loop spaces of higher types
is the _suspension–loop space_ [[adjunction]]: basepoint-preserving maps
_from_ a suspension are the same thing as basepoint-preserving maps
_into_ a loop space. We construct the equivalence in two steps, but both
halves are constructed in elementary terms.

First, we'll prove that
$$
(\Susp A \to_* B) \simeq \left(\sum_{b_s : B} A \to b_0 \equiv b_s\right),
$$
which is slightly involved, but not too much. The actual equivalence is
very straightforward to construct, but proving that the two maps
`Σ-map→loops` and `loops→Σ-map` are inverses involves nontrivial path
algebra.

```agda
module _ {ℓ ℓ'} {A∙@(A , a₀) : Type∙ ℓ} {B∙@(B , b₀) : Type∙ ℓ'} where
  Σ-map∙→loops : (Σ¹ A∙ →∙ B∙) → (Σ _ λ bs → A → b₀ ≡ bs)
  Σ-map∙→loops f .fst   = f .fst south
  Σ-map∙→loops f .snd a = sym (f .snd) ∙ ap (f .fst) (merid a)

  loops→Σ-map∙ : (Σ _ λ bs → A → b₀ ≡ bs) → (Σ¹ A∙ →∙ B∙)
  loops→Σ-map∙ pair .fst north       = b₀
  loops→Σ-map∙ pair .fst south       = pair .fst
  loops→Σ-map∙ pair .fst (merid x i) = pair .snd x i
  loops→Σ-map∙ pair .snd = refl
```

The construction for turning a family of loops into a
basepoint-preserving map into $\Omega B$ is even simpler, perhaps
because these are almost definitionally the same thing.

```agda
  loops→map∙-Ω : (Σ _ λ bs → A → b₀ ≡ bs) → (A∙ →∙ Ω¹ B∙)
  loops→map∙-Ω (b , l) .fst a = l a ∙ sym (l a₀)
  loops→map∙-Ω (b , l) .snd   = ∙-invr (l a₀)

  map∙-Ω→loops : (A∙ →∙ Ω¹ B∙) → (Σ _ λ bs → A → b₀ ≡ bs)
  map∙-Ω→loops (f , _) .fst = b₀
  map∙-Ω→loops (f , _) .snd = f
```

<details>
<summary>The path algebra for showing these are both pairs of inverse
equivalences is not very interesting, so I've kept it hidden.</summary>

```agda
  Σ-map∙≃loops : (Σ¹ A∙ →∙ B∙) ≃ (Σ _ λ b → A → b₀ ≡ b)
  Σ-map∙≃loops = Iso→Equiv (Σ-map∙→loops , iso loops→Σ-map∙ invr invl) where
    invr : is-right-inverse loops→Σ-map∙ Σ-map∙→loops
    invr (p , q) = Σ-pathp refl $ funext λ a → ∙-idl (q a)

    invl : is-left-inverse loops→Σ-map∙ Σ-map∙→loops
    invl (f , pres) i = funext f' i , λ j → pres (~ i ∨ j) where
      f' : (a : Susp A) → loops→Σ-map∙ (Σ-map∙→loops (f , pres)) .fst a ≡ f a
      f' north = sym pres
      f' south = refl
      f' (merid x i) j = ∙-filler₂ (sym pres) (ap f (merid x)) j i

  loops≃map∙-Ω : (Σ _ λ bs → A → b₀ ≡ bs) ≃ (A∙ →∙ Ω¹ B∙)
  loops≃map∙-Ω = Iso→Equiv (loops→map∙-Ω , iso map∙-Ω→loops invr invl) where
    lemma' : ∀ {ℓ} {A : Type ℓ} {x : A} (q : x ≡ x) (r : refl ≡ q)
           → ap (λ p → q ∙ sym p) r ∙ ∙-invr q ≡ ∙-idr q ∙ sym r
    lemma' q r =
      J (λ q' r → ap (λ p → q' ∙ sym p) r ∙ ∙-invr q' ≡ ∙-idr q' ∙ sym r)
        (∙-idl _ ∙ sym (∙-idr _))
        r

    invr : is-right-inverse map∙-Ω→loops loops→map∙-Ω
    invr (b , x) = Σ-pathp (funext (λ a → ap₂ _∙_ refl (ap sym x) ∙ ∙-idr _)) (to-pathp (subst-path-left _ _ ∙ lemma)) where
      lemma =
        ⌜ sym (ap₂ _∙_ refl (ap sym x) ∙ ∙-idr (b a₀)) ⌝ ∙ ∙-invr (b a₀)          ≡⟨ ap! (sym-∙ (sym _) _) ⟩
        (sym (∙-idr (b a₀)) ∙ ap (b a₀ ∙_) (ap sym (sym x))) ∙ ∙-invr (b a₀)      ≡⟨ sym (∙-assoc _ _ _) ⟩
        sym (∙-idr (b a₀)) ∙ ⌜ ap (λ p → b a₀ ∙ sym p) (sym x) ∙ ∙-invr (b a₀) ⌝  ≡⟨ ap! (lemma' (b a₀) (sym x)) ⟩
        sym (∙-idr (b a₀)) ∙ ∙-idr (b a₀) ∙ x                                     ≡⟨ ∙-cancell _ _ ⟩
        x                                                                         ∎

    invl : is-left-inverse map∙-Ω→loops loops→map∙-Ω
    invl (f , p) = Σ-pathp (p a₀) $ to-pathp $ funext $ λ x →
        subst-path-right _ _ ∙ sym (∙-assoc _ _ _)
      ∙ ap₂ _∙_ refl (∙-invl (p a₀)) ∙ ∙-idr _
      ∙ ap p (transport-refl x)
```
</details>

Composing these equivalences, we get the adjunction $\Susp \dashv \Omega$:

$$
(\Susp A \to_* B) \simeq (A \to_* \Omega B).
$$

```agda
  Σ-map∙≃map∙-Ω : (Σ¹ A∙ →∙ B∙) ≃ (A∙ →∙ Ω¹ B∙)
  Σ-map∙≃map∙-Ω = Σ-map∙≃loops ∙e loops≃map∙-Ω

  Σ-map∙≃∙map∙-Ω : Maps∙ (Σ¹ A∙) B∙ ≃∙ Maps∙ A∙ (Ω¹ B∙)
  Σ-map∙≃∙map∙-Ω .fst = Σ-map∙≃map∙-Ω
  Σ-map∙≃∙map∙-Ω .snd = homogeneous-funext∙ λ a →
    loops→map∙-Ω (Σ-map∙→loops zero∙) · a ≡⟨⟩
    (refl ∙ refl) ∙ sym (refl ∙ refl)     ≡⟨ ap (λ x → x ∙ sym x) (∙-idl _) ⟩
    refl ∙ refl                           ≡⟨ ∙-idl _ ⟩
    refl                                  ∎
```

<!--
```agda
private
  loops-map
    : ∀ {ℓa ℓb ℓc} {A∙@(A , a₀) : Type∙ ℓa} {B∙@(B , b₀) : Type∙ ℓb} {C∙@(C , c₀) : Type∙ ℓc}
    → (B∙ →∙ C∙)
    → (Σ _ λ b → A → b₀ ≡ b) → (Σ _ λ c → A → c₀ ≡ c)
  loops-map (f , pt) (b , l) = f b , λ a → sym pt ∙ ap f (l a)

Σ-map∙≃loops-naturalr
  : ∀ {ℓa ℓb ℓc} {A∙@(A , a₀) : Type∙ ℓa} {B∙@(B , b₀) : Type∙ ℓb} {C∙@(C , c₀) : Type∙ ℓc}
  → (f∙ : B∙ →∙ C∙) (l∙ : Σ¹ A∙ →∙ B∙)
  → loops-map {A∙ = A∙} f∙ (Σ-map∙→loops {A∙ = A∙} l∙)
  ≡ Σ-map∙→loops {A∙ = A∙} (f∙ ∘∙ l∙)
Σ-map∙≃loops-naturalr {A∙ = A , a₀} (f , pt) (l , pt') = refl ,ₚ ext λ a →
  sym pt ∙ ap f (sym pt' ∙ ap l (merid a))           ≡⟨ ap (sym pt ∙_) (ap-∙ f _ _) ⟩
  sym pt ∙ ap f (sym pt') ∙ ap (f ∘ l) (merid a)     ≡⟨ ∙-assoc _ _ _ ⟩
  ⌜ sym pt ∙ ap f (sym pt') ⌝ ∙ ap (f ∘ l) (merid a) ≡˘⟨ ap¡ (sym-∙ _ _) ⟩
  sym (ap f pt' ∙ pt) ∙ ap (f ∘ l) (merid a)         ∎

opaque
  unfolding Ω¹-map

  loops≃map∙-Ω-naturalr
    : ∀ {ℓa ℓb ℓc} {A∙@(A , a₀) : Type∙ ℓa} {B∙@(B , b₀) : Type∙ ℓb} {C∙@(C , c₀) : Type∙ ℓc}
    → (f∙ : B∙ →∙ C∙) (l∙ : Σ _ λ b → A → b₀ ≡ b)
    → Ω¹-map f∙ ∘∙ loops→map∙-Ω {A∙ = A∙} l∙
    ≡ loops→map∙-Ω (loops-map {A∙ = A∙} f∙ l∙)
  loops≃map∙-Ω-naturalr {A∙ = A , a₀} f∙@(f , pt) (b , l) = homogeneous-funext∙ λ a →
    Ω¹-map f∙ .fst (loops→map∙-Ω (b , l) .fst a)       ≡⟨⟩
    conj pt (ap f (l a ∙ sym (l a₀)))                  ≡⟨ conj-defn _ _ ⟩
    sym pt ∙ ⌜ ap f (l a ∙ sym (l a₀)) ⌝ ∙ pt          ≡⟨ ap! (ap-∙ f _ _) ⟩
    sym pt ∙ ((ap f (l a) ∙ ap f (sym (l a₀))) ∙ pt)   ≡⟨ ap (sym pt ∙_) (sym (∙-assoc _ _ _)) ⟩
    sym pt ∙ (ap f (l a) ∙ (ap f (sym (l a₀)) ∙ pt))   ≡⟨ ∙-assoc _ _ _ ⟩
    (sym pt ∙ ap f (l a)) ∙ ⌜ ap f (sym (l a₀)) ∙ pt ⌝ ≡˘⟨ ap¡ (sym-∙ _ _) ⟩
    (sym pt ∙ ap f (l a)) ∙ sym (sym pt ∙ ap f (l a₀)) ∎

Σ-map∙≃map∙-Ω-naturalr
  : ∀ {ℓa ℓb ℓc} {A∙ : Type∙ ℓa} {B∙ : Type∙ ℓb} {C∙ : Type∙ ℓc}
  → (f : B∙ →∙ C∙) (l : Σ¹ A∙ →∙ B∙)
  → Ω¹-map f ∘∙ Σ-map∙≃map∙-Ω {A∙ = A∙} .fst l ≡ Σ-map∙≃map∙-Ω .fst (f ∘∙ l)
Σ-map∙≃map∙-Ω-naturalr {A∙ = A∙} f∙ l∙ =
  Ω¹-map f∙ ∘∙ Σ-map∙≃map∙-Ω .fst l∙                                ≡⟨ loops≃map∙-Ω-naturalr f∙ _ ⟩
  loops→map∙-Ω (loops-map {A∙ = A∙} f∙ (Σ-map∙→loops {A∙ = A∙} l∙)) ≡⟨ ap loops→map∙-Ω (Σ-map∙≃loops-naturalr {A∙ = A∙} f∙ l∙) ⟩
  Σ-map∙≃map∙-Ω .fst (f∙ ∘∙ l∙)                                     ∎
```
-->

We give an explicit description of the [[unit]] of this adjunction,
a map $\sigma : A \to_* \Omega \Susp A$, which will be useful in the
proof of the [[Freudenthal suspension theorem]].
The `merid`{.Agda} constructor of the suspension $\Susp A$
generates a path between the `north`{.Agda} and `south`{.Agda} poles,
rather than a loop on either pole; but, since $A$ is pointed, we
can "correct" the meridian generated by an element $x : A$ by composing
with the inverse of the meridian at the basepoint, to properly get an
element in the [[loop space]] $\Omega \Susp A$. Moreover, since
$\merid{a_0}\cdot\merid{a_0}\inv$ is $\refl$, this is a [[pointed map]].

```agda
suspend∙ : ∀ {ℓ} (A : Type∙ ℓ) → A →∙ Ω¹ (Σ¹ A)
suspend∙ (A , a₀) .fst x = merid x ∙ sym (merid a₀)
suspend∙ (A , a₀) .snd = ∙-invr (merid a₀)
```

<!--
```agda
suspend : ∀ {ℓ} (A : Type∙ ℓ) → ⌞ A ⌟ → Path ⌞ Σ¹ A ⌟ north north
suspend A∙ x = suspend∙ A∙ .fst x
```
-->

In order to connect this map with the adjunction we built above,
we prove that, for any pointed map $f : A \to_* B$, the adjunct of the
composite $A \to_* B \to_* \Omega \Susp B$ is the map $\Susp f :
\Susp A \to_* \Susp B$. In particular, when $f$ is the identity, this
uniquely characterises `suspend∙`{.Agda} as the unit of the adjunction.

```agda
suspend∙-is-unit
  : ∀ {ℓa ℓb} {A : Type∙ ℓa} {B : Type∙ ℓb} (f : A →∙ B)
  → Equiv.from Σ-map∙≃map∙-Ω (suspend∙ B ∘∙ f) ≡ Susp-map∙ f
suspend∙-is-unit {B = B , b₀} f = funext∙
  (Susp-elim _ refl (merid b₀) λ a →
    transpose (flip₁ (∙-filler (merid (f .fst a)) (sym (merid b₀)))))
  refl
```

<!--
```agda
opaque
  unfolding Ω¹-map

  suspend∙-natural
    : ∀ {ℓa ℓb} {A : Type∙ ℓa} {B : Type∙ ℓb} (f : A →∙ B)
    → Ω¹-map (Susp-map∙ f) ∘∙ suspend∙ A ≡ suspend∙ B ∘∙ f
  suspend∙-natural {A = A∙@(A , a₀)} {B = B∙@(B , b₀)} f∙@(f , pt) =
    homogeneous-funext∙ λ a →
      conj refl (ap (Susp-map f) (merid a ∙ sym (merid a₀))) ≡⟨ conj-refl _ ⟩
      ap (Susp-map f) (merid a ∙ sym (merid a₀))             ≡⟨ ap-∙ (Susp-map f) (merid a) (sym (merid a₀)) ⟩
      merid (f a) ∙ sym (merid ⌜ f a₀ ⌝)                     ≡⟨ ap! pt ⟩
      merid (f a) ∙ sym (merid b₀)                           ∎
```
-->

### Loop spaces are equivalently based maps out of spheres {defines="loop-spaces-are-maps-out-of-spheres"}

Repeatedly applying the equivalence we just built, we can build an
equivalence

$$
(S^n \to_* A) \simeq (S^{n - 1} \to_* \Omega A) \simeq ... \simeq \Omega^n A,
$$

thus characterising $n$-fold loop spaces as basepoint-preserving maps
out of $S^n$, the $n$-dimensional sphere. As a special case, in the
zeroth dimension, we conclude that $(2 \to_* A) \equiv A$, i.e.,
basepoint-preserving maps from the booleans (based at either point) are
the same thing as points of $A$.

```agda
opaque

  Ωⁿ≃∙Sⁿ-map : ∀ {ℓ} {A : Type∙ ℓ} n → Maps∙ (Sⁿ n) A ≃∙ Ωⁿ n A
  Ωⁿ≃∙Sⁿ-map {A = A} zero = Iso→Equiv (from , iso to (λ _ → refl) invr) , refl where
    to : A .fst → ((Susp ⊥ , north) →∙ A)
    to x .fst north = A .snd
    to x .fst south = x
    to x .snd = refl

    from : ((Susp ⊥ , north) →∙ A) → A .fst
    from f = f .fst south

    invr : is-right-inverse from to
    invr (x , p) = Σ-pathp (funext (λ { north → sym p ; south → refl }))
      λ i j → p (~ i ∨ j)

  Ωⁿ≃∙Sⁿ-map {A = A} (suc n) =
    Maps∙ (Σ¹ (Sⁿ n)) A   ≃∙⟨ Σ-map∙≃∙map∙-Ω ⟩
    Maps∙ (Sⁿ n) (Ωⁿ 1 A) ≃∙⟨ Ωⁿ≃∙Sⁿ-map n ⟩
    Ωⁿ n (Ωⁿ 1 A)         ≃∙˘⟨ Ωⁿ-suc _ n ⟩
    Ωⁿ (suc n) A          ≃∙∎

Ωⁿ≃Sⁿ-map : ∀ {ℓ} {A : Type∙ ℓ} n → (Sⁿ n →∙ A) ≃ Ωⁿ n A .fst
Ωⁿ≃Sⁿ-map n = Ωⁿ≃∙Sⁿ-map n .fst
```

<!--
```agda
opaque
  unfolding Ωⁿ≃∙Sⁿ-map
```
-->

<details>
<summary>
We also show that this equivalence is [[natural|natural isomorphism]]
in $A$:

```agda
  Ωⁿ≃Sⁿ-map-natural
    : ∀ {ℓ ℓ'} {A : Type∙ ℓ} {B : Type∙ ℓ'} n
    → (f : A →∙ B) (l : Sⁿ n →∙ A)
    → Ωⁿ-map n f · (Ωⁿ≃Sⁿ-map n · l) ≡ Ωⁿ≃Sⁿ-map n · (f ∘∙ l)
```
</summary>

```agda
  Ωⁿ≃Sⁿ-map-natural zero f l = refl
  Ωⁿ≃Sⁿ-map-natural (suc n) f l =
    Ωⁿ-map (suc n) f · (Equiv.from (Ωⁿ-suc _ n .fst) (Ωⁿ≃Sⁿ-map n · (Σ-map∙≃map∙-Ω · l)))
      ≡⟨ Equiv.adjunctl (Ωⁿ-suc _ n .fst) (Ω-suc-natural n f ·ₚ _) ⟩
    Equiv.from (Ωⁿ-suc _ n .fst) ⌜ Ωⁿ-map n (Ω¹-map f) .fst (Ωⁿ≃Sⁿ-map n · (Σ-map∙≃map∙-Ω · l)) ⌝
      ≡⟨ ap! (Ωⁿ≃Sⁿ-map-natural n (Ω¹-map f) _) ⟩
    Equiv.from (Ωⁿ-suc _ n .fst) (Ωⁿ≃Sⁿ-map n · ⌜ Ω¹-map f ∘∙ Σ-map∙≃map∙-Ω · l ⌝)
      ≡⟨ ap! (Σ-map∙≃map∙-Ω-naturalr f l) ⟩
    Equiv.from (Ωⁿ-suc _ n .fst) (Ωⁿ≃Sⁿ-map n · (Σ-map∙≃map∙-Ω · (f ∘∙ l)))
      ∎
```
</details>

<!--
```agda
  Ωⁿ≃Sⁿ-map-inv-natural
    : ∀ {ℓ ℓ'} {A : Type∙ ℓ} {B : Type∙ ℓ'} n
    → (f : A →∙ B) (l : ⌞ Ωⁿ n A ⌟)
    → f ∘∙ Equiv.from (Ωⁿ≃Sⁿ-map n) l ≡ Equiv.from (Ωⁿ≃Sⁿ-map n) (Ωⁿ-map n f .fst l)
  Ωⁿ≃Sⁿ-map-inv-natural n f l = Equiv.adjunctl (Ωⁿ≃Sⁿ-map n) $
      sym (Ωⁿ≃Sⁿ-map-natural n f (Equiv.from (Ωⁿ≃Sⁿ-map n) l))
    ∙ ap (Ωⁿ-map n f .fst) (Equiv.ε (Ωⁿ≃Sⁿ-map n) l)
```
-->
