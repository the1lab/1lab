<!--
```agda
open import 1Lab.Prelude

open import Homotopy.Conjugation
```
-->

```agda
module Homotopy.Loopspace where
```

<!--
```agda
private variable
  ℓ ℓ'  : Level
  A B C : Type∙ ℓ
```
-->

# Loop spaces {defines="loop-space"}

Given a [[pointed type]] $A$ (with basepoint $a_0$), we refer to the
type $a_0 \is a_0$ as the **loop space of $A$**, and write it $\Omega
A$. Since we always have $\refl_{a_0} : \Omega A$, this type is
itself naturally pointed.

```agda
Ω¹ : Type∙ ℓ → Type∙ ℓ
Ω¹ (A , a₀) = Path A a₀ a₀ , refl
```

If $(f, p) : A \to_* B$ is a [[pointed map]] and $\alpha : \Omega A$,
then we have $\ap{f}{\alpha} : f(a_0) \is f(a_0)$, which, while a loop
in the type underlying $B$, does not belong to $\Omega B$. However,
[[conjugation]] by $p$ is an equivalence from $\Omega (B, f(a_0))$ to
$\Omega B$, so that $p\inv \cdot \ap{f}{\alpha} \cdot p$ lands in the
right type. Since we have $p\inv \cdot \refl \cdot p \is \refl$, we see
that
$$\alpha \mapsto p\inv \cdot \ap{f}{\alpha} \cdot p$$
is itself a pointed map $\Omega A \to_* \Omega B$. Conjugating by $p$,
while necessary, introduces some complications in showing that this
makes $\Omega(-)$ into a functor --- if we could "get away with" only
using $\ap{f}(-)$, then this would be definitional.

Moreover, it initially looks as though we will have to identify the
pointedness proofs as well as the underlying maps, which would require
us to state and prove several annoying higher coherences involving
conjugation.

```agda
opaque
  Ω¹-map : (A →∙ B) → Ω¹ A →∙ Ω¹ B
  Ω¹-map (f , pt) .fst α = conj pt (ap f α)
  Ω¹-map (f , pt) .snd   = conj-of-refl pt
```

However, path (and thus loop) spaces are [[*homogeneous*]], so we can
obtain pointed homotopies from unpointed ones. This doesn't prevent us
from having to do path algebra with conjugation, but it does mean we
don't accumulate coherences on our coherences. We can thus show without
much pain that $\Omega(-)$ preserves identities, composition, and the
zero map.

```agda
  Ω¹-map-id : Ω¹-map {A = A} id∙ ≡ id∙
  Ω¹-map-id = homogeneous-funext∙ λ α →
    conj refl (ap id α) ≡⟨ conj-refl α ⟩
    α                   ∎

  Ω¹-map-∘ : (f : B →∙ C) (g : A →∙ B) → Ω¹-map f ∘∙ Ω¹-map g ≡ Ω¹-map (f ∘∙ g)
  Ω¹-map-∘ (f , f*) (g , g*) = homogeneous-funext∙ λ α →
    conj f* (ap f (conj g* (ap g α)))        ≡⟨ ap (conj f*) (ap-conj f g* (ap g α)) ⟩
    conj f* (conj (ap f g*) (ap (f ∘ g) α))  ≡⟨ conj-∙ _ _ _ ⟩
    conj (ap f g* ∙ f*) (ap (f ∘ g) α)       ∎

  Ω¹-map-zero : Ω¹-map (zero∙ {A = A} {B = B}) ≡ zero∙
  Ω¹-map-zero {B = B} = Σ-pathp (funext λ _ → conj-refl _) conj-refl-square
```

<!--
```agda
Ω¹-map∙ : Maps∙ A B →∙ Maps∙ (Ω¹ A) (Ω¹ B)
Ω¹-map∙ .fst = Ω¹-map
Ω¹-map∙ .snd = Ω¹-map-zero

Ω-Maps∙ : Ω¹ (Maps∙ A B) ≃∙ Maps∙ A (Ω¹ B)
Ω-Maps∙ .fst = twist , eqv where
  twist : Ω¹ (Maps∙ _ _) .fst → Maps∙ _ (Ω¹ _) .fst
  twist p .fst x i = p i .fst x
  twist p .snd i j = p j .snd i

  eqv : is-equiv twist
  eqv = is-iso→is-equiv λ where
    .is-iso.from f i → (λ x → f .fst x i) , (λ j → f .snd j i)
    .is-iso.rinv x → refl
    .is-iso.linv x → refl
Ω-Maps∙ {B = B} .snd i = (λ x j → B .snd) , λ j k → B .snd
```
-->

In passing, we note that since $\ap{e}(-)$ of a (pointed) equivalence is
itself an equivalence, and so is conjugation, the functorial action of
$\Omega(-)$ defined above carries equivalences to equivalences.

```agda
opaque
  unfolding Ω¹-map

  Ω¹-ap : A ≃∙ B → Ω¹ A ≃∙ Ω¹ B
  Ω¹-ap f .fst .fst = Ω¹-map (Equiv∙.to∙ f) .fst
  Ω¹-ap f .fst .snd = ∘-is-equiv (conj-is-equiv (f .snd)) (ap-equiv (f .fst) .snd)
  Ω¹-ap f .snd = Ω¹-map (Equiv∙.to∙ f) .snd
```

<!--
```agda
opaque
  unfolding Ω¹-ap conj

  Ω¹-ap-inv : (e : A ≃∙ B) → Equiv∙.inverse (Ω¹-ap e) ≡ Ω¹-ap (Equiv∙.inverse e)
  Ω¹-ap-inv (e , pt) = ≃∙-ext $ homogeneous-funext∙ λ l →
    let e⁻¹ = Equiv.from e in
    conj (Equiv.η e _) ⌜ ap e⁻¹ (conj (sym pt) l) ⌝        ≡⟨ ap! (ap-conj e⁻¹ _ _) ⟩
    conj (Equiv.η e _) (conj (ap e⁻¹ (sym pt)) (ap e⁻¹ l)) ≡⟨ conj-∙ _ _ _ ⟩
    conj ⌜ _ ⌝ (ap e⁻¹ l)                                  ≡˘⟨ ap¡ (sym-∙ _ _) ⟩
    conj (sym (Equiv.adjunctl e pt)) (ap e⁻¹ l)            ∎
```
-->

Finally, since both conjugation and $\ap{f}(-)$ do so, $\Omega(f)$
preserves path composition.

```agda
opaque
  unfolding Ω¹-map

  Ω¹-map-∙
    : ∀ (f : A →∙ B) p q
    → Ω¹-map f · (p ∙ q) ≡ Ω¹-map f · p ∙ Ω¹-map f · q
  Ω¹-map-∙ (f , f*) p q =
    conj f* (ap f (p ∙ q))              ≡⟨ ap (conj f*) (ap-∙ f _ _) ⟩
    conj f* (ap f p ∙ ap f q)           ≡⟨ conj-of-∙ f* _ _ ⟩
    conj f* (ap f p) ∙ conj f* (ap f q) ∎
```

## Higher loop spaces {defines="higher-loop-space"}

Since $\Omega$ is an endofunctor of pointed types, it can be iterated,
producing the **higher loop spaces** $\Omega^n A$ of $A$, with the
convention that $\Omega^0 A$ is simply $A$. We can also equip
$\Omega^n(-)$ with a functorial action by iterating that of $\Omega(-)$.

```agda
Ωⁿ : Nat → Type∙ ℓ → Type∙ ℓ
Ωⁿ zero    A = A
Ωⁿ (suc n) A = Ω¹ (Ωⁿ n A)

Ωⁿ-map      : ∀ n (e : A →∙ B) → Ωⁿ n A →∙ Ωⁿ n B
Ωⁿ-map zero    f = f
Ωⁿ-map (suc n) f = Ω¹-map (Ωⁿ-map n f)
```

<details>
<summary>

To show that this is a pointed functorial action preserving path
composition, we simply iterate the proofs that $\Omega(-)$ is
functorial. This gives us the following battery of lemmas:

```agda
Ωⁿ-map-id   : ∀ n → Ωⁿ-map {A = A} n id∙ ≡ id∙
Ωⁿ-map-zero : ∀ n → Ωⁿ-map n (zero∙ {A = A} {B = B}) ≡ zero∙

Ωⁿ-map-∘
  : ∀ n → (f : B →∙ C) (g : A →∙ B)
  → Ωⁿ-map n f ∘∙ Ωⁿ-map n g ≡ Ωⁿ-map n (f ∘∙ g)

Ωⁿ-map-∙
  : ∀ n (f : A →∙ B) p q
  → Ωⁿ-map (suc n) f · (p ∙ q)
  ≡ Ωⁿ-map (suc n) f · p ∙ Ωⁿ-map (suc n) f · q
```

</summary>

```agda
Ωⁿ-map-id zero    = refl
Ωⁿ-map-id (suc n) = ap Ω¹-map (Ωⁿ-map-id n) ∙ Ω¹-map-id

Ωⁿ-map-∘ zero    f g = refl
Ωⁿ-map-∘ (suc n) f g = Ω¹-map-∘ (Ωⁿ-map n f) (Ωⁿ-map n g) ∙ ap Ω¹-map (Ωⁿ-map-∘ n f g)

Ωⁿ-map-zero zero    = refl
Ωⁿ-map-zero (suc n) = ap Ω¹-map (Ωⁿ-map-zero n) ∙ Ω¹-map-zero

Ωⁿ-map-∙ n f p q = Ω¹-map-∙ (Ωⁿ-map n f) p q
```

</details>

<!--
```agda
opaque
  unfolding Ω¹-ap

  Ωⁿ-map-equiv : ∀ n (f : A →∙ B) → is-equiv (f .fst) → is-equiv (Ωⁿ-map n f .fst)
  Ωⁿ-map-equiv zero    f e = e
  Ωⁿ-map-equiv (suc n) f e = Ω¹-ap ((_ , Ωⁿ-map-equiv n f e) , _) .fst .snd

Ωⁿ-map∙ : ∀ n → Maps∙ A B →∙ Maps∙ (Ωⁿ n A) (Ωⁿ n B)
Ωⁿ-map∙ n .fst = Ωⁿ-map n
Ωⁿ-map∙ n .snd = Ωⁿ-map-zero n

Ωⁿ-ap
  : ∀ {ℓ ℓ'} {A : Type∙ ℓ} {B : Type∙ ℓ'} n (e : A ≃∙ B)
  → Ωⁿ n A ≃∙ Ωⁿ n B
Ωⁿ-ap {A = A} {B = B} n e∙@((e , eq) , p) = record
  { fst = e' .fst , Ωⁿ-map-equiv n (e , p) eq
  ; snd = e' .snd
  }
  where e' = Ωⁿ-map n (e , p)

Ωⁿ-ap-id : ∀ n → Ωⁿ-ap {A = A} n id≃∙ ≡ id≃∙
Ωⁿ-ap-id n with p ← Ωⁿ-map-id n = Σ-pathp (Σ-prop-path! (ap fst p)) (ap snd p)
```
-->

## Loop spaces at successors

Note that, unlike the HoTT book [-@HoTT], we have defined iterated loop
spaces so that they satisfy the recurrence
$$\Omega^{1 + n}(A) = \Omega \Omega^n(A)$$,
rather than
$$\Omega^{1 + n}(A) = \Omega^n \Omega(A)$$. This has the benefit of
definitionally "exposing" that $\Omega^{k + n}(A)$ is a $k$-fold
iterated path type as soon as $k$ is a literal number, but it does
significantly complicate showing that the lifting $\Omega^{1 + n}(f)$
agrees with $\Omega^n(\Omega f)$--- they don't even live in the same
type--- and this identification turns out to be a key component in
Whitehead's lemma.

We can, however, recursively identify $\Omega^{1+n}(A)$ with
$\Omega^n(\Omega A)$, and this identification naturally generates a
pointed equivalence. If desired, we could define the "book" version of
$\Omega^n$ and use this identification to prove that it agrees with
ours.

```agda
Ωⁿ-sucP : ∀ (A : Type∙ ℓ) n → Ωⁿ (suc n) A ≡ Ωⁿ n (Ω¹ A)
Ωⁿ-sucP A zero    = refl
Ωⁿ-sucP A (suc n) = ap Ω¹ (Ωⁿ-sucP A n)

Ωⁿ-suc : ∀ (A : Type∙ ℓ) n → Ωⁿ (suc n) A ≃∙ Ωⁿ n (Ω¹ A)
Ωⁿ-suc A n = path→equiv∙ (Ωⁿ-sucP A n)
```

Over this identification (on both the domain and codomain) we can then,
and once again recursively, identify $\Omega^{1 + n}(f)$ with
$\Omega^n(\Omega f)$.

```agda
Ω-suc-naturalP
  : ∀ {A : Type∙ ℓ} {B : Type∙ ℓ'} n (f : A →∙ B)
  → PathP (λ i → Ωⁿ-sucP A n i →∙ Ωⁿ-sucP B n i)
    (Ωⁿ-map (suc n) f) (Ωⁿ-map n (Ω¹-map f))
Ω-suc-naturalP zero    f = refl
Ω-suc-naturalP (suc n) f = apd (λ i → Ω¹-map) (Ω-suc-naturalP n f)
```

<!--
```agda
abstract
  Ω-suc-natural
    : ∀ {A : Type∙ ℓ} {B : Type∙ ℓ'} n (f : A →∙ B)
    → Equiv∙.to∙ (Ωⁿ-suc B n) ∘∙ Ωⁿ-map (suc n) f ∘∙ Equiv∙.from∙ (Ωⁿ-suc A n)
    ≡ Ωⁿ-map n (Ω¹-map f)
  Ω-suc-natural {A = A} {B = B} n f =
    let
      instance _ : Homogeneous (Ωⁿ n (Ωⁿ 1 B) .fst)
      _ = subst Homogeneous (ap fst (Ωⁿ-sucP B n)) auto
    in homogeneous-funext∙ λ x → from-pathp {A = λ i → ⌞ Ωⁿ-sucP B n i ⌟} λ i →
        Ω-suc-naturalP n f i .fst (coe1→i (λ i → ⌞ Ωⁿ-sucP A n i ⌟) i x)
```
-->
