<!--
```agda
open import 1Lab.Prelude

open import Algebra.Group.Concrete.Abelian
open import Algebra.Group.Concrete

open import Data.Set.Truncation
open import Data.Int.Base

open import Homotopy.Space.Suspension.Properties
open import Homotopy.Connectedness.Automation
open import Homotopy.Space.Sphere.Properties
open import Homotopy.Space.Suspension
open import Homotopy.Connectedness
open import Homotopy.Space.Circle
open import Homotopy.Space.Sphere
open import Homotopy.Conjugation
open import Homotopy.Loopspace
open import Homotopy.Base

open ConcreteGroup
```
-->

```agda
module Homotopy.Space.Sphere.Degree where
```

# Degrees of maps of spheres {defines="degree"}

Piecing together our [[characterisation|stability for spheres]] of the
[[homotopy groups]] of higher [[spheres]] $\pi_n(S^n)$ as the
[[group of integers]] $\bZ$ with the [[equivalence|loop spaces are maps
out of spheres]] between the $n$th [[loop space]] $\Omega^n A$ and the
space of [[pointed maps]] $S^n \to_* A$, we obtain a function which
associates to every pointed map $f : S^n \to_* S^n$ an integer; we call
this number the **degree** of $f$.

```agda
degree∙ : ∀ n → (Sⁿ (suc n) →∙ Sⁿ (suc n)) → Int
degree∙ n f = πₙSⁿ≃Int n · inc (Ωⁿ≃Sⁿ-map (suc n) · f)
```

Intuitively, the degree of a map $f$ is a generalisation of the winding
number of a loop in $S^1$: it measures how many times $f$ "wraps
around" the $n$-sphere. In particular, the degree of the identity map
is $1$ and the degree of the `zero∙`{.Agda} map is $0$.
To prove this, we first establish a useful property of the degrees of
maps of spheres.

The fact that the isomorphisms $\pi_n(S^n) \simeq \bZ$ are compatible
with [[suspension]] implies that the maps $f : S^n \to_* S^n$ and $\Susp f
: S^{n+1} \to_* S^{n+1}$ have the same degree; indeed, the functorial
action of $\Susp$ and the map $\Loop^n \sigma$ fit together in the
following diagram over $\bZ$:

~~~{.quiver}
\[\begin{tikzcd}
  {(S^n \to_* S^n)} && {(\Sigma\, S^n \to_* \Sigma\, S^n)} \\
  {\Omega^n\, S^n} && {\Omega^{n+1}\, S^{n+1}} \\
  & \bZ
  \arrow["\Sigma", from=1-1, to=1-3]
  \arrow["\sim"', from=1-1, to=2-1]
  \arrow["\sim", from=1-3, to=2-3]
  \arrow["{\Omega^n\, \sigma}", from=2-1, to=2-3]
  \arrow[from=2-1, to=3-2]
  \arrow[from=2-3, to=3-2]
\end{tikzcd}\]
~~~

```agda
opaque
  unfolding Ωⁿ≃∙Sⁿ-map

  Ωⁿ-suspend-is-Susp-map∙
    : ∀ {ℓ} (A : Type∙ ℓ) n (f : Sⁿ (suc n) →∙ A)
    → Ωⁿ≃Sⁿ-map (2 + n) · Susp-map∙ f
    ≡ Ωⁿ-suspend (suc n) _ · (Ωⁿ≃Sⁿ-map (suc n) · f)
  Ωⁿ-suspend-is-Susp-map∙ A n f =
    Equiv∙.from∙ (Ωⁿ-suc (Σ¹ A) (suc n)) · (Ωⁿ≃Sⁿ-map (suc n) · ⌜ Σ-map∙≃∙map∙-Ω · Susp-map∙ f ⌝)
      ≡⟨ ap! (Equiv.adjunctr Σ-map∙≃map∙-Ω (sym (suspend∙-is-unit f))) ⟩
    Equiv∙.from∙ (Ωⁿ-suc (Σ¹ A) (suc n)) · ⌜ Ωⁿ≃Sⁿ-map (suc n) · (suspend∙ A ∘∙ f) ⌝
      ≡˘⟨ ap¡ (Ωⁿ≃Sⁿ-map-natural (suc n) (suspend∙ A) f) ⟩
    Equiv∙.from∙ (Ωⁿ-suc (Σ¹ A) (suc n)) · (Ωⁿ-map (suc n) (suspend∙ A) · (Ωⁿ≃Sⁿ-map (suc n) · f))
      ∎

degree∙-Susp-map∙
  : ∀ n (f : Sⁿ (suc n) →∙ Sⁿ (suc n))
  → degree∙ (suc n) (Susp-map∙ f) ≡ degree∙ n f
degree∙-Susp-map∙ n f =
  πₙSⁿ≃Int (suc n) · ∥_∥₀.inc ⌜ Ωⁿ≃Sⁿ-map (2 + n) · Susp-map∙ f ⌝
    ≡⟨ ap! (Ωⁿ-suspend-is-Susp-map∙ (Sⁿ (suc n)) n f) ⟩
  πₙSⁿ≃Int (suc n) · inc (Ωⁿ-suspend (suc n) (Sⁿ (suc n)) · (Ωⁿ≃Sⁿ-map (suc n) · f))
    ≡⟨ πₙSⁿ≃Int-suspend n _ ⟩
  degree∙ n f
    ∎
```

This lets us characterise the degrees of the identity and zero maps by
induction: in both cases, the base case $S^1 \to_* S^1$ computes, and
the induction step uses the fact that $\Susp$ preserves those maps.

```agda
opaque
  unfolding conj Ω¹-map Ωⁿ≃∙Sⁿ-map

  degree∙-id∙ : ∀ n → degree∙ n id∙ ≡ 1
  degree∙-id∙ zero = refl
  degree∙-id∙ (suc n) =
    degree∙ (suc n) ⌜ id∙ ⌝                           ≡˘⟨ ap¡ (Susp-map∙-id {A∙ = Sⁿ (suc n)}) ⟩
    degree∙ (suc n) (Susp-map∙ {A∙ = Sⁿ (suc n)} id∙) ≡⟨ degree∙-Susp-map∙ n id∙ ⟩
    degree∙ n id∙                                     ≡⟨ degree∙-id∙ n ⟩
    1                                                 ∎

  degree∙-zero∙ : ∀ n → degree∙ n zero∙ ≡ 0
  degree∙-zero∙ zero = refl
  degree∙-zero∙ (suc n) =
    degree∙ (suc n) ⌜ zero∙ ⌝                           ≡˘⟨ ap¡ (Susp-map∙-zero {A∙ = Sⁿ (suc n)}) ⟩
    degree∙ (suc n) (Susp-map∙ {A∙ = Sⁿ (suc n)} zero∙) ≡⟨ degree∙-Susp-map∙ n zero∙ ⟩
    degree∙ n zero∙                                     ≡⟨ degree∙-zero∙ n ⟩
    0                                                   ∎
```

## Degrees of unpointed maps of spheres

We extend the definition of degrees above to *un*pointed maps
$S^n \to S^n$, by showing that the [[set]] of [[pointed homotopy]] classes
of maps $S^n \to_* S^n$ is equivalent to the set of homotopy classes of
unpointed maps $S^n \to S^n$.

We start by showing that the map $\|S^n \to_* S^n\|_0 \to \|S^n \to
S^n\|_0$ which forgets the pointing is injective; in other words, that
for any two paths $p, q : f(N) \is N$, the pointed maps $(f, p)$ and
$(f, q)$ are merely equal.

```agda
Sⁿ-unpoint
  : ∀ n
  → ∥ (Sⁿ (suc n) →∙ Sⁿ (suc n)) ∥₀
  → ∥ (⌞ Sⁿ (suc n) ⌟ → ⌞ Sⁿ (suc n) ⌟) ∥₀
Sⁿ-unpoint n = ∥-∥₀-rec (hlevel 2) λ (f , _) → inc f

Sⁿ-unpoint-injective
  : ∀ n f (p q : f north ≡ north)
  → ∥ Path (Sⁿ (suc n) →∙ Sⁿ (suc n)) (f , p) (f , q) ∥
```

There are two cases: when $n = 1$, $S^1$ is a [[concrete abelian group]],
and some abstract nonsense about [[first abelian group cohomology]]
tells us that the set of unpointed maps $\|S^1 \to S^1\|_0$ is
equivalent to the set of concrete group automorphisms of $S^1$, which is
just the set of pointed maps $S^1 \to_* S^1$.

```agda
Sⁿ-unpoint-injective zero f p q = inc (S¹-cohomology.injective refl)
  where
    Sⁿ⁼¹-concrete : ConcreteGroup lzero
    Sⁿ⁼¹-concrete .B = Sⁿ 1
    Sⁿ⁼¹-concrete .has-is-connected = connected∙
    Sⁿ⁼¹-concrete .has-is-groupoid = Equiv→is-hlevel 3 SuspS⁰≃S¹ S¹-is-groupoid

    Sⁿ⁼¹≡S¹ : Sⁿ⁼¹-concrete ≡ S¹-concrete
    Sⁿ⁼¹≡S¹ = ConcreteGroup-path (ua∙ SuspS⁰≃∙S¹)

    Sⁿ⁼¹-ab : is-concrete-abelian Sⁿ⁼¹-concrete
    Sⁿ⁼¹-ab = subst is-concrete-abelian (sym Sⁿ⁼¹≡S¹) S¹-concrete-abelian

    module S¹-cohomology = Equiv
      (first-concrete-abelian-group-cohomology Sⁿ⁼¹-concrete Sⁿ⁼¹-concrete Sⁿ⁼¹-ab)
```

The case $n \geq 2$ is a lot more down-to-earth: in that case, $S^n$ is
[[simply connected]], so the paths $p$ and $q$ are themselves merely
equal.

```agda
Sⁿ-unpoint-injective (suc n) f p q = ap (f ,_) <$> simply-connected p q
```

Since the $n$-sphere is [[connected]], every map $S^n \to S^n$ is merely
pointed, so the map `Sⁿ-unpoint`{.Agda} is also surjective, hence an
[[equivalence]] of sets.

```agda
Sⁿ-pointed≃unpointed
  : ∀ n
  → ∥ (Sⁿ (suc n) →∙ Sⁿ (suc n)) ∥₀
  ≃ ∥ (⌞ Sⁿ (suc n) ⌟ → ⌞ Sⁿ (suc n) ⌟) ∥₀
Sⁿ-pointed≃unpointed n .fst = Sⁿ-unpoint n
Sⁿ-pointed≃unpointed n .snd = injective-surjective→is-equiv! (inj _ _) surj
  where
    inj : ∀ f g → Sⁿ-unpoint n f ≡ Sⁿ-unpoint n g → f ≡ g
    inj = elim! λ f ptf g ptg f≡g →
      ∥-∥₀-path.from do
        f≡g ← ∥-∥₀-path.to f≡g
        J (λ g _ → ∀ ptg → ∥ (f , ptf) ≡ (g , ptg) ∥)
          (Sⁿ-unpoint-injective n f ptf)
          f≡g ptg

    surj : is-surjective (Sⁿ-unpoint n)
    surj = ∥-∥₀-elim (λ _ → hlevel 2) λ f → do
      pointed ← connected (f north) north
      pure (inc (f , pointed) , refl)
```

Since $\bZ$ is a set, we can therefore define the degree of an unpointed
map by set-truncation recursion on the corresponding class of pointed
maps, and show that the degree of a pointed map is the degree of its
underlying unpointed map.

```agda
degree : ∀ n → (⌞ Sⁿ (suc n) ⌟ → ⌞ Sⁿ (suc n) ⌟) → Int
degree n f = ∥-∥₀-rec (hlevel 2) (degree∙ n)
  (Equiv.from (Sⁿ-pointed≃unpointed n) (inc f))

degree≡degree∙ : ∀ n f∙ → degree n (f∙ .fst) ≡ degree∙ n f∙
degree≡degree∙ n f∙ = ap (∥-∥₀-rec _ _)
  (Equiv.η (Sⁿ-pointed≃unpointed n) (inc f∙))
```
