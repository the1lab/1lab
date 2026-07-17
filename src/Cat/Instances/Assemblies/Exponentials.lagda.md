<!--
```agda
open import Cat.Instances.Assemblies
open import Cat.Diagram.Exponential
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Prelude

open import Data.Partial.Total
open import Data.Partial.Base
open import Data.Vec.Base using ([]v ; _∷v_)

open import Realisability.PCA

import Cat.Instances.Assemblies.Limits

import Realisability.Data.Pair
import Realisability.PCA.Sugar
import Realisability.Base

open is-exponential
open Exponential
```
-->

```agda
module Cat.Instances.Assemblies.Exponentials {ℓA} (𝔸 : PCA ℓA) where
```

<!--
```agda
open Realisability.Data.Pair 𝔸
open Realisability.PCA.Sugar 𝔸
open Realisability.Base 𝔸

open Cat.Instances.Assemblies.Limits 𝔸

private variable
  ℓ ℓ' : Level
  X Y Z : Assembly 𝔸 ℓ
```
-->

# Exponentials in assemblies

Since we have a good handle on [[product assemblies]], and [[partial
combinatory algebras]] model *higher-order* (untyped) programming, we
should also expect to have an understanding of [[exponential objects]]
in assemblies. Indeed, they are simple to describe:

:::{.definition #exponential-assembly}
The **exponential assembly** $[X, Y]$ has underlying set the type of
assembly morphisms $X \to Y$. We let $\sf{e} \Vdash f$ if $\sf{e}$ is a
realiser for $f$ considered as a function of sets, i.e. $\sf{e}$ is
defined and
$$
\forall\, (x : X)\, (a : \bA),\ \sf{a} \Vdash x \to (\sf{e}\, \sf{a}) \Vdash f(x)
$$.
:::

```agda
_⇒Asm_ : Assembly 𝔸 ℓ → Assembly 𝔸 ℓ' → Assembly 𝔸 _
(X ⇒Asm Y) .Ob         = Assembly-hom X Y
(X ⇒Asm Y) .has-is-set = hlevel 2
(X ⇒Asm Y) .realisers f = record where
  mem e = record where
    ∣_∣ = ⌞ e ⌟ × □
      ( (x : ⌞ X ⌟) (a : ↯ ⌞ 𝔸 ⌟)
      → [ X ] a ⊩ x → [ Y ] e % a ⊩ f · x)
    is-tr = hlevel 1
  def = fst
```

Of course, every assembly morphism has *some* realiser by definition, so
every element of $[X, Y]$ is realised.

```agda
(X ⇒Asm Y) .realised f = do
  record { realiser = r ; tracks = t } ← f .tracked
  inc (r .fst , r .snd , inc λ x a → t {x} {a})
```

The evaluation morphism is, at the level of sets, defined as simply
application. It is tracked by the function which takes a pair and
applies its first component to its second. A typical calculation in
$\bA$ shows that this is a realiser.

```agda
asm-ev : Assembly-hom ((X ⇒Asm Y) ×Asm X) Y
asm-ev {X = X} {Y = Y} = to-assembly-hom record where
  map (f , x) = f · x

  realiser = val ⟨ u ⟩ `fst `· u `· (`snd `· u)

  tracks {a = x} = elim! λ p q α pp p⊩f q⊩a → subst⊩ Y (p⊩f _ _ q⊩a) $
    (val ⟨ u ⟩ `fst `· u `· (`snd `· u)) ⋆ x           ≡⟨ abs-β _ []v (_ , subst ⌞_⌟ (sym α) (`pair↓₂ pp (X .def q⊩a))) ⟩
    `fst ⋆ ⌜ x ⌝ ⋆ (`snd ⋆ ⌜ x ⌝)                      ≡⟨ ap! α ⟩
    `fst ⋆ (`pair ⋆ p ⋆ q) ⋆ (`snd ⋆ (`pair ⋆ p ⋆ q))  ≡⟨ ap₂ _%_ (`fst-β pp (X .def q⊩a)) (`snd-β pp (X .def q⊩a)) ⟩
    p ⋆ q                                              ∎
```

The currying of an assembly map is slightly more involved to formalise,
since we have multiple realisability relations to contend with. However,
conceptually, it suffices to consider the "outermost" level, i.e.
realisability in $[Y,Z]$.

```agda
curry-asm : Assembly-hom (X ×Asm Y) Z → Assembly-hom X (Y ⇒Asm Z)
curry-asm {X = X} {Y = Y} {Z = Z} h .map x = record where
  map y   = h · (x , y)
```

<!--
```agda
  tracked = do
    record { realiser = `h ; tracks = t } ← h .tracked
    (u , u⊩x) ← X .realised x

    inc record where
      realiser = val ⟨ v ⟩ `h `· (`pair `· const (u , X .def u⊩x) `· v)

      tracks a⊩x = subst⊩ Z (t (inc (u , _ , refl , u⊩x , a⊩x))) $
        abs-β _ []v (_ , Y .def a⊩x)
```
-->

This turns out to be very simple, since the currying of an assembly
morphism $X \times Y \to Z$ (with realiser, say, $\sf{h}$) is realised
by the currying-*qua*-program of $h$, i.e. $\langle u \rangle \langle v
\rangle\ h\ (u,\, v)$. A very simple computation in $\bA$ shows that this
is indeed a realiser.

```agda
curry-asm {X = X} {Y = Y} {Z = Z} h .tracked = do
  record { realiser = `h ; tracks = t } ← h .tracked
  inc record where
    realiser = val ⟨ u ⟩ ⟨ v ⟩ `h `· (`pair `· u `· v)

    tracks a⊩x = record where
      fst = subst ⌞_⌟ (sym (abs-βₙ []v ((_ , X .def a⊩x) ∷v []v))) (abs↓ _ _)
      snd = inc λ y b b⊩y → subst⊩ Z (t (inc (_ , _ , refl , a⊩x , b⊩y))) $
        abs-βₙ []v ((b , Y .def b⊩y) ∷v (_ , X .def a⊩x) ∷v []v)
```

<details>
<summary>All that remains is to show that evaluation and currying are
inverses, which is true at the level of the underlying sets.</summary>

```agda
Assemblies-exp : ∀ A B → Exponential (Assemblies 𝔸 ℓA) Assemblies-cartesian A B
Assemblies-exp A B .B^A = A ⇒Asm B
Assemblies-exp A B .ev = asm-ev
Assemblies-exp A B .has-is-exp .ƛ = curry-asm
Assemblies-exp A B .has-is-exp .commutes m = ext λ x y → refl
Assemblies-exp A B .has-is-exp .unique m' p = ext λ x y → sym p ·ₚ (x , y)

Assemblies-cc : Cartesian-closed (Assemblies 𝔸 ℓA) _
Assemblies-cc = record { has-exp = Assemblies-exp }
```

</details>
