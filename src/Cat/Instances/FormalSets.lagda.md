<!--
```agda
open import Algebra.Ring.Commutative
open import Algebra.Ring.DualNumbers using (R[ε] ; ι-dual ; aug-dual ; aug-ι)

open import Cat.Instances.Presheaf.Exponentials
open import Cat.Instances.Presheaf.Limits
open import Cat.Diagram.Exponential
open import Cat.Diagram.Terminal
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Instances.Presheaf.Cohesive
import Cat.Reasoning

open Precategory
open Terminal
open Functor
open _=>_
```
-->

```agda
module Cat.Instances.FormalSets {ℓ} (R : CRing ℓ) where
```

<!--
```agda
private
  module CR = Cat.Reasoning (CRings ℓ)
```
-->

# Formal sets: the topos of infinitesimal probes {defines="formal-sets infinitesimal-site"}

Following the "algebraic geometry" reading of probes — a space is
known by the algebras of functions on the shapes probing it — the
**infinitesimally thickened points** are the formal duals of the
[[dual numbers|dual-numbers]] and their relatives: spaces with a
single global point, but a non-trivial infinitesimal *halo* around
it. We construct here the smallest interesting site of this kind,
the *walking* first-order infinitesimal: two objects, the point
$\ast$ (dual to $R$) and the first-order disk $\bD$ (dual to
$R[\epsilon]$), with morphisms the $R$-algebra homomorphisms between
their function rings, reversed.

```agda
data Probe : Type ℓ where
  pt  : Probe
  εpt : Probe

dual : Probe → CRing ℓ
dual pt = R
dual εpt = R[ε] R

struct : ∀ p → CR.Hom R (dual p)
struct pt = CR.id
struct εpt = ι-dual R
```

A morphism of probes $x \to y$ is an $R$-algebra map
$\cO(y) \to \cO(x)$: a ring homomorphism commuting with the
structure maps from $R$. Since the commutativity condition is a
proposition, composition and the category laws come directly from
those of rings.

```agda
record Probe-hom (x y : Probe) : Type ℓ where
  no-eta-equality
  constructor probe-hom
  field
    fun      : CR.Hom (dual y) (dual x)
    commutes : fun CR.∘ struct y ≡ struct x
```

<!--
```agda
open Probe-hom

private unquoteDecl eqv = declare-record-iso eqv (quote Probe-hom)

Probe-hom-path
  : ∀ {x y} {f g : Probe-hom x y} → f .fun ≡ g .fun → f ≡ g
Probe-hom-path {f = f} {g} p i .fun = p i
Probe-hom-path {x} {y} {f = f} {g} p i .commutes =
  is-prop→pathp (λ i → CR.Hom-set R (dual x) (p i CR.∘ struct y) (struct x))
    (f .commutes) (g .commutes) i

Probe-hom-set : ∀ x y → is-set (Probe-hom x y)
Probe-hom-set x y = Iso→is-hlevel 2 eqv $
  Σ-is-hlevel 2 (CR.Hom-set _ _) λ h → is-prop→is-set (CR.Hom-set _ _ _ _)
```
-->

```agda
Infinitesimals : Precategory ℓ ℓ
Infinitesimals .Ob = Probe
Infinitesimals .Hom = Probe-hom
Infinitesimals .Hom-set = Probe-hom-set
Infinitesimals .id = probe-hom CR.id (CR.idl _)
Infinitesimals ._∘_ {z = z} f g = probe-hom
  (g .fun CR.∘ f .fun)
  ( sym (CR.assoc (g .fun) (f .fun) (struct z))
  ∙ ap (g .fun CR.∘_) (f .commutes) ∙ g .commutes)
Infinitesimals .idr f = Probe-hom-path (CR.idl _)
Infinitesimals .idl f = Probe-hom-path (CR.idr _)
Infinitesimals .assoc f g h =
  Probe-hom-path (sym (CR.assoc (h .fun) (g .fun) (f .fun)))
```

The point is the terminal probe — dually, $R$ is the initial
$R$-algebra — so this site supports the [[cohesion|cohesive-topos]]
adjunctions, and the paper's map $\iota : \ast \to \bD$ is dual to
the augmentation.

```agda
pt-terminal : Terminal Infinitesimals
pt-terminal .top = pt
pt-terminal .has⊤ x .centre = probe-hom (struct x) (CR.idr _)
pt-terminal .has⊤ x .paths h =
  Probe-hom-path (sym (h .commutes) ∙ CR.idr _)

ι∞ : Infinitesimals .Hom pt εpt
ι∞ = probe-hom (aug-dual R) (aug-ι R)
```

**Formal sets** are the presheaves on this site: spaces probeable by
the point and by the infinitesimal disk. This is the constructive
skeleton of the paper's $\rm{FrmlSmthSet} = \rm{Sh}(\rm{ThCrtSp})$,
with the smooth direction stripped away and the infinitesimal
direction retained exactly.

```agda
FrmlSet : Precategory (lsuc ℓ) ℓ
FrmlSet = PSh ℓ Infinitesimals

𝔻 : ⌞ FrmlSet ⌟
𝔻 = よ₀ Infinitesimals εpt

module FrmlSet-cohesion =
  Cat.Instances.Presheaf.Cohesive Infinitesimals pt-terminal
```

<!--
```agda
private
  module PC = Cartesian-closed (PSh-closed Infinitesimals)
  module FS = Cat.Reasoning FrmlSet

zero-𝔻 : ∀ (U : Probe) → Infinitesimals .Hom U εpt
zero-𝔻 U =
  Infinitesimals ._∘_ {U} {pt} {εpt} ι∞ (pt-terminal .has⊤ U .centre)

zero-𝔻-natural
  : ∀ {U V} (g : Infinitesimals .Hom V U)
  → Infinitesimals ._∘_ (zero-𝔻 U) g ≡ zero-𝔻 V
zero-𝔻-natural {U} {V} g =
    sym (Infinitesimals .assoc ι∞ (pt-terminal .has⊤ U .centre) g)
  ∙ ap (λ h → Infinitesimals ._∘_ {V} {pt} {εpt} ι∞ h)
      (is-contr→is-prop (pt-terminal .has⊤ V)
        (Infinitesimals ._∘_ (pt-terminal .has⊤ U .centre) g)
        (pt-terminal .has⊤ V .centre))
```
-->

## The tangent bundle as a mapping space

The payoff is Schreiber's (16): in a topos of spaces containing an
infinitesimal disk, the **tangent bundle** is no extra structure but
simply the [[mapping space|exponential object]] out of the disk,

$$
T X := \rm{Maps}(\bD, X)
$$

with the bundle projection given by restriction along
$\iota : \ast \to \bD$ — "evaluating a tangent vector at its base
point".

```agda
T : ⌞ FrmlSet ⌟ → ⌞ FrmlSet ⌟
T X = PC.[ 𝔻 , X ]

T-proj : ∀ X → FS.Hom (T X) X
T-proj X .η U f = f .η U (Infinitesimals .id , zero-𝔻 U)
T-proj X .is-natural U V g = funext λ f →
    ap (f .η V) (Σ-pathp
      (Infinitesimals .idr g ∙ sym (Infinitesimals .idl g))
      (sym (zero-𝔻-natural g)))
  ∙ happly (f .is-natural U V g) (Infinitesimals .id , zero-𝔻 U)
```

Concretely, and in the paper's language of plots: a *tangent vector*
of $X$ — a plot of $T X$ by the point — is exactly a plot of $X$ by
the infinitesimal disk, an "infinitesimal curve" in $X$.

```agda
T-at-point : ∀ X → ∣ T X .F₀ pt ∣ ≃ ∣ X .F₀ εpt ∣
T-at-point X = Iso→Equiv (to , iso from ri li) where
  to : ∣ T X .F₀ pt ∣ → ∣ X .F₀ εpt ∣
  to f = f .η εpt (pt-terminal .has⊤ εpt .centre , Infinitesimals .id)

  from : ∣ X .F₀ εpt ∣ → ∣ T X .F₀ pt ∣
  from x .η V (u , d) = X .F₁ d x
  from x .is-natural V W g = funext λ (u , d) →
    happly (X .F-∘ g d) x

  ri : is-right-inverse from to
  ri x = happly (X .F-id) x

  li : is-left-inverse from to
  li f = Nat-path {C = Infinitesimals ^op} {D = Sets ℓ} λ V → funext λ (u , d) →
      sym (happly (f .is-natural εpt V d)
        (pt-terminal .has⊤ εpt .centre , Infinitesimals .id))
    ∙ ap (f .η V) (Σ-pathp
        (is-contr→is-prop (pt-terminal .has⊤ V) _ _)
        (Infinitesimals .idl d))
```

Under this identification the bundle projection is the presheaf
action of $\iota$ — restricting an infinitesimal curve to its base
point:

```agda
_ : (X : ⌞ FrmlSet ⌟) → ∣ X .F₀ εpt ∣ → ∣ X .F₀ pt ∣
_ = λ X → X .F₁ ι∞
```

The higher-order disks $\bD^m_k$, dual to
$R[\epsilon_1, \dots, \epsilon_m]/(\epsilon^{k+1})$, extend this site
in the evident way; jet bundles arise from them just as the tangent
bundle arises from $\bD$. We leave the general Weil-algebra site to
future work.
