<!--
```agda
open import 1Lab.Path.Cartesian

open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning

open Functor
open _=>_
```
-->

```agda
module Cat.Diagram.Monad.Relative where
```

# Relative extension systems {defines=relative-extension-system}

By definition, [[monads]] must be endofunctors. For most applications,
this is sufficient, and the theory of monads is quite rich. However,
this restriction can become problematic. As an example, let $T$ be a
monad on $\Sets$, interpreted as an *algebraic theory*, where each fibre
$T(A)$ is interpreted as *the syntax of $T$ with $A$-many variables*. In
this situation, the unit interprets a variable as a term, and the
multiplication performs *substitution*.

However, we might wish to give a more refined treatment of
variables^[For instance, if we want to model a syntax where terms can
only have finitely many variables.], then we immediately run into issues:
We *want* to restrict $T$'s domain away from being an endofunctor $\Sets
\to \Sets$, but we can't make it into an endofunctor on $\FinSets$,
either! In all but the most trivial situations, the collection of syntax
trees on even a single variable is infinite.

So, if we want to work in a scenario like this, we will need to
generalise the notion of monad. The fundamental impediment is that we
can not take iterated composites of a functor $M : \cJ \to \cC$, so the
unit-and-multiplication presentation of monads will not do. However, we
can consider an alternative starting point: [[extension systems]], where
the problematic multiplication is replaced with an *extension*
operation, written $(-)^{M} : \cC(X,MY) \to \cC(MX, MY)$.

Since the type of the extension operation does not mention iterated
composites of $M$, we have cleared the main obstruction. It remains to
see that we can actually achieve something. Following
[@Altenkirch-Chapman-Uustalu:2015], we define a **relative extension
system**, over a functor $F : \cJ \to \cC$, as:

1. A mapping of objects, $M : J \to C$; and

2. A family of *unit* morphisms, $\eta_X : \cC(FX, MX)$; and

3. An *extension* operation, $(-)^{M} : \cC(FX,MY) \to \cC(MX, MY)$.

Like their non-relative counterparts, we do not require any
functoriality or naturality.

<!--
```agda
module _
  {oj ℓj oc ℓc}
  {J : Precategory oj ℓj}
  {C : Precategory oc ℓc}
  (F : Functor J C)
  where
  private
    module J = Cat.Reasoning J
    module C = Cat.Reasoning C
    module F = Cat.Functor.Reasoning F
```
-->

```agda
  record Relative-extension-system : Type (oj ⊔ oc ⊔ ℓc) where
    no-eta-equality
    field
      M₀ : J.Ob → C.Ob
      unit : ∀ {x} → C.Hom (F.₀ x) (M₀ x)
      bind : ∀ {x y} → C.Hom (F.₀ x) (M₀ y) → C.Hom (M₀ x) (M₀ y)
```

The equations for a relative extension system are similar to the
non-relative case.

```agda
      bind-unit-id : ∀ {x} → bind (unit {x}) ≡ C.id
      bind-unit-∘ : ∀ {x y} (f : C.Hom (F.₀ x) (M₀ y)) → bind f C.∘ unit ≡ f
      bind-∘
        : ∀ {x y z}
        → (f : C.Hom (F.₀ y) (M₀ z)) (g : C.Hom (F.₀ x) (M₀ y))
        → bind f C.∘ bind g ≡ bind (bind f C.∘ g)
```

The functorial action of $M$ on $f$ can be recovered by extending
$\eta \circ f$.

```agda
    M₁ : ∀ {x y} → J.Hom x y → C.Hom (M₀ x) (M₀ y)
    M₁ f = bind (unit C.∘ F.₁ f)
```

Furthermore, the latter two equations ensure naturality of the unit and
extension, respectively.

```agda
    unit-natural
      : ∀ {x y} (f : J.Hom x y)
      → unit C.∘ F.₁ f ≡ M₁ f C.∘ unit
    unit-natural f =
      unit C.∘ F.₁ f                 ≡˘⟨ bind-unit-∘ (unit C.∘ F.₁ f) ⟩
      bind (unit C.∘ F.₁ f) C.∘ unit ∎

    bind-naturall
      : ∀ {x y z} (f : J.Hom y z) (g : C.Hom (F.₀ x) (M₀ y))
      → M₁ f C.∘ bind g ≡ bind (M₁ f C.∘ g)
    bind-naturall f g =
      bind (unit C.∘ F.₁ f) C.∘ bind g   ≡⟨ bind-∘ (unit C.∘ (F.₁ f)) g ⟩
      bind (bind (unit C.∘ F.₁ f) C.∘ g) ∎

    bind-naturalr
      : ∀ {x y z} (f : C.Hom (F.₀ y) (M₀ z)) (g : J.Hom x y)
      → bind f C.∘ M₁ g ≡ bind (f C.∘ F.₁ g)
    bind-naturalr f g =
      bind f C.∘ bind (unit C.∘ F.₁ g)   ≡⟨ bind-∘ f (unit C.∘ F.₁ g) ⟩
      bind (bind f C.∘ unit C.∘ (F.₁ g)) ≡⟨ ap bind (C.pulll (bind-unit-∘ f)) ⟩
      bind (f C.∘ F.₁ g) ∎
```

Functoriality also follows.

```agda
    M-id : ∀ {x} → M₁ (J.id {x}) ≡ C.id
    M-id =
      bind (unit C.∘ F.₁ J.id) ≡⟨ ap bind (C.elimr F.F-id) ⟩
      bind unit                ≡⟨ bind-unit-id ⟩
      C.id                     ∎

    M-∘ : ∀ {x y z} → (f : J.Hom y z) (g : J.Hom x y) → M₁ (f J.∘ g) ≡ M₁ f C.∘ M₁ g
    M-∘ f g =
      bind (unit C.∘ F.₁ (f J.∘ g))  ≡⟨ ap bind (F.shufflel (unit-natural f)) ⟩
      bind (M₁ f C.∘ unit C.∘ F.₁ g) ≡˘⟨ bind-∘ (unit C.∘ F.₁ f) (unit C.∘ F.₁ g) ⟩
      M₁ f C.∘ M₁ g                  ∎
```

<!--
```agda
    M : Functor J C
    M .F₀ = M₀
    M .F₁ = M₁
    M .F-id = M-id
    M .F-∘ = M-∘
```
-->

However, note that we do **not** have a multiplication operation, as we
cannot iterate $M$!

<!--
```agda
module _
  {oj ℓj oc ℓc}
  {J : Precategory oj ℓj}
  {C : Precategory oc ℓc}
  {F : Functor J C}
  {E E' : Relative-extension-system F} where
  private
    module J = Cat.Reasoning J
    module C = Cat.Reasoning C
    module F = Cat.Functor.Reasoning F
    module E = Relative-extension-system E
    module E' = Relative-extension-system E'
    open Relative-extension-system

  Relative-extension-system-path
    : (p0 : ∀ x → E.M₀ x ≡ E'.M₀ x)
    → (∀ x → PathP (λ i → C.Hom (F.₀ x) (p0 x i)) E.unit E'.unit)
    → (∀ {x y} (f : ∀ i → C.Hom (F.₀ x) (p0 y i)) → PathP (λ i → C.Hom (p0 x i) (p0 y i)) (E.bind (f i0)) (E'.bind (f i1)))
    → E ≡ E'
  Relative-extension-system-path p0 punit pbind = sys where
    coe-pbind
      : ∀ i
      → {x y : J.Ob}
      → (f : C.Hom (F.₀ x) (p0 y i))
      → C.Hom (p0 x i) (p0 y i)
    coe-pbind i {x} {y} f = pbind (λ j → coe (λ i → C.Hom (F.₀ x) (p0 y i)) i j f) i

    sys : E ≡ E'
    sys i .M₀ x = p0 x i
    sys i .unit {x} = punit x i
    sys i .bind f = coe-pbind i f
    sys i .bind-unit-id {x} =
      is-prop→pathp (λ i → C.Hom-set (p0 x i) (p0 x i) (coe-pbind i (punit x i)) C.id)
        E.bind-unit-id
        E'.bind-unit-id i
    sys i .bind-unit-∘ {x} {y} f =
      hcomp (∂ i) λ where
        j (i = i0) → C.Hom-set _ _ _ _ base (E.bind-unit-∘ f) j
        j (i = i1) → C.Hom-set _ _ _ _ base (E'.bind-unit-∘ f) j
        j (j = i0) → base
      where
        base =
          coe0→i (λ i → (f : C.Hom (F.₀ x) (p0 y i)) → coe-pbind i f C.∘ punit x i ≡ f)
            i
            (λ f → E.bind-unit-∘ {x} {y} f) f
    sys i .bind-∘ {x} {y} {z} f g =
      hcomp (∂ i) λ where
        j (i = i0) → C.Hom-set _ _ _ _ base (E.bind-∘ f g) j
        j (i = i1) → C.Hom-set _ _ _ _ base (E'.bind-∘ f g) j
        j (j = i0) → base
      where
        base =
          coe0→i (λ i → (f : C.Hom (F.₀ y) (p0 z i)) (g : C.Hom (F.₀ x) (p0 y i)) → coe-pbind i f C.∘ coe-pbind i g ≡ coe-pbind i (coe-pbind i f C.∘ g))
            i
            (λ f g → E.bind-∘ {x} {y} f g) f g
```
-->

# Algebras over a relative extension system {defines=relative-extension-algebra}

A **relative extension algebra** over $E$ is the relative extension
system analog of an [[algebra over a monad]]. Following the general
theme of extension operations, a relative extension algebra on $X : \cC$
is given by an operation $\nu : \cC(FA, X) \to \cC(MA, X)$.
Intuitively, this operation lets us "evaluate" any $M$, so long as the
codomain of the evaluation is $X$.

<!--
```agda
module _
  {oj ℓj oc ℓc}
  {J : Precategory oj ℓj}
  {C : Precategory oc ℓc}
  {F : Functor J C}
  (E : Relative-extension-system F)
  where
  private
    module J = Cat.Reasoning J
    module C = Cat.Reasoning C
    module F = Cat.Functor.Reasoning F
    open Relative-extension-system E
```
-->

```agda
  record Relative-algebra-on (x : C.Ob) : Type (oj ⊔ ℓc) where
    no-eta-equality
    field
      ν : ∀ {a} (f : C.Hom (F.₀ a) x) → C.Hom (M₀ a) x
```

This operation must satisfy a pair of equations:

1. For every $f : \cC(FA, X)$, we must have $\nu(f) \circ \eta_{A} = f$;

2. For every $f : \cC(FB, X)$, and $g : \cC(FA, MB)$, we must have
   $\nu(f) \circ g^M = \nu(\nu f \circ g)$.

```agda
      ν-unit : ∀ {a} (f : C.Hom (F.₀ a) x) → ν f C.∘ unit ≡ f
      ν-bind
        : ∀ {a b} (f : C.Hom (F.₀ b) x) (g : C.Hom (F.₀ a) (M₀ b))
        → ν f C.∘ bind g ≡ ν (ν f C.∘ g)
```

From these, we can deduce a sort of naturality principle for $\nu$:

```agda
    ν-natural
      : ∀ {a b} (f : C.Hom (F.₀ b) x) (g : J.Hom a b)
      → ν f C.∘ M₁ g ≡ ν (f C.∘ F.₁ g)
    ν-natural f g =
      ν f C.∘ bind (unit C.∘ F.₁ g) ≡⟨ ν-bind f (unit C.∘ F.₁ g) ⟩
      ν (ν f C.∘ unit C.∘ F.₁ g)    ≡⟨ ap ν (C.pulll (ν-unit f)) ⟩
      ν (f C.∘ F.₁ g)  ∎
```

<!--
```agda
module _
  {oj ℓj oc ℓc}
  {J : Precategory oj ℓj}
  {C : Precategory oc ℓc}
  {F : Functor J C}
  {E : Relative-extension-system F}
  where
  private
    module J = Cat.Reasoning J
    module C = Cat.Reasoning C
    module F = Cat.Functor.Reasoning F
    open Relative-extension-system E
    open Relative-algebra-on

  Relative-algebra-on-pathp
    : ∀ {x y}
    → (p : x ≡ y)
    → {α : Relative-algebra-on E x}
    → {β : Relative-algebra-on E y}
    → (∀ {a} → (f : ∀ i → C.Hom (F.₀ a) (p i)) → PathP (λ i → C.Hom (M₀ a) (p i)) (α .ν (f i0)) (β .ν (f i1)))
    → PathP (λ i → Relative-algebra-on E (p i)) α β
  Relative-algebra-on-pathp {x} {y} p {α} {β} pν = sys where
    coe-ν : ∀ i → {a : J.Ob} → (f : C.Hom (F.₀ a) (p i)) → C.Hom (M₀ a) (p i)
    coe-ν i {a} f = pν (λ j → coe (λ i → C.Hom (F.₀ a) (p i)) i j f) i

    sys : PathP (λ i → Relative-algebra-on E (p i)) α β
    sys i .ν f = coe-ν i f
    sys i .ν-unit {a} f =
      hcomp (∂ i) λ where
        j (i = i0) → C.Hom-set _ _ _ _ base (α .ν-unit f) j
        j (i = i1) → C.Hom-set _ _ _ _ base (β .ν-unit f) j
        j (j = i0) → base
      where
        base =
          coe0→i (λ i → (f : C.Hom (F.₀ a) (p i)) → coe-ν i f C.∘ unit ≡ f)
            i
            (α .ν-unit) f
    sys i .ν-bind {a} {b} f g =
      hcomp (∂ i) λ where
        j (i = i0) → C.Hom-set _ _ _ _ base (α .ν-bind f g) j
        j (i = i1) → C.Hom-set _ _ _ _ base (β .ν-bind f g) j
        j (j = i0) → base
      where
        base =
          coe0→i (λ i → (f : C.Hom (F.₀ b) (p i)) → coe-ν i f C.∘ bind g ≡ coe-ν i (coe-ν i f C.∘ g))
            i
            (λ f → α .ν-bind f g) f
```
-->

# The relative Eilenberg-Moore category

We can also relativize the [[Eilenberg-Moore category]] to obtain the
**relative Eilenberg-Moore category**.

<!--
```agda
module _
  {oj ℓj oc ℓc}
  {J : Precategory oj ℓj}
  {C : Precategory oc ℓc}
  {F : Functor J C}
  (E : Relative-extension-system F)
  where
  private
    module J = Cat.Reasoning J
    module C = Cat.Reasoning C
    module F = Cat.Functor.Reasoning F
    open Relative-extension-system E
    open Relative-algebra-on
    open Displayed
```
-->

```agda
  Relative-Eilenberg-Moore : Displayed C (oj ⊔ ℓc) (oj ⊔ ℓc)
```

Objects over $x : \cC$ are given by relative extension algebras over $x$,
and maps over $f : \cC(x, y)$ between algebras $\alpha$ and $\beta$ are
relative extension algebra morphisms when, for every $g : \cC(F(a), x)$,
we have $f \circ \alpha(g) = \beta(f \circ g)$.

```agda
  Relative-Eilenberg-Moore .Ob[_] = Relative-algebra-on E
  Relative-Eilenberg-Moore .Hom[_] {x} {y} f α β =
    ∀ {a} (g : C.Hom (F.₀ a) x) → f C.∘ α .ν g ≡ β .ν (f C.∘ g)
```

It is straightforward to show that relative extension algebra morphisms
are closed under identities and composites.

```agda
  Relative-Eilenberg-Moore .id' {x = α} g =
    C.id C.∘ α .ν g   ≡⟨ C.idl _ ⟩
    α .ν g            ≡˘⟨ ap (α .ν) (C.idl _) ⟩
    α .ν (C.id C.∘ g) ∎
  Relative-Eilenberg-Moore ._∘'_ {x = α} {y = β} {z = γ} {f = f} {g = g} p q h =
    (f C.∘ g) C.∘ α .ν h   ≡⟨ C.pullr (q h) ⟩
    f C.∘ β .ν (g C.∘ h)   ≡⟨ p (g C.∘ h) ⟩
    γ .ν (f C.∘ g C.∘ h)   ≡⟨ ap (γ .ν) (C.assoc _ _ _) ⟩
    γ .ν ((f C.∘ g) C.∘ h) ∎
```

<details>
<summary>All of the equations are trivial.
</summary>
```agda
  Relative-Eilenberg-Moore .Hom[_]-set = hlevel!
  Relative-Eilenberg-Moore .idr' _ =
    is-prop→pathp (λ i → Π-is-hlevel' 1 λ _ → Π-is-hlevel 1 λ _ → C.Hom-set _ _ _ _) _ _
  Relative-Eilenberg-Moore .idl' _ =
    is-prop→pathp (λ i → Π-is-hlevel' 1 λ _ → Π-is-hlevel 1 λ _ → C.Hom-set _ _ _ _) _ _
  Relative-Eilenberg-Moore .assoc' _ _ _ =
    is-prop→pathp (λ i → Π-is-hlevel' 1 λ _ → Π-is-hlevel 1 λ _ → C.Hom-set _ _ _ _) _ _
```
</details>
