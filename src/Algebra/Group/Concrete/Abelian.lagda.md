<!--
```agda
open import 1Lab.Path.Reasoning
open import 1Lab.Prelude

open import Algebra.Group.Instances.Integers
open import Algebra.Group.Cat.Base
open import Algebra.Group.Concrete
open import Algebra.Group.Ab

open import Cat.Functor.Equivalence
open import Cat.Morphism

open import Data.Set.Truncation

open import Homotopy.Space.Delooping
open import Homotopy.Connectedness
open import Homotopy.Space.Circle

open ConcreteGroup
```
-->

```agda
module Algebra.Group.Concrete.Abelian where
```

# Concrete abelian groups {defines="concrete-abelian-group"}

A **concrete [[abelian group]]** is, unsurprisingly, a [[concrete group]] in which
concatenation of loops at the base point is commutative.

```agda
module _ {ℓ} (G : ConcreteGroup ℓ) where
  is-concrete-abelian : Type ℓ
  is-concrete-abelian = ∀ (p q : pt G ≡ pt G) → p ∙ q ≡ q ∙ p
```

This is a property:

```agda
  open ConcreteGroup G using (H-Level-B)

  is-concrete-abelian-is-prop : is-prop is-concrete-abelian
  is-concrete-abelian-is-prop = hlevel 1
```

As an easy consequence, in an abelian group $\B{G}$, we can fill any square
that has equal opposite sides.

```agda
  concrete-abelian→square
    : is-concrete-abelian
    → {x : ⌞ B G ⌟} → (p q : x ≡ x) → Square p q q p
  concrete-abelian→square ab {x} = connected∙-elim-prop
    {P = λ x → (p q : x ≡ x) → Square p q q p}
    (G .has-is-connected)
    (hlevel 1)
    (λ p q → commutes→square (ab p q))
    x
```

Still unsurprisingly, the properties of being a concrete abelian group
and being an abelian group are [[equivalent over|equivalence over]]
the equivalence between concrete and abstract groups.

```agda
abelian≃abelian
  : ∀ {ℓ}
  → is-concrete-abelian ≃[ Concrete≃Abstract {ℓ} ] is-commutative-group
abelian≃abelian = prop-over-ext Concrete≃Abstract
  (λ {G} → is-concrete-abelian-is-prop G)
  (λ {G} → Group-on-is-abelian-is-prop (G .snd))
  (λ G G-ab → G-ab)
  (λ G G-ab → ∙-comm _ G-ab)
```

For example, the circle is abelian, being the delooping of $\mathbb{Z}$.

```agda
S¹-concrete-abelian : is-concrete-abelian S¹-concrete
S¹-concrete-abelian = Equiv.from (abelian≃abelian S¹-concrete ℤ π₁S¹≡ℤ)
  (Abelian→Group-on-abelian (ℤ-ab .snd))
```

## First abelian group cohomology

When $H$ is a concrete abelian group, something interesting happens: for any
other concrete group $G$, the set of pointed maps $\B{G} \to^\bullet \B{H}$ (i.e.
group homomorphisms from $G$ to $H$) turns out to be equivalent to the
[[set truncation]] of the type of *un*pointed maps, $\|\B{G} \to \B{H}\|_0$.

This is a special case of a theorem that relates this set truncation with the set
of orbits of the action of the *inner automorphism group* of $H$ on the set of group
homomorphisms $\B{G} \to^\bullet \B{H}$. We do not prove this here, but see
[@Symmetry, theorem 5.12.2]. In the special case that $H$ is abelian, its inner
automorphism group is trivial, and we can avoid quotienting.

In even fancier language, it is also a computation of the first *cohomology group*
of $G$ with coefficients in $H$, hence we adopt the notation
$H^1(G, H) = \|\B{G} \to \B{H}\|_0$.

```agda
H¹[_,_] : ∀ {ℓ ℓ'} → ConcreteGroup ℓ → ConcreteGroup ℓ' → Type (ℓ ⊔ ℓ')
H¹[ G , H ] = ∥ (⌞ B G ⌟ → ⌞ B H ⌟) ∥₀
```

First, note that there is always a natural map $(\B{G} \to^\bullet \B{H}) \to
H^1(G, H)$ that just forgets the pointing path.

```agda
class
  : ∀ {ℓ ℓ'} (G : ConcreteGroup ℓ) (H : ConcreteGroup ℓ')
  → (B G →∙ B H) → H¹[ G , H ]
class G H (f , _) = inc f
```

Now assume $H$ is abelian; we will show that this map is injective and surjective,
so that it is an equivalence of sets.

<!--
```agda
module _ {ℓ ℓ'}
  (G : ConcreteGroup ℓ)
  (H : ConcreteGroup ℓ') (H-ab : is-concrete-abelian H)
  where
  open ConcreteGroup H using (H-Level-B)
```
-->

Surjectivity is the easy part: since $H$ is connected, every map is merely
homotopic to a pointed map.

```agda
  class-surjective : is-surjective (class G H)
  class-surjective = ∥-∥₀-elim (λ _ → hlevel 2) λ f → do
    ptf ← H .has-is-connected (f (pt G))
    inc ((f , ptf) , refl)
```

For injectivity, we restrict our attention to the case of two pointed maps whose
underlying maps are *definitionally* equal. In other words, we prove that any
two pointings of $f$ (say $p, q : f(\point{G}) \equiv \point{H}$) yield
equal *pointed* maps.

In order to define our underlying homotopy, we proceed by induction: since
$G$ is a pointed connected type, it suffices to give a path $\alpha :
f(\point{G}) \equiv f(\point{G})$ and to show that every loop $l : \point{G}
\equiv \point{G}$ respects this identification, in the sense of the
following square:

~~~{.quiver}
\[\begin{tikzcd}
  {f(\point{G})} & {f(\point{G})} \\
  {f(\point{G})} & {f(\point{G})}
  \arrow["{\alpha}", from=1-1, to=1-2]
  \arrow["{\alpha}"', from=2-1, to=2-2]
  \arrow["{f(l)}"', from=1-1, to=2-1]
  \arrow["{f(l)}", from=1-2, to=2-2]
\end{tikzcd}\]
~~~

Since our homotopy additionally has to be *pointed*, we know that we must have
$\alpha = p \bullet q\inv$. This is where the fact that $H$ is abelian
comes in: the above square has equal opposite sides, so it automatically commutes.

```agda
  class-injective
    : ∀ f → (p q : f (pt G) ≡ pt H)
    → Path (B G →∙ B H) (f , p) (f , q)
  class-injective f p q = Σ-pathp
    (funext E.elim)
    (transpose (symP (∙→square'' E.elim-β-point)))
    where
      α : f (pt G) ≡ f (pt G)
      α = p ∙ sym q

      coh : ∀ (l : pt G ≡ pt G) → Square (ap f l) α α (ap f l)
      coh l = concrete-abelian→square H H-ab (ap f l) α

      module E = connected∙-elim-set {P = λ g → f g ≡ f g}
        (G .has-is-connected) (hlevel 2) α coh
```

By a quick path induction, we can conclude that `class`{.Agda} is an equivalence
between sets.

```agda
  class-is-equiv : is-equiv (class G H)
  class-is-equiv = injective-surjective→is-equiv! (inj _ _) class-surjective
    where
      inj : ∀ f g → class G H f ≡ class G H g → f ≡ g
      inj (f , ptf) (g , ptg) f≡g = ∥-∥-rec
        (ConcreteGroups-Hom-set G H _ _)
        (λ f≡g → J (λ g _ → ∀ ptg → (f , ptf) ≡ (g , ptg))
                   (class-injective f ptf)
                   f≡g ptg)
        (∥-∥₀-path.to f≡g)

  first-concrete-abelian-group-cohomology
    : (B G →∙ B H) ≃ H¹[ G , H ]
  first-concrete-abelian-group-cohomology
    = class G H , class-is-equiv
```

Translating this across our equivalence of categories gives a similar statement
for abstract groups.

<!--
```agda
module _ {ℓ}
  (G : Group ℓ)
  (H : Group ℓ) (H-ab : is-commutative-group H)
  where
```
-->

```agda
  Deloop-hom-equiv : (Deloop∙ G →∙ Deloop∙ H) ≃ Hom (Groups ℓ) G H
  Deloop-hom-equiv = ff+split-eso→hom-equiv π₁F
    (λ {G} {H} → π₁F-is-ff {_} {G} {H})
    π₁F-is-split-eso
    G H .snd .snd

  first-abelian-group-cohomology
    : H¹[ Concrete G , Concrete H ] ≃ Hom (Groups ℓ) G H
  first-abelian-group-cohomology =
    first-concrete-abelian-group-cohomology
      (Concrete G) (Concrete H)
      (Equiv.from (abelian≃abelian (Concrete H) H (Concrete≃Abstract.ε H)) H-ab)
      e⁻¹
    ∙e Deloop-hom-equiv
```
