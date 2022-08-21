```agda
open import Algebra.Group.Ab
open import Algebra.Group
open import Algebra.Ring

open import Cat.Functor.FullSubcategory
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Prelude

module Algebra.Ring.Module where
```

<!--
```agda
open is-ring-hom
open Displayed
```
-->

# Modules

A **module** over a ring $R$ is an abelian group $G$ equipped with an
action by $R$. Modules generalise the idea of vector space, which may be
familiar from linear algebra, by replacing the field of scalars by a
_ring_ of scalars. More pertinently, though, modules _specialise_
[functors]: specifically, functors into the category $\Ab$.

[functors]: Cat.Abelian.Instances.Functor.html

```agda
record Module {ℓ} ℓ′ (R : Ring ℓ) : Type (ℓ ⊔ lsuc ℓ′) where
  no-eta-equality
  field G : AbGroup ℓ′

  module R = Ring-on (R .snd)
  module G = AbGrp G renaming (_⋆_ to _+_)
  open G using (_+_) public

  field
    _⋆_     : R .fst → G.₀ → G.₀
    ⋆-id    : ∀ x → R.1R ⋆ x ≡ x
    ⋆-add-r : ∀ r x y → r ⋆ (x G.+ y) ≡ (r ⋆ x) G.+ (r ⋆ y)
    ⋆-add-l : ∀ r s x → (r R.+ s) ⋆ x ≡ (r ⋆ x) G.+ (s ⋆ x)
    ⋆-assoc : ∀ r s x → r ⋆ (s ⋆ x) ≡ (r R.* s) ⋆ x

  G₀ : Type ℓ′
  G₀ = G .Restrict-ob.object .fst
```

In much the same way that a monoid determines a 1-object category, a
ring determines a 1-object $\Ab$-category, and a module in the above
sense determines an $\Ab$-functor. In slightly more generality, though,
we can define homomorphisms $M \to N$ from an $R$-module to an
$S$-module, as long as we have a homomorphism $R \to S$.

We internalise this construction as a category [displayed over] the
category $\Rings$. The objects over a ring are given by the modules, and
the homomorphisms $M \to N$ over a map $f : R \to S$ are given by
$R$-module homomorphisms $M \to f^*(N)$, where $f^*(N)$ is the
_restriction of scalars_, defined below.

[displayed over]: Cat.Displayed.Base.html

```agda
Scalar-restriction
  : ∀ {ℓ ℓ′} {R S : Ring ℓ} → Rings.Hom R S → Module ℓ′ S → Module ℓ′ R
Scalar-restriction f M = N where
  module M = Module M
  open Module
```

The idea behind restriction of scalars is much simpler than the fanciful
name suggests: Given a map $f : R \to S$, we can transfer an $S$-action
on $G$ to an $R$-action by precomposition with $f$, hence the
contravariance.

```agda
  N : Module _ _
  N .G = M.G
  N ._⋆_ r m = f .fst r M.⋆ m

  N .⋆-id x        = ap (M._⋆ x) (f .snd .pres-id) ∙ M.⋆-id x
  N .⋆-add-r r x y = M.⋆-add-r _ x y
  N .⋆-add-l r s x = ap (M._⋆ x) (f .snd .pres-+ _ _) ∙ M.⋆-add-l _ _ x
  N .⋆-assoc r s x = M.⋆-assoc _ _ _ ∙ ap (M._⋆ x) (sym (f .snd .pres-* r s))
```

<!--
```agda
module
   _ {ℓ ℓ′} {R S : Ring ℓ} (M : Module ℓ′ R) (N : Module ℓ′ S) (f : Rings.Hom R S)
  where
  private
    module M = Module M
    module N = Module (Scalar-restriction f N)

  is-R-S-linear : (f : M.G₀ → N.G₀) → Type _
  is-R-S-linear f =
    ∀ r m s n → f ((r M.⋆ m) M.+ (s M.⋆ n)) ≡ (r N.⋆ f m) N.+ (s N.⋆ f n)

  R-S-linear-map : Type _
  R-S-linear-map = Σ _ is-R-S-linear

  abstract
    is-R-S-linear-is-prop : ∀ f → is-prop (is-R-S-linear f)
    is-R-S-linear-is-prop f a b i r m s n =
      N.G.has-is-set _ _ (a r m s n) (b r m s n) i

    R-S-linear-map-path : {x y : R-S-linear-map} → x .fst ≡ y .fst → x ≡ y
    R-S-linear-map-path = Σ-prop-path is-R-S-linear-is-prop
```
-->

We abbreviate the notion of $R$-linear map $M \to N$ over $f : R \to S$
as _$R$-$S$-linear maps_: To be perfectly explicit, this is a function
$M \to f^*(N)$ which satisfies the property
$$
f(rm + sn) = rf(m) + sf(n)\text{,}
$$
since our modules are unital, this implies that $f$ is a homomorphism of
between the groups underlying each module:
$$
f(m + n) = f(1m + 1n) = 1f(m) + 1f(n)\text{.}
$$

```agda
Mods : ∀ ℓ ℓ′ → Displayed (Rings ℓ) (ℓ ⊔ lsuc ℓ′) (ℓ ⊔ ℓ′)
Ob[ Mods ℓ ℓ′ ] R = Module ℓ′ R
Hom[ Mods ℓ ℓ′ ] f M N = R-S-linear-map M N f
Hom[ Mods ℓ ℓ′ ]-set f x y =
  Σ-is-hlevel 2 (fun-is-hlevel 2 (Module.G.has-is-set y)) λ g →
    is-prop→is-set (is-R-S-linear-is-prop x y f g)

Mods ℓ ℓ′ .id′ .fst x = x
Mods ℓ ℓ′ .id′ .snd r m s n = refl

Mods ℓ ℓ′ ._∘′_ (f , h) (g , i) .fst x = f (g x)
Mods ℓ ℓ′ ._∘′_ (f , h) (g , i) .snd r m s n = ap f (i r m s n) ∙ h _ _ _ _

Mods ℓ ℓ′ .idr′ {x = x} {y} {f} f′ = R-S-linear-map-path x y f refl
Mods ℓ ℓ′ .idl′ {x = x} {y} {f} f′ = R-S-linear-map-path x y f refl
Mods ℓ ℓ′ .assoc′ {w = w} {z = z} {f} {g} {h} f′ g′ h′ =
  R-S-linear-map-path w z (f Rings.∘ g Rings.∘ h) refl
```

The fibre of this displayed category over a ring $R$ is the _category of
$R$-modules_.

```agda
R-Mod : ∀ {ℓ} ℓ′ (R : Ring ℓ) → Precategory (ℓ ⊔ lsuc ℓ′) (ℓ ⊔ ℓ′)
R-Mod ℓ′ R = Fibre (Mods _ ℓ′) R
```

## As a fibration

Let us prove that `Mods`{.Agda} is not just displayed over the category
of rings, but fibred over it, too. But this is essentially something we
have already done: the data of a Cartesian fibration is essentially that
of a functorial reindexing of the fibres by morphisms in the base, but
this is given exactly by the restriction of scalars we defined above.

```agda
Mods-fibration : ∀ ℓ ℓ′ → Cartesian-fibration (Mods ℓ ℓ′)
Mods-fibration ℓ ℓ′ = mods where
  open Cartesian-fibration
  open Cartesian-lift
  open Cartesian
```

So, given a map $f : R \to S$ and an $S$-module $N$, how do we find a
universal $R$-module $X$ making the following diagram cartesian? Well,
I've already explained the answer, but our hand is essentially forced by
the definition of maps-over in `Mods`{.Agda}. Since $R$-$S$-linear maps
over $f : R \to S$ are defined as maps $X \to f^*(N)$, the freest choice
we can make is that which makes the identity function $R$-$S$-linear:
simply take $X = f^*(N)$.

~~~{.quiver}
\[\begin{tikzcd}
  {f^*(N)} && N \\
  \\
  R && S
  \arrow["f"', from=3-1, to=3-3]
  \arrow[Bar-{Triangle[open]}, from=1-3, to=3-3]
  \arrow[from=1-1, to=1-3]
  \arrow[Bar-{Triangle[open]}, from=1-1, to=3-1]
  \arrow[dr, phantom, "\lrcorner", very near start, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

```agda
  mods : Cartesian-fibration (Mods ℓ ℓ′)
  mods .has-lift f N = the-lift where
    the-lift : Cartesian-lift (Mods ℓ ℓ′) f N
    the-lift .x′ = Scalar-restriction f N
    the-lift .lifting .fst x = x
    the-lift .lifting .snd r m s n = refl
    the-lift .cartesian .universal m h′ = h′
    the-lift .cartesian .commutes {u′ = u′} m h′ =
       R-S-linear-map-path u′ N (f Rings.∘ m) refl
    the-lift .cartesian .unique {u′ = u′} {m} m′ p =
      R-S-linear-map-path u′ N (f Rings.∘ m) (ap fst p)
```

It is straightforward to calculate that this choice indeed furnishes a
Cartesian lift of $f$.
