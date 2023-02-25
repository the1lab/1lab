<!--
```agda
open import Algebra.Group.Ab
open import Algebra.Group
open import Algebra.Ring

open import Cat.Displayed.Univalence.Thin
open import Cat.Functor.FullSubcategory
open import Cat.Displayed.Cartesian
open import Cat.Functor.Adjoint.Hom
open import Cat.Displayed.Fibre
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import Cat.Displayed.Base
open import Cat.Abelian.Base
open import Cat.Abelian.Endo
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Algebra.Ring.Module where
```

<!--
```agda
open is-ring-hom
open Displayed
open Total-hom
open Functor
```
-->

# Modules

A **module** over a \r{ring} $R$ is an \r{abelian group} $G$ equipped
with an action by $R$. Modules generalise the idea of vector spaces,
which may be familiar from linear algebra, by replacing the field of
scalars by a _ring_ of scalars. More pertinently, though, modules
_specialise_ [functors]: specifically, functors into the category $\Ab$.

[functors]: Cat.Abelian.Instances.Functor.html

For silly formalisation reasons, when defining modules, we do not take
"an $\Ab$-functor into $\Ab$" as the definition: this correspondence is
a theorem we prove later. Instead, we define a record packaging an
$R$-module structure _on_ an abelian group:

```agda
record Module-on {ℓ ℓ′} (R : Ring ℓ) (G : Abelian-group ℓ′) : Type (ℓ ⊔ lsuc ℓ′) where
```

<!--
```agda
  no-eta-equality

  module R = Ring-on (R .snd)
  module G = Abelian-group-on (G .snd) renaming (_*_ to _+_)
  open G using (_+_) public
```
-->

Nicely typeset, the data of an $R$-module structure on a group $G$ is
given by a _multiplication_ by $R$, a function $\star : R \to G \to
G$^[We generally elide the star and write only $rx$ for $r \star x$.],
such that:

- For every $r : R$, the function $r \star -$ is a group homomorphism $G
\to G$: We have $r(x + y) = rx + ry$;
- Left multiplication is a ring homomorphism onto $G \to G$: We have
equalities $1x = x$, $(r+s)x = rx + sx$, and $(rs)x$ = r(sx)$.

**Note**: Even though we do not require all rings to be commutative, we
only care about doing algebra with commutative rings. Because of this,
we don't differentiate between left and right modules.

```agda
  field
    _⋆_     : ⌞ R ⌟ → ⌞ G ⌟ → ⌞ G ⌟
    ⋆-id    : ∀ x → R.1r ⋆ x ≡ x
    ⋆-add-r : ∀ r x y → r ⋆ (x G.+ y) ≡ (r ⋆ x) G.+ (r ⋆ y)
    ⋆-add-l : ∀ r s x → (r R.+ s) ⋆ x ≡ (r ⋆ x) G.+ (s ⋆ x)
    ⋆-assoc : ∀ r s x → r ⋆ (s ⋆ x) ≡ (r R.* s) ⋆ x
```

<!--
```agda
  ⋆-group-hom : ∀ (r : ⌞ R ⌟) → is-group-hom (Abelian→Group-on (G .snd)) (Abelian→Group-on (G .snd)) (r ⋆_)
  ⋆-group-hom r .is-group-hom.pres-⋆ = ⋆-add-r r
  module ⋆-group-hom r = is-group-hom (⋆-group-hom r)

  ⋆-group-homᵣ : ∀ (x : ⌞ G ⌟)
    → is-group-hom
        (record { has-is-group = is-abelian-group.has-is-group R.+-group })
        (Abelian→Group-on (G .snd))
        (_⋆ x)
  ⋆-group-homᵣ x .is-group-hom.pres-⋆ y z = ⋆-add-l y z x
  module ⋆-group-homᵣ x = is-group-hom (⋆-group-homᵣ x)
  infixr 25 _⋆_

Module : ∀ {ℓ} ℓ′ → Ring ℓ → Type (lsuc ℓ′ ⊔ ℓ)
Module ℓ′ R = Σ (Abelian-group ℓ′) λ G → Module-on R G
module Module {ℓ ℓ′} {R : Ring ℓ} (M : Module ℓ′ R) where
  open Module-on (M .snd) public
```
-->

In much the same way that a monoid determines a 1-object category, a
ring determines a 1-object $\Ab$-category, and a module in the above
sense determines an $\Ab$-functor: so there should be a category of
$R$-modules, in the same way that there is a category of $\Ab$-functors
(between fixed domain/codomain categories).

Modules can be considered in slightly more generality, however: Rather
than considering only homomorphisms between $R$-modules $M \to N$, for a
fixed $R$, we can define homomorphisms _between modules over different
rings_, as long as we have a ring homomorphism to mediate the
difference.

We formalise this construction by defining a "big category of modules"
as being [displayed over] the category $\Rings$. The objects over a ring
$R$ are precisely the $R$-modules, and the homomorphisms $M \to N$ over
a map $f : R \to S$ are given by $R$-module homomorphisms $M \to
f^*(N)$, where $f^*(N)$ is the _restriction of scalars_, defined below.

[displayed over]: Cat.Displayed.Base.html

```agda
Scalar-restriction
  : ∀ {ℓ ℓ′} {G : Abelian-group ℓ′} {R S : Ring ℓ}
  → Rings.Hom R S → Module-on S G → Module-on R G
Scalar-restriction {G = G} f M = N where
  module M = Module-on M
  open Module-on
```

The idea behind restriction of scalars is much simpler than the fanciful
name suggests: Given a map $f : R \to S$, we can transfer an $S$-action
on $G$ to an $R$-action by precomposition with $f$. Since we're
transporting it by _pre_composition, we get a little contravariance, as
a treat.

```agda
  N : Module-on _ G
  N ._⋆_ r m = f # r M.⋆ m

  N .⋆-id x        = ap (M._⋆ x) (f .preserves .pres-id) ∙ M.⋆-id x
  N .⋆-add-r r x y = M.⋆-add-r _ x y
  N .⋆-add-l r s x = ap (M._⋆ x) (f .preserves .pres-+ _ _) ∙ M.⋆-add-l _ _ x
  N .⋆-assoc r s x = M.⋆-assoc _ _ _ ∙ ap (M._⋆ x) (sym (f .preserves .pres-* r s))
```

<!--
```agda
module
   _ {ℓ ℓ′ ℓ′′} {R S : Ring ℓ} (M : Module ℓ′ R) (N : Module ℓ′′ S)
     (f : Rings.Hom R S)
  where
  private
    module M = Module-on (M .snd)
    module N = Module-on (Scalar-restriction f (N .snd))

  is-R-S-bilinear : (f : ⌞ M ⌟ → ⌞ N ⌟) → Type _
  is-R-S-bilinear f =
    ∀ r m s n → f (r M.⋆ m M.+ s M.⋆ n) ≡ r N.⋆ f m N.+ s N.⋆ f n

  record Linear-map : Type (ℓ ⊔ ℓ′ ⊔ ℓ′′) where
    no-eta-equality
    field
      map : ⌞ M ⌟ → ⌞ N ⌟
      linear : is-R-S-bilinear map

    linear-simple : ∀ x y → x N.⋆ map y ≡ map (x M.⋆ y)
    linear-simple x y =
      x N.⋆ map y                           ≡⟨ N.G.intror (N.⋆-group-homᵣ.pres-id _) ⟩
      x N.⋆ map y N.+ N.R.0r N.⋆ map M.G.1g ≡˘⟨ linear _ _ _ _ ⟩
      map (x M.⋆ y M.+ M.R.0r M.⋆ M.G.1g)   ≡⟨ ap map (M.G.elimr (M.⋆-group-homᵣ.pres-id _)) ⟩
      map (x M.⋆ y)                         ∎

    has-group-hom : is-group-hom (Abelian→Group-on (M .fst .snd)) (Abelian→Group-on (N .fst .snd)) map
    has-group-hom .is-group-hom.pres-⋆ x y =
      map (x M.+ y)                         ≡⟨ ap map (ap₂ M._+_ (sym (M.⋆-id _)) (sym (M.⋆-id _))) ⟩
      map (M.R.1r M.⋆ x M.+ M.R.1r M.⋆ y)   ≡⟨ linear M.R.1r x N.R.1r y ⟩
      M.R.1r N.⋆ map x N.+ M.R.1r N.⋆ map y ≡⟨ ap₂ N._+_ (N.⋆-id _) (N.⋆-id _) ⟩
      map x N.+ map y                       ∎
    module has-group-hom = is-group-hom has-group-hom

  open Linear-map public

  abstract
    is-R-S-bilinear-is-prop : ∀ f → is-prop (is-R-S-bilinear f)
    is-R-S-bilinear-is-prop f a b i r m s n =
      N.G.has-is-set _ _ (a r m s n) (b r m s n) i

module
   _ {ℓ ℓ′ ℓ′′} {R S : Ring ℓ}
     {M : Module ℓ′ R} {N : Module ℓ′′ S} {f : I → Rings.Hom R S}
  where
  private module N i = Module-on (Scalar-restriction (f i) (N .snd))

  Linear-map-path : ∀ {x y} → x .map ≡ y .map → PathP (λ i → Linear-map M N (f i)) x y
  Linear-map-path {x} {y} p i .map = p i
  Linear-map-path {x} {y} p i .linear r m s n =
    is-prop→pathp
      (λ i → N.G.has-is-set i
        (p i _)
        (N._+_ i (N._⋆_ i r (p i m)) (N._⋆_ i s (p i n))))
      (x .linear r m s n)
      (y .linear r m s n) i

private unquoteDecl eqv = declare-record-iso eqv (quote Linear-map)
Linear-map-is-set
  : ∀ {ℓ ℓ′ ℓ′′} {R S : Ring ℓ} {x : Module ℓ′ R} {y : Module ℓ′′ S}
  → {f : Rings.Hom R S}
  → is-set (Linear-map x y f)
Linear-map-is-set {x = x} {y} {f} =
  Iso→is-hlevel 2 eqv $
  Σ-is-hlevel 2 (fun-is-hlevel 2 (Module.G.has-is-set y)) λ g →
    is-prop→is-set (is-R-S-bilinear-is-prop x y f g)
```
-->

We abbreviate the sentence "a linear map $M \to N$ over a ring
homomorphism $f : R \to S$" using the name **$R$-$S$-bilinear map**, even
though this might not be perfectly accurate to existing literature on
commutative algebra. Being explicit, this is a function between the sets
$M \to f^*(N)$, satisfying the property

$$
f(rm + sn) = rf(m) + sf(n)\text{.}
$$

Since our modules are unital, this compressed definition still implies
that $f$ is a homomorphism of abelian groups $M \to N$, as the following
calculation shows:

$$
f(m + n) = f(1m + 1n) = 1f(m) + 1f(n) = f(m) + f(n)\text{.}
$$

```agda
Mods : ∀ ℓ ℓ′ → Displayed (Rings ℓ) (ℓ ⊔ lsuc ℓ′) (ℓ ⊔ ℓ′)
Ob[ Mods ℓ ℓ′ ] R = Module ℓ′ R
Hom[ Mods ℓ ℓ′ ] f M N = Linear-map M N f
Hom[ Mods ℓ ℓ′ ]-set f x y = Linear-map-is-set

Mods _ _ .id′ .map x = x
Mods _ _ .id′ .linear r m s n = refl

Mods _ _ ._∘′_ f g .map x = f .map (g .map x)
Mods _ _ ._∘′_ f g .linear r m s n =
  ap (f .map) (g .linear r m s n) ∙ f .linear _ _ _ _

Mods _ _ .idr′ f′ = Linear-map-path refl
Mods _ _ .idl′ f′ = Linear-map-path refl
Mods _ _ .assoc′ f′ g′ h′ = Linear-map-path refl
```

The fibre of this displayed category over a ring $R$ is the _category of
$R$-modules_.

```agda
R-Mod : ∀ {ℓ} ℓ′ (R : Ring ℓ) → Precategory (ℓ ⊔ lsuc ℓ′) (ℓ ⊔ ℓ′)
R-Mod ℓ′ R = Fibre′ (Mods _ ℓ′) R fix coh where
```

<!--
```agda
  -- For computation reasons we use a custom reindexing function to
  -- define R-Mod. Since the definition of Linear-map depends only on
  -- the map component of the ring homomorphism, for which id ∘ id is
  -- definitionally id (and for which path coming from the definition of
  -- Ring would be refl), we can omit a transport refl:

  fix : ∀ {x y : Module ℓ′ R} → Linear-map x y (Rings.id Rings.∘ Rings.id)
      → Linear-map x y Rings.id
  fix x .map = x .map
  fix x .linear = x .linear

  abstract
    coh : ∀ {x y : Module ℓ′ R} (f : Linear-map x y (Rings.id Rings.∘ Rings.id))
        → fix f ≡ transport (λ i → Hom[_] (Mods _ ℓ′) (Rings.idl Rings.id i) x y) f
    coh f = Linear-map-path $ funext λ x → Regularity.fast! refl
```
-->

```agda
module R-Mod {ℓ ℓ′} {R : Ring ℓ} = Cat.Reasoning (R-Mod ℓ′ R)
```

<!--
```agda
Forget-module : ∀ {ℓ ℓ′} (R : Ring ℓ) → Functor (R-Mod ℓ′ R) (Sets ℓ′)
Forget-module R .F₀ x = x .fst .fst
Forget-module R .F₁ x = x .map
Forget-module R .F-id = refl
Forget-module R .F-∘ f g = refl
```
-->

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
  open is-cartesian
```

So, given a map $f : R \to S$ and an $S$-module $N$, how do we find a
universal $R$-module $X$ making the following diagram cartesian? Well,
I've already explained the answer, but our hand is essentially forced by
the definition of maps-over in `Mods`{.Agda}. Since $R$-$S$-bilinear maps
over $f : R \to S$ are defined as maps $X \to f^*(N)$, the freest choice
we can make is that which makes the identity function $R$-$S$-bilinear:
simply take $X = f^*(N)$.

~~~{.quiver}
\[\begin{tikzcd}
  {f^*(N)} && N \\
  \\
  R && S
  \arrow["f"', from=3-1, to=3-3]
  \arrow[lies over, from=1-3, to=3-3]
  \arrow[from=1-1, to=1-3]
  \arrow[lies over, from=1-1, to=3-1]
  \arrow[dr, phantom, "\lrcorner", very near start, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

```agda
  mods : Cartesian-fibration (Mods ℓ ℓ′)
  mods .has-lift f N = the-lift where
    the-lift : Cartesian-lift (Mods ℓ ℓ′) f N
    the-lift .x′ = N .fst , Scalar-restriction f (N .snd)
    the-lift .lifting .map x = x
    the-lift .lifting .linear r m s n = refl
    the-lift .cartesian .universal m h′ .map = h′ .map
    the-lift .cartesian .universal m h′ .linear = h′ .linear
    the-lift .cartesian .commutes {u′ = u′} m h′ =
      Linear-map-path refl
    the-lift .cartesian .unique {u′ = u′} {m} m′ p =
      Linear-map-path (ap map p)
```

It is straightforward to calculate that this choice indeed furnishes a
Cartesian lift of $f$.

## Representable modules

Analogously to how groups act on themselves (Cayley's theorem) and how
precategories act on themselves (the Yoneda lemma), rings _also_ act on
themselves to give a notion of _representable modules_. $R$ can be
regarded as an $R$-module with underlying group given by $R$'s additive
group, and with multiplication exactly $R$'s multiplication.

```agda
representable-module : ∀ {ℓ} (R : Ring ℓ) → Module ℓ R
representable-module R = _ , mod where
  open Module-on hiding (module R ; module G)
  module R = Ring-on (R .snd)
  mod : Module-on R (R .fst , record { has-is-ab = R.+-group })
  mod ._⋆_ = R._*_
  mod .⋆-id x = R.*-idl
  mod .⋆-add-r r x y = R.*-distribl
  mod .⋆-add-l r s x = R.*-distribr
  mod .⋆-assoc r s x = R.*-associative
```

The construction of representable modules extends from a functor from
the category of rings to the (big) category of modules --- the total
space of the fibration of modules.

```agda
Representable-modules : ∀ {ℓ} → Functor (Rings ℓ) (∫ (Mods ℓ ℓ))
Representable-modules .F₀ R = R , representable-module R
Representable-modules .F₁ {x} {y} f = total-hom f $ record
  { map    = f #_
  ; linear = λ r m s n →
      f .preserves .pres-+ _ _
    ∙ ap₂ (y .snd .Ring-on._+_)
        (f .preserves .pres-* r m) (f .preserves .pres-* s n)
  }
Representable-modules .F-id {x} = total-hom-path _ refl $
  Linear-map-path refl
Representable-modules .F-∘ {x} {y} {z} f g = total-hom-path _ refl $
  Linear-map-path refl
```

# As actions

Another presentation of modules, which might make more sense to some, is
the following: In the same way that a monoid can act on a category
(resp. a group can act on a groupoid), a ring can act on a _ringoid_: an
[$\Ab$-category]. And, as usual, we have an adjunction: an action of $R$
on an $\Ab$-category $\cA$ can be described either as an
$\Ab$-functor $\bf{B}(R) \to \cA$, or as a ring homomorphism $R \to
\rm{Endo}_\cA(x)$, where $x$ is the object being acted on.

[$\Ab$-category]: Cat.Abelian.Base.html#ab-enriched-categories

In the particular case where $\cA = \Ab$ is the archetypal
$\Ab$-category, these actions get a fancy name: **modules**. This is
analogous to how _monoid actions_ and _group actions_ are fancy names
for actions on the archetypal $\Sets$-category, which is $\Sets$ itself.

```agda
module _ {ℓ} (R : Ring ℓ) where
  Module→Action : ∀ G (M : Module-on R G) → Rings.Hom R (Endo Ab-ab-category G)
  Module→Action G M = rh where
    module M = Module-on M
    rh : Rings.Hom R (Endo Ab-ab-category G)
    rh .hom x .hom g    = x M.⋆ g
    rh .preserves .pres-id    = Homomorphism-path (λ x → M.⋆-id x)
    rh .preserves .pres-+ x y = Homomorphism-path (λ x → M.⋆-add-l _ y x)
    rh .preserves .pres-* x y = Homomorphism-path (λ x → sym (M.⋆-assoc _ _ _))
    rh .hom x .preserves .is-group-hom.pres-⋆ g g′ = M.⋆-add-r x g g′

  open Module-on
  Action→Module : ∀ G → Rings.Hom R (Endo Ab-ab-category G) → Module-on R G
  Action→Module G rh ._⋆_ r g       = (rh # r) .hom g
  Action→Module G rh .⋆-id x        = rh .preserves .pres-id #ₚ x
  Action→Module G rh .⋆-add-r x y z = (rh # x) .preserves .is-group-hom.pres-⋆ y z
  Action→Module G rh .⋆-add-l x y z = rh .preserves .pres-+ x y #ₚ z
  Action→Module G rh .⋆-assoc x y z = sym $ rh .preserves .pres-* x y #ₚ z
```

This correspondence between presentations --- shuffling of data --- is
almost definitionally an equivalence, but in both cases, we need to
appeal to some extensionality principles to "get at" the data, even if
it is unchanging.

```agda
  Action≃Module : ∀ G → Module-on R G ≃ Rings.Hom R (Endo Ab-ab-category G)
  Action≃Module G = Iso→Equiv morp where
    open is-iso
    morp : Iso (Module-on R G) (Rings.Hom R (Endo Ab-ab-category G))
    morp .fst = Module→Action G
    morp .snd .inv = Action→Module G

    morp .snd .rinv x = Homomorphism-path λ x → Homomorphism-path λ y → refl
    morp .snd .linv x i ._⋆_     = x ._⋆_
    morp .snd .linv x i .⋆-id    = x .⋆-id
    morp .snd .linv x i .⋆-add-r = x .⋆-add-r
    morp .snd .linv x i .⋆-add-l = x .⋆-add-l
    morp .snd .linv x i .⋆-assoc = x .⋆-assoc
```
