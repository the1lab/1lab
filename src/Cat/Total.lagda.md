<!--
```agda
open import Cat.Instances.Elements.Properties
open import Cat.Instances.Presheaf.Colimits
open import Cat.Functor.Adjoint.Continuous
open import Cat.Functor.Adjoint.Reflective
open import Cat.Diagram.Coproduct.Copower
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Instances.Presheaf.Limits
open import Cat.Diagram.Colimit.Terminal
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.Adjoint.Colimit
open import Cat.Instances.Sets.Complete
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Hom.Coyoneda
open import Cat.Functor.Equivalence
open import Cat.Functor.Kan.Adjoint
open import Cat.Functor.Hom.Yoneda
open import Cat.Functor.Kan.Unique
open import Cat.Instances.Discrete
open import Cat.Instances.Elements
open import Cat.Instances.Functor
open import Cat.Diagram.Terminal
open import Cat.Functor.Constant
open import Cat.Diagram.Initial
open import Cat.Functor.Adjoint
open import Cat.Functor.Compose
open import Cat.Functor.Final
open import Cat.Functor.Base
open import Cat.Prelude hiding (J)

import Cat.Diagram.Colimit.Coproduct
import Cat.Functor.Reasoning
import Cat.Morphism
```
-->

```agda
module Cat.Total {o ℓ} (C : Precategory o ℓ) where
open import Cat.Functor.Hom C
```
<!--
```agda
private
  open module C = Precategory C
  variable
    o' ℓ' : Level
    E : Precategory o' ℓ'
    J : Precategory o' ℓ'
```
-->

# Total precategories {defines="total-precategory"}

A precategory is **total** if its yoneda embedding has a left adjoint.
We call this adjoint <ruby>さ<rp>(</rp><rt>sa</rt><rp>)</rp></ruby>,
a reading for 左, which means "left".

```agda
record is-total : Type (o ⊔ lsuc ℓ) where
  field
    {さ} : Functor Cat[ C ^op , Sets ℓ ] C
    has-よ-adj : さ ⊣ よ
  open module さ = Cat.Functor.Reasoning さ using () renaming (F₀ to さ₀; F₁ to さ₁) public
```

## Motivation

Total categories represent a particularly nice site in which to do
logic, as they are a reflective subcategory of their category of
presheaves. In particular, total categories are cocomplete with many
useful limits. However, a category being total is a slightly weaker
requirement than a category being a topos, as all topoi are both total
and cototal.

## Free objects relative to よ

Before we investigate the properties of a total category, it's worth
considering the action of such a functor on objects, if it exists. Given
some presheaf $F\in\psh(\cC)$, an object could be $\sa(F)$ if it is [[free|free object]]
with respect to $\yo$.

<!--
```agda
module _ (F : Functor (C ^op) (Sets ℓ)) (c : Free-object よ F) where
  open Free-object c
  private
```
-->

Since $F$ is a presheaf, it can be written as a colimit of representable
functors by the [[coyoneda lemma]].

```agda
    F-is-colimit : is-colimit (よ F∘ πₚ C F) F _
    F-is-colimit = coyoneda _ F
```

As left adjoints preserve colimits, we can imagine that a *partial* left
adjoint (a [[free object]]) of a colimit should also be a colimit.
Indeed this is true as $\yo$ is fully faithful.

We call a free object with respect to $\yo$ a **realising object** for
$F$.

```agda
  free-is-colimit : is-colimit (πₚ C F) free _
  free-is-colimit = free-object→is-colimit よ よ-is-fully-faithful (to-colimit F-is-colimit) c
```

<!--
```agda
module Total (C-total : is-total) where
  open module C-total = is-total C-total public
  open Cat.Morphism C public

  さ∘よ≅ⁿid : さ F∘ よ ≅ⁿ Id
  さ∘よ≅ⁿid = is-reflective→counit-iso has-よ-adj よ-is-fully-faithful

  private
    さ∘よ∘F≅ⁿF : ∀ {F : Functor J C} → さ F∘ よ F∘ F ≅ⁿ F
    さ∘よ∘F≅ⁿF = ni-assoc ∙ni (さ∘よ≅ⁿid ◂ni _) ∙ni path→iso F∘-idl
```
-->


## さ on values

For each $F$,  $\sa(F)$ yields a free value on $F$ relative to $\yo$. As
we have proved, this is a colimit.

```agda
  さ₀-is-colimit : (F : ⌞ PSh ℓ C ⌟) → is-colimit (πₚ C F) (さ₀ F) _
  さ₀-is-colimit F = free-is-colimit F  $ left-adjoint→free-objects has-よ-adj F
```

## Cocompleteness

Thus, all total categories are [[cocomplete]] as their colimits can be
computed in $\psh(\cC)$.

```agda
  cocomplete : is-cocomplete ℓ ℓ C
  cocomplete F = natural-iso→colimit さ∘よ∘F≅ⁿF $ left-adjoint-colimit has-よ-adj $ PSh-cocomplete ℓ C (よ F∘ F)
```

## Terminal object

Total categories also have many limits. For example, the terminal
presheaf has a realisation in $\cC$. Furthermore, the projection functor
from the category of elements of the terminal presheaf is an
equivalence. A colimit of an equivalence is equivalent to a colimit of
the identity---i.e., a terminal object.

```agda
  ★ : C.Ob
  ★ = さ.₀ (⊤PSh _ _)

  private
    ★-is-colimit-id : is-colimit (Id {C = C}) ★ _
    ★-is-colimit-id = extend-is-colimit _ (right-adjoint-is-final (elements-terminal-is-equivalence.F⁻¹⊣F {s = ℓ})) _ col'
      where
      open is-equivalence
      col : is-colimit (πₚ C $ ⊤PSh _ _) ★ _
      col = さ₀-is-colimit _
      col' : is-colimit (Id F∘ πₚ C (⊤PSh _ _)) ★ _
      col' = natural-iso-ext→is-lan (left-adjoint-is-cocontinuous (Id-is-equivalence .F⊣F⁻¹) col) (!const-isoⁿ id-iso)

  total-terminal : Terminal C
  total-terminal = Id-colimit→Terminal $ to-colimit ★-is-colimit-id
  module total-terminal = Terminal total-terminal
```

## Copowers

As `C` is cocomplete, it has all set-indexed coproducts
```agda
  open Cat.Diagram.Colimit.Coproduct C
  has-set-indexed-coproducts : (S : Set ℓ) → has-coproducts-indexed-by C ∣ S ∣
  has-set-indexed-coproducts S F = Colimit→IC F (cocomplete $ Disc-adjunct F)
```

and is thus copowered.
```agda
  open Copowers has-set-indexed-coproducts public
  open Consts total-terminal has-set-indexed-coproducts public
```
