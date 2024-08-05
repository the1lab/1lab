<!--
```agda
open import Algebra.Group.Cat.Base
open import Algebra.Group

open import Cat.Functor.Properties
open import Cat.Prelude hiding (_*_ ; _+_)

import Cat.Reasoning
```
-->

```agda
module Algebra.Group.Ab where
```

# Abelian groups {defines=abelian-group}

A very important class of [[groups]] (which includes most familiar
examples of groups: the integers, all finite cyclic groups, etc) are
those with a _commutative_ group operation, that is, those for which $xy
= yx$.  Accordingly, these have a name reflecting their importance and
ubiquity: They are called **commutative groups**. Just kidding! They're
named **abelian groups**, named after [a person], because nothing can
have self-explicative names in mathematics. It's the law.

[a person]: https://en.wikipedia.org/wiki/Niels_Henrik_Abel

<!--
```agda
private variable
  ℓ : Level
  G : Type ℓ

Group-on-is-abelian : Group-on G → Type _
Group-on-is-abelian G = ∀ x y → Group-on._⋆_ G x y ≡ Group-on._⋆_ G y x

Group-on-is-abelian-is-prop : (g : Group-on G) → is-prop (Group-on-is-abelian g)
Group-on-is-abelian-is-prop g = Π-is-hlevel² 1 λ _ _ → g .Group-on.has-is-set _ _
```
-->

This module does the usual algebraic structure dance to set up the
category $\Ab$ of Abelian groups.

```agda
record is-abelian-group (_*_ : G → G → G) : Type (level-of G) where
  no-eta-equality
  field
    has-is-group : is-group _*_
    commutes     : ∀ {x y} → x * y ≡ y * x
  open is-group has-is-group renaming (unit to 1g) public
```

<!--
```agda
  equal-sum→equal-diff : ∀ a b c d → a * b ≡ c * d → a — c ≡ d — b
  equal-sum→equal-diff a b c d p = commutes ∙ swizzle p inverser inversel
```
-->

<!--
```agda
private unquoteDecl eqv = declare-record-iso eqv (quote is-abelian-group)
instance
  H-Level-is-abelian-group
    : ∀ {n} {* : G → G → G} → H-Level (is-abelian-group *) (suc n)
  H-Level-is-abelian-group = prop-instance $ Iso→is-hlevel 1 eqv $
    Σ-is-hlevel 1 (hlevel 1) λ x → Π-is-hlevel²' 1 λ _ _ →
      is-group.has-is-set x _ _
```
-->

```agda
record Abelian-group-on (T : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    _*_       : T → T → T
    has-is-ab : is-abelian-group _*_
  open is-abelian-group has-is-ab renaming (inverse to infixl 30 _⁻¹) public
```

<!--
```agda
  Abelian→Group-on : Group-on T
  Abelian→Group-on .Group-on._⋆_ = _*_
  Abelian→Group-on .Group-on.has-is-group = has-is-group

  Abelian→Group-on-abelian : Group-on-is-abelian Abelian→Group-on
  Abelian→Group-on-abelian _ _ = commutes

  infixr 20 _*_

open Abelian-group-on using (Abelian→Group-on; Abelian→Group-on-abelian) public
```
-->

```agda
Abelian-group-structure : ∀ ℓ → Thin-structure ℓ Abelian-group-on
∣ Abelian-group-structure ℓ .is-hom f G₁ G₂ ∣ =
  is-group-hom (Abelian→Group-on G₁) (Abelian→Group-on G₂) f
Abelian-group-structure ℓ .is-hom f G₁ G₂ .is-tr = hlevel 1
Abelian-group-structure ℓ .id-is-hom .is-group-hom.pres-⋆ x y = refl
Abelian-group-structure ℓ .∘-is-hom f g α β .is-group-hom.pres-⋆ x y =
  ap f (β .is-group-hom.pres-⋆ x y) ∙ α .is-group-hom.pres-⋆ (g x) (g y)
Abelian-group-structure ℓ .id-hom-unique {s = s} {t} α _ = p where
  open Abelian-group-on

  p : s ≡ t
  p i ._*_ x y = α .is-group-hom.pres-⋆ x y i
  p i .has-is-ab = is-prop→pathp
    (λ i → hlevel {T = is-abelian-group (λ x y → p i ._*_ x y)} 1)
    (s .has-is-ab) (t .has-is-ab) i

Ab : ∀ ℓ → Precategory (lsuc ℓ) ℓ
Ab ℓ = Structured-objects (Abelian-group-structure ℓ)

module Ab {ℓ} = Cat.Reasoning (Ab ℓ)

instance
  Ab-equational : ∀ {ℓ} → is-equational (Abelian-group-structure ℓ)
  Ab-equational .is-equational.invert-id-hom = Groups-equational .is-equational.invert-id-hom
```

<!--
```agda
Abelian-group : (ℓ : Level) → Type (lsuc ℓ)
Abelian-group _ = Ab.Ob

Abelian→Group : ∀ {ℓ} → Abelian-group ℓ → Group ℓ
Abelian→Group G = G .fst , Abelian→Group-on (G .snd)

record make-abelian-group (T : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    ab-is-set : is-set T
    mul   : T → T → T
    inv   : T → T
    1g    : T
    idl   : ∀ x → mul 1g x ≡ x
    assoc : ∀ x y z → mul x (mul y z) ≡ mul (mul x y) z
    invl  : ∀ x → mul (inv x) x ≡ 1g
    comm  : ∀ x y → mul x y ≡ mul y x

  make-abelian-group→make-group : make-group T
  make-abelian-group→make-group = mg where
    mg : make-group T
    mg .make-group.group-is-set = ab-is-set
    mg .make-group.unit   = 1g
    mg .make-group.mul    = mul
    mg .make-group.inv    = inv
    mg .make-group.assoc  = assoc
    mg .make-group.invl   = invl
    mg .make-group.idl    = idl

  to-group-on-ab : Group-on T
  to-group-on-ab = to-group-on make-abelian-group→make-group

  to-abelian-group-on : Abelian-group-on T
  to-abelian-group-on .Abelian-group-on._*_ = mul
  to-abelian-group-on .Abelian-group-on.has-is-ab .is-abelian-group.has-is-group =
    Group-on.has-is-group to-group-on-ab
  to-abelian-group-on .Abelian-group-on.has-is-ab .is-abelian-group.commutes =
    comm _ _

  to-ab : Abelian-group ℓ
  ∣ to-ab .fst ∣ = T
  to-ab .fst .is-tr = ab-is-set
  to-ab .snd = to-abelian-group-on

is-commutative-group : ∀ {ℓ} → Group ℓ → Type ℓ
is-commutative-group G = Group-on-is-abelian (G .snd)

from-commutative-group
  : ∀ {ℓ} (G : Group ℓ)
  → is-commutative-group G
  → Abelian-group ℓ
from-commutative-group G comm .fst = G .fst
from-commutative-group G comm .snd .Abelian-group-on._*_ =
  Group-on._⋆_ (G .snd)
from-commutative-group G comm .snd .Abelian-group-on.has-is-ab .is-abelian-group.has-is-group =
  Group-on.has-is-group (G .snd)
from-commutative-group G comm .snd .Abelian-group-on.has-is-ab .is-abelian-group.commutes =
  comm _ _

Grp→Ab→Grp
  : ∀ {ℓ} (G : Group ℓ) (c : is-commutative-group G)
  → Abelian→Group (from-commutative-group G c) ≡ G
Grp→Ab→Grp G c = Σ-pathp refl go where
  go : Abelian→Group-on (from-commutative-group G c .snd) ≡ G .snd
  go i .Group-on._⋆_ = G .snd .Group-on._⋆_
  go i .Group-on.has-is-group = G .snd .Group-on.has-is-group

open make-abelian-group using (make-abelian-group→make-group ; to-group-on-ab ; to-abelian-group-on ; to-ab) public

open Functor

Ab↪Grp : ∀ {ℓ} → Functor (Ab ℓ) (Groups ℓ)
Ab↪Grp .F₀ = Abelian→Group
Ab↪Grp .F₁ f .hom = f .hom
Ab↪Grp .F₁ f .preserves = f .preserves
Ab↪Grp .F-id = trivial!
Ab↪Grp .F-∘ f g = trivial!

Ab↪Grp-is-ff : ∀ {ℓ} → is-fully-faithful (Ab↪Grp {ℓ})
Ab↪Grp-is-ff {x = A} {B} = is-iso→is-equiv $ iso
  promote (λ _ → trivial!) (λ _ → trivial!)
  where
    promote : Groups.Hom (Abelian→Group A) (Abelian→Group B) → Ab.Hom A B
    promote f .hom = f .hom
    promote f .preserves = f .preserves

Ab↪Sets : ∀ {ℓ} → Functor (Ab ℓ) (Sets ℓ)
Ab↪Sets = Grp↪Sets F∘ Ab↪Grp
```
-->

The fundamental example of an abelian group is the [[group of integers]].
