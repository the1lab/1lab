```agda
{-# OPTIONS -vtactic.hlevel:10 #-}
open import 1Lab.Prelude

open import Algebra.Magma.Unital hiding (idl ; idr)
open import Algebra.Semigroup
open import Algebra.Monoid hiding (idl ; idr)
open import Algebra.Magma

open import Cat.Instances.Delooping

import Cat.Reasoning

module Algebra.Group where
```

# Groups

A **group** is a [monoid] that has inverses for every element. The
inverse for an element is [necessarily, unique]; Thus, to say that "$(G,
\star)$ is a group" is a statement about $(G, \star)$ having a certain
_property_ (namely, being a group), not _structure_ on $(G, \star)$.

Furthermore, since `group homomorphisms`{.Agda ident=Group-hom}
automatically preserve this structure, we are justified in calling this
_property_ rather than _property-like structure_.

[monoid]: Algebra.Monoid.html
[necessarily, unique]: Algebra.Monoid.html#inverses

In particular, for a binary operator to be a group operator, it has to
`be a monoid`{.Agda ident=has-is-monoid}, meaning it must have a
`unit`{.Agda}.

```agda
record is-group {ℓ} {A : Type ℓ} (_*_ : A → A → A) : Type ℓ where
  no-eta-equality
  field
    unit : A
```

There is also a map which assigns to each element $x$ its _`inverse`{.Agda
ident=inverse}_ $x^{-1}$, and this inverse must multiply with $x$ to
give the unit, both on the left and on the right:

```agda
    inverse : A → A

    has-is-monoid : is-monoid unit _*_
    inversel : {x : A} → inverse x * x ≡ unit
    inverser : {x : A} → x * inverse x ≡ unit

  open is-monoid has-is-monoid public
```

<!--
```agda
  _—_ : A → A → A
  x — y = x * inverse y

  abstract
    inv-unit : inverse unit ≡ unit
    inv-unit = monoid-inverse-unique
      has-is-monoid unit _ _ inversel (has-is-monoid .is-monoid.idl)

    inv-inv : ∀ {x} → inverse (inverse x) ≡ x
    inv-inv = monoid-inverse-unique
      has-is-monoid _ _ _ inversel inversel

    inv-comm : ∀ {x y} → inverse (x * y) ≡ inverse y — x
    inv-comm {x = x} {y} =
      monoid-inverse-unique has-is-monoid _ _ _ inversel p
      where
        p : (x * y) * (inverse y — x) ≡ unit
        p = associative has-is-monoid
         ·· ap₂ _*_
              (  sym (associative has-is-monoid)
              ·· ap₂ _*_ refl inverser
              ·· has-is-monoid .is-monoid.idr)
              refl
         ·· inverser

    zero-diff : ∀ {x y} → x — y ≡ unit → x ≡ y
    zero-diff {x = x} {y = y} p =
      monoid-inverse-unique has-is-monoid _ _ _ p inversel

  underlying-monoid : Monoid ℓ
  underlying-monoid = A , record
    { identity = unit ; _⋆_ = _*_ ; has-is-monoid = has-is-monoid }

  open Cat.Reasoning (B (underlying-monoid .snd))
    hiding (id ; assoc ; idl ; idr ; invr ; invl ; to ; from ; inverses ; _∘_)
    public
```
-->

## is-group is propositional

Showing that `is-group`{.Agda} takes values in propositions is
straightforward, but, fortunately, very easy to automate: Our automation
takes care of all the propositional components, and we've already
established that units and inverses (thus inverse-assigning maps) are
unique in a monoid.

```agda
private unquoteDecl eqv = declare-record-iso eqv (quote is-group)

is-group-is-prop : ∀ {ℓ} {A : Type ℓ} {_*_ : A → A → A}
                 → is-prop (is-group _*_)
is-group-is-prop {A = A} x y = Equiv.injective (Iso→Equiv eqv) $
     1x=1y
  ,ₚ funext (λ a →
      monoid-inverse-unique x.has-is-monoid a _ _
        x.inversel
        (y.inverser ∙ sym 1x=1y))
  ,ₚ prop!
  where
    module x = is-group x
    module y = is-group y hiding (magma-hlevel ; module HLevel-instance)
    A-hl : ∀ {n} → H-Level A (2 + n)
    A-hl = basic-instance {T = A} 2 (x .is-group.has-is-set)
    1x=1y = identities-equal _ _
      (is-monoid→is-unital-magma x.has-is-monoid)
      (is-monoid→is-unital-magma y.has-is-monoid)

instance
  H-Level-is-group
    : ∀ {ℓ} {G : Type ℓ} {_+_ : G → G → G} {n}
    → H-Level (is-group _+_) (suc n)
  H-Level-is-group = prop-instance is-group-is-prop
```

# Group Homomorphisms

In contrast with monoid homomorphisms, for group homomorphisms, it is
not necessary for the underlying map to explicitly preserve the unit
(and the inverses); It is sufficient for the map to preserve the
multiplication.

As a stepping stone, we define what it means to equip a type with a
group structure: a `group structure on`{.Agda ident=Group-on} a type.

```agda
record Group-on {ℓ} (A : Type ℓ) : Type ℓ where
  field
    _⋆_ : A → A → A
    has-is-group : is-group _⋆_

  infixr 20 _⋆_
  infixl 30 _⁻¹

  _⁻¹ : A → A
  x ⁻¹ = has-is-group .is-group.inverse x

  open is-group has-is-group public
```

We have that a map `is a group homomorphism`{.Agda ident=Group-hom} if
it `preserves the multiplication`{.Agda ident=pres-⋆}.

```agda
record
  Group-hom
    {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′}
    (G : Group-on A) (G′ : Group-on B) (e : A → B) : Type (ℓ ⊔ ℓ′) where
  private
    module A = Group-on G
    module B = Group-on G′

  field
    pres-⋆ : (x y : A) → e (x A.⋆ y) ≡ e x B.⋆ e y
```

A tedious calculation shows that this is sufficient to preserve the
identity:

```agda
  private
    1A = A.unit
    1B = B.unit

  pres-id : e 1A ≡ 1B
  pres-id =
    e 1A                       ≡⟨ sym B.idr ⟩
    e 1A B.⋆ ⌜ 1B ⌝            ≡˘⟨ ap¡ B.inverser ⟩
    e 1A B.⋆ (e 1A B.— e 1A)   ≡⟨ B.associative ⟩
    ⌜ e 1A B.⋆ e 1A ⌝ B.— e 1A ≡⟨ ap! (sym (pres-⋆ _ _) ∙ ap e A.idl) ⟩
    e 1A B.— e 1A              ≡⟨ B.inverser ⟩
    1B                         ∎

  pres-inv : ∀ {x} → e (A.inverse x) ≡ B.inverse (e x)
  pres-inv {x} =
    monoid-inverse-unique B.has-is-monoid (e x) _ _
      (sym (pres-⋆ _ _) ·· ap e A.inversel ·· pres-id)
      B.inverser

  pres-diff : ∀ {x y} → e (x A.— y) ≡ e x B.— e y
  pres-diff {x} {y} =
    e (x A.— y)                 ≡⟨ pres-⋆ _ _ ⟩
    e x B.⋆ ⌜ e (A.inverse y) ⌝ ≡⟨ ap! pres-inv ⟩
    e x B.— e y                 ∎
```

<!--
```agda
Group-hom-is-prop
  : ∀ {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′}
      {G : Group-on A} {H : Group-on B} {f}
  → is-prop (Group-hom G H f)
Group-hom-is-prop {H = H} a b i .Group-hom.pres-⋆ x y =
  Group-on.has-is-set H _ _ (a .Group-hom.pres-⋆ x y) (b .Group-hom.pres-⋆ x y) i

instance
  H-Level-group-hom
    : ∀ {n} {ℓ ℓ′} {A : Type ℓ} {B : Type ℓ′}
      {G : Group-on A} {H : Group-on B} {f}
    → H-Level (Group-hom G H f) (suc n)
  H-Level-group-hom = prop-instance Group-hom-is-prop
```
-->

An `equivalence`{.Agda ident=≃} is an equivalence of groups when its
underlying map is a group homomorphism.

```agda
Group≃
  : ∀ {ℓ} (A B : Σ (Type ℓ) Group-on) (e : A .fst ≃ B .fst) → Type ℓ
Group≃ A B (f , _) = Group-hom (A .snd) (B .snd) f

Group[_⇒_] : ∀ {ℓ} (A B : Σ (Type ℓ) Group-on) → Type ℓ
Group[ A ⇒ B ] = Σ (A .fst → B .fst) (Group-hom (A .snd) (B .snd))
```

## Making groups

Since the interface of `Group-on`{.Agda} is very deeply nested, we
introduce a helper function for arranging the data of a group into a
record.

```agda
record make-group {ℓ} (G : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    group-is-set : is-set G
    unit : G
    mul  : G → G → G
    inv  : G → G

    assoc : ∀ x y z → mul (mul x y) z ≡ mul x (mul y z)
    invl  : ∀ x → mul (inv x) x ≡ unit
    invr  : ∀ x → mul x (inv x) ≡ unit
    idl   : ∀ x → mul unit x ≡ x

  to-group-on : Group-on G
  to-group-on .Group-on._⋆_ = mul
  to-group-on .Group-on.has-is-group .is-group.unit = unit
  to-group-on .Group-on.has-is-group .is-group.inverse = inv
  to-group-on .Group-on.has-is-group .is-group.inversel = invl _
  to-group-on .Group-on.has-is-group .is-group.inverser = invr _
  to-group-on .Group-on.has-is-group .is-group.has-is-monoid .is-monoid.idl {x} = idl x
  to-group-on .Group-on.has-is-group .is-group.has-is-monoid .is-monoid.idr {x} =
    mul x ⌜ unit ⌝           ≡˘⟨ ap¡ (invl x) ⟩
    mul x (mul (inv x) x)    ≡⟨ sym (assoc _ _ _) ⟩
    mul ⌜ mul x (inv x) ⌝ x  ≡⟨ ap! (invr x) ⟩
    mul unit x               ≡⟨ idl x ⟩
    x                        ∎
  to-group-on .Group-on.has-is-group .is-group.has-is-monoid .has-is-semigroup =
    record { has-is-magma = record { has-is-set = group-is-set }
           ; associative = λ {x y z} → sym (assoc x y z)
           }

open make-group using (to-group-on) public
```

# Symmetric Groups

If $X$ is a set, then the type of all bijections $X \simeq X$ is also a
set, and it forms the carrier for a group: The _symmetric group_ on $X$.

```agda
Sym : ∀ {ℓ} (X : Set ℓ) → Group-on (∣ X ∣ ≃ ∣ X ∣)
Sym X = to-group-on group-str where
  open make-group
  group-str : make-group (∣ X ∣ ≃ ∣ X ∣)
  group-str .mul g f = f ∙e g
```

The group operation is `composition of equivalences`{.Agda ident=∙e};
The identity element is `the identity equivalence`{.Agda ident=id-equiv}.

```agda
  group-str .unit = id , id-equiv
```

This type is a set because $X \to X$ is a set (because $X$ is a set by
assumption), and `being an equivalence is a proposition`{.Agdaa
ident=is-equiv-is-prop}.

```agda
  group-str .group-is-set = hlevel!
```

The associativity and identity laws hold definitionally.

```agda
  group-str .assoc _ _ _ = Σ-prop-path is-equiv-is-prop refl
  group-str .idl _ = Σ-prop-path is-equiv-is-prop refl
```

The inverse is given by `the inverse equivalence`{.Agda ident=_e⁻¹}, and
the inverse equations hold by the fact that the inverse of an
equivalence is both a section and a retraction.

```agda
  group-str .inv = _e⁻¹
  group-str .invl (f , eqv) =
    Σ-prop-path is-equiv-is-prop (funext (equiv→unit eqv))
  group-str .invr (f , eqv) =
    Σ-prop-path is-equiv-is-prop (funext (equiv→counit eqv))
```

<!--
```agda
is-abelian-group : ∀ {ℓ} {G : Type ℓ} → Group-on G → Type ℓ
is-abelian-group {G = G} st = ∀ (x y : G) → x G.⋆ y ≡ y G.⋆ x
  where module G = Group-on st
```
-->
