<!--
```agda
{-# OPTIONS -vtactic.hlevel:10 #-}
open import 1Lab.Prelude

open import Algebra.Magma.Unital hiding (idl ; idr)
open import Algebra.Semigroup
open import Algebra.Monoid hiding (idl ; idr)
open import Algebra.Magma

open import Cat.Instances.Delooping

import Cat.Reasoning
```
-->

```agda
module Algebra.Group where
```

# Groups {defines=group}

A **group** is a [monoid] that has inverses for every element. The
inverse for an element is, [necessarily, unique]; thus, to say that "$(G,
\star)$ is a group" is a statement about $(G, \star)$ having a certain
_property_ (namely, being a group), not _structure_ on $(G, \star)$.

Furthermore, since [[group homomorphisms]]
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
ident=inverse}_ $x\inv$, and this inverse must multiply with $x$ to
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
  infixr 20 _—_
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

Note that any element $x$ of $G$ determines two
bijections on the underlying set of $G$, by multiplication with $x$ on
the left and on the right.
The inverse of this bijection is given by multiplication with
$x\inv$, and the proof that these are in fact inverse functions are
given by the group laws:

```agda
  ⋆-equivl : ∀ x → is-equiv (x *_)
  ⋆-equivl x = is-iso→is-equiv (iso (inverse x *_)
    (λ _ → cancell inverser) λ _ → cancell inversel)

  ⋆-equivr : ∀ y → is-equiv (_* y)
  ⋆-equivr y = is-iso→is-equiv (iso (_* inverse y)
    (λ _ → cancelr inversel) λ _ → cancelr inverser)
```

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
is-group-is-prop {A = A} x y = Iso.injective eqv $
     1x=1y
  ,ₚ funext (λ a →
      monoid-inverse-unique x.has-is-monoid a _ _
        x.inversel
        (y.inverser ∙ sym 1x=1y))
  ,ₚ prop!
  where
    module x = is-group x
    module y = is-group y hiding (magma-hlevel)
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

# Group homomorphisms {defines="group-homomorphism"}

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
  infixl 35 _⁻¹

  _⁻¹ : A → A
  x ⁻¹ = has-is-group .is-group.inverse x

  open is-group has-is-group public
```

We have that a map `is a group homomorphism`{.Agda ident=is-group-hom} if
it `preserves the multiplication`{.Agda ident=pres-⋆}.

```agda
record
  is-group-hom
    {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
    (G : Group-on A) (G' : Group-on B) (e : A → B) : Type (ℓ ⊔ ℓ') where
  private
    module A = Group-on G
    module B = Group-on G'

  field
    pres-⋆ : (x y : A) → e (x A.⋆ y) ≡ e x B.⋆ e y
```

A tedious calculation shows that this is sufficient to preserve the
identity and inverses:

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
is-group-hom-is-prop
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
      {G : Group-on A} {H : Group-on B} {f}
  → is-prop (is-group-hom G H f)
is-group-hom-is-prop {H = H} a b i .is-group-hom.pres-⋆ x y =
  Group-on.has-is-set H _ _ (a .is-group-hom.pres-⋆ x y) (b .is-group-hom.pres-⋆ x y) i

instance
  H-Level-group-hom
    : ∀ {n} {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
      {G : Group-on A} {H : Group-on B} {f}
    → H-Level (is-group-hom G H f) (suc n)
  H-Level-group-hom = prop-instance is-group-hom-is-prop
```
-->

An `equivalence`{.Agda ident=≃} is an equivalence of groups when its
underlying map is a group homomorphism.

```agda
Group≃
  : ∀ {ℓ} (A B : Σ (Type ℓ) Group-on) (e : A .fst ≃ B .fst) → Type ℓ
Group≃ A B (f , _) = is-group-hom (A .snd) (B .snd) f

Group[_⇒_] : ∀ {ℓ} (A B : Σ (Type ℓ) Group-on) → Type ℓ
Group[ A ⇒ B ] = Σ (A .fst → B .fst) (is-group-hom (A .snd) (B .snd))
```

# Making groups

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

    assoc : ∀ x y z → mul x (mul y z) ≡ mul (mul x y) z
    invl  : ∀ x → mul (inv x) x ≡ unit
    idl   : ∀ x → mul unit x ≡ x

  private
    inverser : ∀ x → mul x (inv x) ≡ unit
    inverser x =
      mul x (inv x)                                   ≡˘⟨ idl _ ⟩
      mul unit (mul x (inv x))                        ≡˘⟨ ap₂ mul (invl _) refl ⟩
      mul (mul (inv (inv x)) (inv x)) (mul x (inv x)) ≡˘⟨ assoc _ _ _ ⟩
      mul (inv (inv x)) (mul (inv x) (mul x (inv x))) ≡⟨ ap₂ mul refl (assoc _ _ _) ⟩
      mul (inv (inv x)) (mul (mul (inv x) x) (inv x)) ≡⟨ ap₂ mul refl (ap₂ mul (invl _) refl) ⟩
      mul (inv (inv x)) (mul unit (inv x))            ≡⟨ ap₂ mul refl (idl _) ⟩
      mul (inv (inv x)) (inv x)                       ≡⟨ invl _ ⟩
      unit                                            ∎

  to-group-on : Group-on G
  to-group-on .Group-on._⋆_ = mul
  to-group-on .Group-on.has-is-group .is-group.unit = unit
  to-group-on .Group-on.has-is-group .is-group.inverse = inv
  to-group-on .Group-on.has-is-group .is-group.inversel = invl _
  to-group-on .Group-on.has-is-group .is-group.inverser = inverser _
  to-group-on .Group-on.has-is-group .is-group.has-is-monoid .is-monoid.idl {x} = idl x
  to-group-on .Group-on.has-is-group .is-group.has-is-monoid .is-monoid.idr {x} =
    mul x ⌜ unit ⌝           ≡˘⟨ ap¡ (invl x) ⟩
    mul x (mul (inv x) x)    ≡⟨ assoc _ _ _ ⟩
    mul ⌜ mul x (inv x) ⌝ x  ≡⟨ ap! (inverser x) ⟩
    mul unit x               ≡⟨ idl x ⟩
    x                        ∎
  to-group-on .Group-on.has-is-group .is-group.has-is-monoid .has-is-semigroup =
    record { has-is-magma = record { has-is-set = group-is-set }
           ; associative = λ {x y z} → assoc x y z
           }

open make-group using (to-group-on) public
```
