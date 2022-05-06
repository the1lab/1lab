```agda
open import 1Lab.Prelude

open import Algebra.Magma.Unital
open import Algebra.Semigroup
open import Algebra.Monoid
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
    has-is-monoid : is-monoid unit _*_
```

There is also a map which assigns to each element $x$ its _`inverse`{.Agda
ident=inverse}_ $x^{-1}$, and this inverse must multiply with $x$ to
give the unit, both on the left and on the right:

```agda
    inverse : A → A

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
      has-is-monoid unit _ _ inversel (idl has-is-monoid)

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
              ·· idr has-is-monoid)
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

open is-group
```
-->

## is-group is propositional

Showing that `is-group`{.Agda} takes values in propositions is
straightforward, but tedious. Suppose that $x, y$ are both witnesses of
`is-group`{.Agda} for the same operator; We'll build a path $x = y$.

```agda
is-group-is-prop : ∀ {ℓ} {A : Type ℓ} {_*_ : A → A → A}
                 → is-prop (is-group _*_)
is-group-is-prop {A = A} {_*_ = _*_} x y = path where
```

We begin by constructing a line showing that the `underlying monoid
structures`{.Agda ident=has-is-monoid} are identical -- but since these
have different _types_, we must also show that `the units are the
same`{.Agda ident=same-unit}.

```agda
  same-unit : x .unit ≡ y .unit
  same-unit =
    identities-equal (x .unit) (y .unit)
      (is-monoid→is-unital-magma (x .has-is-monoid))
      (is-monoid→is-unital-magma (y .has-is-monoid))
```

We then use the fact that `is-monoid is a proposition`{.Agda
ident=is-monoid-is-prop} to conclude that the monoid structures underlying
$x$ and $y$ are the same.

```agda
  same-monoid : PathP (λ i → is-monoid (same-unit i) _*_)
                      (x .has-is-monoid) (y .has-is-monoid)
  same-monoid =
    is-prop→pathp (λ i → hlevel {T = is-monoid (same-unit i) _*_} 1)
      (x .has-is-monoid) (y .has-is-monoid)
```

Since `inverses in monoids are unique`{.Agda ident=monoid-inverse-unique}
(when they exist), it follows that `the inverse-assigning maps`{.Agda
ident=inverse} are pointwise equal; By extensionality, they are the same
map.

```agda
  same-inverses : (e : A) → x .inverse e ≡ y .inverse e
  same-inverses e =
    monoid-inverse-unique (y .has-is-monoid) _ _ _
      (x .inversel ∙ same-unit) (y .inverser)
```

Since the underlying type of a group `is a set`{.Agda ident=has-is-set},
we have that any parallel paths are equal - even when the paths are
dependent! This gives us the equations between the `inversel`{.Agda} and
`inverser`{.Agda} fields of `x` and `y`.

```agda
  same-invl : (e : A) → Square _ _ _ _
  same-invl e =
    is-set→squarep (λ _ _ → x .has-is-monoid .has-is-set)
      (ap₂ _*_ (same-inverses e) refl) (x .inversel) (y .inversel) same-unit

  same-invr : (e : A) → Square _ _ _ _
  same-invr e =
    is-set→squarep (λ _ _ → x .has-is-monoid .has-is-set)
      (ap₂ _*_ refl (same-inverses e)) (x .inverser) (y .inverser) same-unit
```

Putting all of this together lets us conclude that `x` and `y` are
identical.

```agda
  path : x ≡ y
  path i .unit         = same-unit i
  path i .has-is-monoid  = same-monoid i
  path i .inverse e    = same-inverses e i
  path i .inversel {e} = same-invl e i
  path i .inverser {e} = same-invr e i

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
  x ⁻¹ = inverse has-is-group x

  open is-group has-is-group public

open Group-on

Group : (ℓ : Level) → Type (lsuc ℓ)
Group ℓ = Σ Group-on
```

We have that a map `is a group homomorphism`{.Agda ident=Group-hom} if
it `preserves the multiplication`{.Agda ident=pres-⋆}.

```agda
record
  Group-hom {ℓ} (A B : Group ℓ) (e : A .fst → B .fst) : Type ℓ where
  private
    module A = Group-on (A .snd)
    module B = Group-on (B .snd)

  field
    pres-⋆ : (x y : A .fst) → e (x A.⋆ y) ≡ e x B.⋆ e y
```

A tedious calculation shows that this is sufficient to preserve the
identity:

```agda
  private
    1A = A.unit
    1B = B.unit

  pres-id : e 1A ≡ 1B
  pres-id =
    e 1A                     ≡⟨ sym B.idr ⟩
    e 1A B.⋆ 1B              ≡⟨ ap₂ B._⋆_ refl (sym B.inverser) ⟩
    e 1A B.⋆ (e 1A B.— e 1A) ≡⟨ B.associative ⟩
    (e 1A B.⋆ e 1A) B.— e 1A ≡⟨ ap₂ B._⋆_ (sym (pres-⋆ _ _) ∙ ap e A.idl) refl ⟩
    e 1A B.— e 1A            ≡⟨ B.inverser ⟩
    1B                       ∎

  pres-inv : ∀ {x} → e (A.inverse x) ≡ B.inverse (e x)
  pres-inv {x} =
    monoid-inverse-unique B.has-is-monoid (e x) _ _
      (sym (pres-⋆ _ _) ·· ap e A.inversel ·· pres-id)
      B.inverser

  pres-diff : ∀ {x y} → e (x A.— y) ≡ e x B.— e y
  pres-diff {x} {y} =
    e (x A.— y)             ≡⟨ pres-⋆ _ _ ⟩
    e x B.⋆ e (A.inverse y) ≡⟨ ap (_ B.⋆_) pres-inv ⟩
    e x B.— e y             ∎
```

<!--
```agda
Group-hom-is-prop : ∀ {ℓ} {G H : Group ℓ} {f} → is-prop (Group-hom G H f)
Group-hom-is-prop {H = _ , H} a b i .Group-hom.pres-⋆ x y =
  Group-on.has-is-set H _ _ (a .Group-hom.pres-⋆ x y) (b .Group-hom.pres-⋆ x y) i

instance
  H-Level-group-hom : ∀ {n} {ℓ} {G H : Group ℓ} {f}
                    → H-Level (Group-hom G H f) (suc n)
  H-Level-group-hom = prop-instance Group-hom-is-prop
```
-->

An `equivalence`{.Agda ident=_≃_} is an equivalence of groups when its
underlying map is a group homomorphism.

```agda
Group≃ : ∀ {ℓ} (A B : Group ℓ) (e : A .fst ≃ B .fst) → Type ℓ
Group≃ A B (f , _) = Group-hom A B f

Group[_⇒_] : ∀ {ℓ} (A B : Group ℓ) → Type ℓ
Group[ A ⇒ B ] = Σ (Group-hom A B)

open Group-hom
```

We automatically derive the proof that paths between groups are
homomorphic equivalences:

```agda
Group-univalent : ∀ {ℓ} → is-univalent {ℓ = ℓ} (HomT→Str Group≃)
Group-univalent {ℓ = ℓ} =
  Derive-univalent-record (record-desc
    (Group-on {ℓ = ℓ}) Group≃
    (record:
      field[ _⋆_         by pres-⋆ ]
      axiom[ has-is-group by (λ _ → is-group-is-prop) ]))
```

## Making groups

Since the interface of `Group-on`{.Agda} is very deeply nested, we
introduce a helper function for arranging the data of a group into a
record.

```agda
make-group
  : ∀ {ℓ} {G : Type ℓ}
  → is-set G
  → (unit : G) (_⋆_ : G → G → G) (inv : G → G)
  → (∀ x y z → (x ⋆ y) ⋆ z ≡ x ⋆ (y ⋆ z))
  → (∀ x → inv x ⋆ x ≡ unit) → (∀ x → x ⋆ inv x ≡ unit)
  → (∀ x → unit ⋆ x ≡ x)
  → Group-on G
make-group gset id star inv assoc invl invr g-idl = r where
  open is-group

  r : Group-on _
  r ._⋆_ = star
  r .has-is-group .unit = id
  r .has-is-group .has-is-monoid .has-is-semigroup .has-is-magma .has-is-set = gset
  r .has-is-group .has-is-monoid .has-is-semigroup .associative = sym (assoc _ _ _)
  r .has-is-group .has-is-monoid .idl = g-idl _
  r .has-is-group .has-is-monoid .idr {x = x} =
    star x id               ≡⟨ ap₂ star refl (sym (invl x)) ⟩
    star x (star (inv x) x) ≡⟨ sym (assoc _ _ _) ⟩
    star (star x (inv x)) x ≡⟨ ap₂ star (invr x) refl ⟩
    star id x               ≡⟨ g-idl x ⟩
    x                       ∎
  r .has-is-group .inverse = inv
  r .has-is-group .inversel = invl _
  r .has-is-group .inverser = invr _
```

# Symmetric Groups

If $X$ is a set, then the type of all bijections $X \simeq X$ is also a
set, and it forms the carrier for a group: The _symmetric group_ on $X$.

```agda
Sym : ∀ {ℓ} → Set ℓ → Group ℓ
Sym X .fst = ∣ X ∣ ≃ ∣ X ∣
Sym X .snd = group-str where
  open n-Type X using (H-Level-n-type)
  group-str : Group-on (∣ X ∣ ≃ ∣ X ∣)
  group-str ._⋆_ g f = f ∙e g
```

The group operation is `composition of equivalences`{.Agda ident=_∙e_};
The identity element is `the identity equivalence`{.Agda ident=id-equiv}.

```agda
  group-str .has-is-group .unit = id , id-equiv
```

This type is a set because $X \to X$ is a set (because $X$ is a set by
assumption), and `being an equivalence is a proposition`{.Agdaa
ident=is-equiv-is-prop}.

```agda
  group-str .has-is-group .has-is-monoid .has-is-semigroup .has-is-magma .has-is-set =
    hlevel 2
```

The associativity and identity laws hold definitionally.

```agda
  group-str .has-is-group .has-is-monoid .has-is-semigroup .associative =
    Σ-prop-path is-equiv-is-prop refl
  group-str .has-is-group .has-is-monoid .idl = Σ-prop-path is-equiv-is-prop refl
  group-str .has-is-group .has-is-monoid .idr = Σ-prop-path is-equiv-is-prop refl
```

The inverse is given by `the inverse equivalence`{.Agda ident=_e⁻¹}, and
the inverse equations hold by the fact that the inverse of an
equivalence is both a section and a retraction.

```agda
  group-str .has-is-group .inverse = _e⁻¹
  group-str .has-is-group .inversel {x = f , eqv} =
    Σ-prop-path is-equiv-is-prop (funext (equiv→retraction eqv))
  group-str .has-is-group .inverser {x = f , eqv} =
    Σ-prop-path is-equiv-is-prop (funext (equiv→section eqv))
```

<!--
```agda
is-abelian-group : ∀ {ℓ} (G : Group ℓ) → Type ℓ
is-abelian-group (G , st) = ∀ (x y : G) → x G.⋆ y ≡ y G.⋆ x
  where module G = Group-on st
```
-->
