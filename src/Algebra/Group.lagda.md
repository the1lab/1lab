```agda
open import 1Lab.Prelude

open import Algebra.Magma.Unital
open import Algebra.Semigroup
open import Algebra.Monoid
open import Algebra.Magma

module Algebra.Group where
```

# Groups

A **group** is a [monoid] that has inverses for every element. The
inverse for an element is [necessarily, unique]; Thus, to say that "$(G,
\star)$ is a group" is a statement about $(G, \star)$ having a certain
_property_ (namely, being a group), not _structure_ on $(G, \star)$.

Furthermore, since `group homomorphisms`{.Agda ident=isGroupHom}
automatically preserve this structure, we are justified in calling this
_property_ rather than _property-like structure_.

[monoid]: Algebra.Monoid.html
[necessarily, unique]: Algebra.Monoid.html#inverses

In particular, for a binary operator to be a group operator, it has to
`be a monoid`{.Agda ident=hasIsMonoid}, meaning it must have a
`unit`{.Agda}.

```agda
record isGroup {ℓ} {A : Type ℓ} (_*_ : A → A → A) : Type ℓ where
  field
    unit : A
    hasIsMonoid : isMonoid unit _*_
```

There is also a map which assigns to each element $x$ its _`inverse`{.Agda
ident=inverse}_ $x^{-1}$, and this inverse must multiply with $x$ to
give the unit, both on the left and on the right:

```agda
    inverse : A → A

    inverseˡ : {x : A} → inverse x * x ≡ unit
    inverseʳ : {x : A} → x * inverse x ≡ unit

  open isMonoid hasIsMonoid public

  abstract
    inv-unit≡unit : inverse unit ≡ unit
    inv-unit≡unit = monoid-inverse-unique 
      hasIsMonoid unit _ _ inverseˡ (idˡ hasIsMonoid)

    inv-inv : ∀ {x} → inverse (inverse x) ≡ x
    inv-inv = monoid-inverse-unique
      hasIsMonoid _ _ _ inverseˡ inverseˡ

    inv-comm : ∀ {x y} → inverse (x * y) ≡ inverse y * inverse x
    inv-comm {x = x} {y} = 
      monoid-inverse-unique hasIsMonoid _ _ _ inverseˡ p
      where
        p : (x * y) * (inverse y * inverse x) ≡ unit
        p = associative hasIsMonoid 
         ·· ap₂ _*_ 
              (  sym (associative hasIsMonoid) 
              ·· ap₂ _*_ refl inverseʳ 
              ·· idʳ hasIsMonoid) 
              refl 
         ·· inverseʳ

    zero-diff→≡ : ∀ {x y} → x * inverse y ≡ unit → x ≡ y
    zero-diff→≡ {x = x} {y = y} p =
      monoid-inverse-unique hasIsMonoid _ _ _ p inverseˡ

open isGroup
```

## isGroup is propositional

Showing that `isGroup`{.Agda} takes values in propositions is
straightforward, but tedious. Suppose that $x, y$ are both witnesses of
`isGroup`{.Agda} for the same operator; We'll build a path $x = y$.

```agda
isProp-isGroup : ∀ {ℓ} {A : Type ℓ} {_*_ : A → A → A}
               → isProp (isGroup _*_)
isProp-isGroup {A = A} {_*_ = _*_} x y = path where
```

We begin by constructing a line showing that the `underlying monoid
structures`{.Agda ident=hasIsMonoid are identical -- but since these
have different _types_, we must also show that `the units are the
same`{.Agda ident=same-unit}.

```agda
  same-unit : x .unit ≡ y .unit
  same-unit =
    identities-equal (x .unit) (y .unit)
      (isMonoid→isUnitalMagma (x .hasIsMonoid))
      (isMonoid→isUnitalMagma (y .hasIsMonoid))
```

We then use the fact that `isMonoid is a proposition`{.Agda
ident=isProp-isMonoid} to conclude that the monoid structures underlying
$x$ and $y$ are the same.

```agda
  same-monoid : PathP (λ i → isMonoid (same-unit i) _*_)
                      (x .hasIsMonoid) (y .hasIsMonoid)
  same-monoid = 
    isProp→PathP (λ i → isProp-isMonoid {id = same-unit i})
      (x .hasIsMonoid) (y .hasIsMonoid)
```

Since `inverses in monoids are unique`{.Agda ident=monoid-inverse-unique} 
(when they exist), it follows that `the inverse-assigning maps`{.Agda
ident=inverse} are pointwise equal; By extensionality, they are the same
map.

```agda
  same-inverses : (e : A) → x .inverse e ≡ y .inverse e
  same-inverses e =
    monoid-inverse-unique (y .hasIsMonoid) _ _ _
      (x .inverseˡ ∙ same-unit) (y .inverseʳ)
```

Since the underlying type of a group `is a set`{.Agda ident=hasIsSet},
we have that any parallel paths are equal - even when the paths are
dependent! This gives us the equations between the `inverseˡ`{.Agda} and
`inverseʳ`{.Agda} fields of `x` and `y`.

```agda
  same-invˡ : (e : A) → Square _ _ _ _
  same-invˡ e =
    isSet→SquareP (λ _ _ → x .hasIsMonoid .hasIsSet)
      (ap₂ _*_ (same-inverses e) refl) (x .inverseˡ) (y .inverseˡ) same-unit 

  same-invʳ : (e : A) → Square _ _ _ _
  same-invʳ e =
    isSet→SquareP (λ _ _ → x .hasIsMonoid .hasIsSet)
      (ap₂ _*_ refl (same-inverses e)) (x .inverseʳ) (y .inverseʳ) same-unit 
```

Putting all of this together lets us conclude that `x` and `y` are
identical.

```agda
  path : x ≡ y
  path i .unit         = same-unit i
  path i .hasIsMonoid  = same-monoid i
  path i .inverse e    = same-inverses e i
  path i .inverseˡ {e} = same-invˡ e i
  path i .inverseʳ {e} = same-invʳ e i
```

# Group Homomorphisms

In contrast with monoid homomorphisms, for group homomorphisms, it is
not necessary for the underlying map to explicitly preserve the unit
(and the inverses); It is sufficient for the map to preserve the
multiplication.

As a stepping stone, we define what it means to equip a type with a
group structure: a `group structure on`{.Agda ident=GroupOn} a type.

```agda
record GroupOn {ℓ} (A : Type ℓ) : Type ℓ where
  field
    _⋆_ : A → A → A
    hasIsGroup : isGroup _⋆_

  infixr 20 _⋆_
  infixl 30 _⁻¹

  _⁻¹ : A → A
  x ⁻¹ = inverse hasIsGroup x

  open isGroup hasIsGroup public

open GroupOn

Group : (ℓ : Level) → Type (lsuc ℓ)
Group ℓ = Σ GroupOn
```

We have that a map `is a group homomorphism`{.Agda ident=isGroupHom} if
it `preserves the multiplication`{.Agda ident=pres-⋆}.

```agda
record
  isGroupHom {ℓ} (A B : Group ℓ) (e : A .fst → B .fst) : Type ℓ where
  private
    module A = GroupOn (A .snd)
    module B = GroupOn (B .snd)

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
    e 1A                            ≡⟨ sym B.idʳ ⟩ 
    e 1A B.⋆ 1B                     ≡⟨ ap₂ B._⋆_ refl (sym B.inverseʳ) ⟩ 
    e 1A B.⋆ (e 1A B.⋆ (e 1A) B.⁻¹) ≡⟨ B.associative ⟩ 
    (e 1A B.⋆ e 1A) B.⋆ (e 1A) B.⁻¹ ≡⟨ ap₂ B._⋆_ (sym (pres-⋆ _ _) ∙ ap e A.idˡ) refl ⟩ 
    e 1A B.⋆ (e 1A) B.⁻¹            ≡⟨ B.inverseʳ ⟩ 
    1B                              ∎

  pres-inv : ∀ x → e (A.inverse x) ≡ B.inverse (e x)
  pres-inv x = 
    monoid-inverse-unique B.hasIsMonoid (e x) _ _ 
      (sym (pres-⋆ _ _) ·· ap e A.inverseˡ ·· pres-id) 
      B.inverseʳ
```

<!--
```agda
isProp-isGroupHom : ∀ {ℓ} {G H : Group ℓ} {f} → isProp (isGroupHom G H f) 
isProp-isGroupHom {H = _ , H} a b i .isGroupHom.pres-⋆ x y = 
  GroupOn.hasIsSet H _ _ (a .isGroupHom.pres-⋆ x y) (b .isGroupHom.pres-⋆ x y) i 
```
-->

An `equivalence`{.Agda ident=_≃_} is an equivalence of groups when its
underlying map is a group homomorphism.

```agda
Group≃ : ∀ {ℓ} (A B : Group ℓ) (e : A .fst ≃ B .fst) → Type ℓ
Group≃ A B (f , _) = isGroupHom A B f

Group[_⇒_] : ∀ {ℓ} (A B : Group ℓ) → Type ℓ
Group[ A ⇒ B ] = Σ (isGroupHom A B)

open isGroupHom
```

We automatically derive the proof that paths between groups are
homomorphic equivalences:

```agda
Group-univalent : ∀ {ℓ} → isUnivalent {ℓ = ℓ} (HomT→Str Group≃)
Group-univalent {ℓ = ℓ} =
  autoUnivalentRecord (autoRecord
    (GroupOn {ℓ = ℓ}) Group≃
    (record:
      field[ _⋆_         by pres-⋆ ]
      axiom[ hasIsGroup by (λ _ → isProp-isGroup) ]))
```

## Making groups

Since the interface of `GroupOn`{.Agda} is very deeply nested, we
introduce a helper function for arranging the data of a group into a
record.

```agda
makeGroup 
  : ∀ {ℓ} {G : Type ℓ}
  → isSet G
  → (unit : G) (_⋆_ : G → G → G) (inv : G → G)
  → (∀ x y z → (x ⋆ y) ⋆ z ≡ x ⋆ (y ⋆ z))
  → (∀ x → inv x ⋆ x ≡ unit) → (∀ x → x ⋆ inv x ≡ unit)
  → (∀ x → unit ⋆ x ≡ x)
  → GroupOn G
makeGroup gset id star inv assoc invl invr idl = r where
  open isGroup
  
  r : GroupOn _
  r ._⋆_ = star
  r .hasIsGroup .unit = id
  r .hasIsGroup .hasIsMonoid .hasIsSemigroup .hasIsMagma .hasIsSet = gset
  r .hasIsGroup .hasIsMonoid .hasIsSemigroup .associative = sym (assoc _ _ _)
  r .hasIsGroup .hasIsMonoid .idˡ = idl _
  r .hasIsGroup .hasIsMonoid .idʳ {x = x} = 
    star x id               ≡⟨ ap₂ star refl (sym (invl x)) ⟩
    star x (star (inv x) x) ≡⟨ sym (assoc _ _ _) ⟩
    star (star x (inv x)) x ≡⟨ ap₂ star (invr x) refl ⟩
    star id x               ≡⟨ idl x ⟩
    x                       ∎
  r .hasIsGroup .inverse = inv
  r .hasIsGroup .inverseˡ = invl _
  r .hasIsGroup .inverseʳ = invr _
```

# Symmetric Groups

If $X$ is a set, then the type of all bijections $X \simeq X$ is also a
set, and it forms the carrier for a group: The _symmetric group_ on $X$.

```agda
Sym : ∀ {ℓ} → Set ℓ → Group ℓ
Sym (X , X-set) .fst = X ≃ X
Sym (X , X-set) .snd = groupStr where
  groupStr : GroupOn (X ≃ X)
  groupStr ._⋆_ g f = f ∙e g
```

The group operation is `composition of equivalences`{.Agda ident=_∙e_};
The identity element is `the identity equivalence`{.Agda ident=idEquiv}.

```agda
  groupStr .hasIsGroup .unit = id , idEquiv
```

This type is a set because $X \to X$ is a set (because $X$ is a set by
assumption), and `being an equivalence is a proposition`{.Agdaa
ident=isProp-isEquiv}.

```agda
  groupStr .hasIsGroup .hasIsMonoid .hasIsSemigroup .hasIsMagma .hasIsSet =
    isHLevelΣ 2 (isHLevel→ 2 X-set) (λ f → isProp→isSet (isProp-isEquiv f))
```

The associativity and identity laws hold definitionally.

```agda
  groupStr .hasIsGroup .hasIsMonoid .hasIsSemigroup .associative =
    Σ≡Prop isProp-isEquiv refl
  groupStr .hasIsGroup .hasIsMonoid .idˡ = Σ≡Prop isProp-isEquiv refl
  groupStr .hasIsGroup .hasIsMonoid .idʳ = Σ≡Prop isProp-isEquiv refl
```

The inverse is given by `the inverse equivalence`{.Agda ident=_e⁻¹}, and
the inverse equations hold by the fact that the inverse of an
equivalence is both a section and a retraction.

```agda
  groupStr .hasIsGroup .inverse = _e⁻¹
  groupStr .hasIsGroup .inverseˡ {x = f , eqv} =
    Σ≡Prop isProp-isEquiv (funext (equiv→retraction eqv))
  groupStr .hasIsGroup .inverseʳ {x = f , eqv} =
    Σ≡Prop isProp-isEquiv (funext (equiv→section eqv))
```

<!--
```agda
isAbelian : ∀ {ℓ} (G : Group ℓ) → Type ℓ
isAbelian (G , st) = ∀ (x y : G) → x G.⋆ y ≡ y G.⋆ x
  where module G = GroupOn st
```
-->
