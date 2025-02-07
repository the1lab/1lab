<!--
```agda
open import 1Lab.Reflection.Induction

open import Algebra.Group.Cat.Base
open import Algebra.Group

open import Cat.Diagram.Initial
open import Cat.Functor.Adjoint
open import Cat.Prelude
```
-->

```agda
module Algebra.Group.Free where
```

<!--
```agda
private variable
  ℓ : Level
  A : Type ℓ
open is-group-hom
open Group-on
open Initial
```
-->

# Free groups {defines=free-group-construction}

We give a direct, higher-inductive constructor of the **free group
$F(A)$ on a type $A$ of generators**. While we allow the parameter to be
any type, these are best behaved in the case where $A$ is a set; In this
case, $F$ satisfies the expected universal property.

```agda
data Free-group (A : Type ℓ) : Type ℓ where
  inc : A → Free-group A
```

The higher-inductive presentation of free algebraic structures is very
direct: There is no need to describe a set of words and then quotient by
an appropriate (complicated) equivalence relation: we can define point
constructors corresponding to the operations of a group, then add in the
path constructors that make this into a group.

```agda
  _◆_ : Free-group A → Free-group A → Free-group A
  inv : Free-group A → Free-group A
  nil : Free-group A
```

We postulate precisely the data that is needed by `make-group`{.Agda}.
This is potentially more data than is needed, but constructing maps out
of `Free-group`{.Agda} is most conveniently done using the universal
property, and there, this redundancy doesn't matter.

```agda
  f-assoc : ∀ x y z → x ◆ (y ◆ z) ≡ (x ◆ y) ◆ z
  f-invl : ∀ x → inv x ◆ x ≡ nil
  f-idl  : ∀ x → nil ◆ x ≡ x
  squash : is-set (Free-group A)
```

We can package these constructors together to give a group with
underlying set `Free-group`{.Agda}. See what was meant by "precisely the
data needed by `make-group`{.Agda}"?

```agda
Free-Group : Type ℓ → Group ℓ
Free-Group A = to-group fg where
  fg : make-group (Free-group A)
  fg .make-group.group-is-set = squash
  fg .make-group.unit = nil
  fg .make-group.mul = _◆_
  fg .make-group.inv = inv
  fg .make-group.assoc = f-assoc
  fg .make-group.invl = f-invl
  fg .make-group.idl = f-idl
```

This lemma will be very useful later. It says that whenever you want to
prove a proposition by induction on `Free-group`{.Agda}, it suffices to
address the value constructors. This is because propositions
automatically respect (higher) path constructors.

```agda
Free-elim-prop
  : ∀ {ℓ} (B : Free-group A → Type ℓ)
  → (∀ x → is-prop (B x))
  → (∀ x → B (inc x))
  → (∀ x → B x → ∀ y → B y → B (x ◆ y))
  → (∀ x → B x → B (inv x))
  → B nil
  → ∀ x → B x
```

The proof of it is a direct (by which I mean repetitive) case analysis,
so we let our reflection machinery handle it for us.

```agda
unquoteDef Free-elim-prop = make-elim-with (default-elim-visible into 1)
  Free-elim-prop (quote Free-group)
```

</details>

## Universal property {defines=free-group}

We now prove the universal property of `Free-group`{.Agda}, or, more
specifically, of the map `inc`{.Agda}: It gives a [[universal way of
mapping|universal-morphism]] from the category of sets to an object in the category of
groups, in that any map from a set to (the underlying set of) a group
factors uniquely through `inc`{.Agda}. To establish this result, we
first implement a helper function, `fold-free-group`{.Agda}, which,
given the data of where to send the generators of a free group,
determines a group homomorphism.

```agda
fold-free-group
  : {A : Type ℓ} {G : Group ℓ}
  → (A → ⌞ G ⌟) → Groups.Hom (Free-Group A) G
fold-free-group {A = A} {G = G , ggrp} map = total-hom go go-hom where
  module G = Group-on ggrp
```

While it might seem that there are many cases to consider when defining
the function `go`{.Agda}, for most of them, our hand is forced: For
example, we must take multiplication in the free group (the `_◆_`{.Agda}
constructor) to multiplication in the codomain.

```agda
  go : Free-group A → ∣ G ∣
  go (inc x) = map x
  go (x ◆ y) = go x G.⋆ go y
  go (inv x) = go x G.⁻¹
  go nil = G.unit
```

Since `_◆_`{.Agda} is interpreted as multiplication in $G$, it's $G$'s
associativity, identity and inverse laws that provide the cases for
`Free-group`{.Agda}'s higher constructors.

```agda
  go (f-assoc x y z i) = G.associative {x = go x} {y = go y} {z = go z} i
  go (f-invl x i) = G.inversel {x = go x} i
  go (f-idl x i) = G.idl {x = go x} i
  go (squash x y p q i j) =
    G.has-is-set (go x) (go y) (λ i → go (p i)) (λ i → go (q i)) i j

  open is-group-hom

  go-hom : is-group-hom _ _ go
  go-hom .pres-⋆ x y = refl
```

Now, given a set $S$, we must come up with a group $G$, with a map
$\eta : S \to U(G)$ (in $\Sets$, where $U$ is the [underlying set functor]),
such that, for any other group $H$, any map $S \to U(H)$ can be factored
uniquely as $S \xrightarrow{\eta} U(G) \to U(H)$. As hinted above, we
pick $G = \rm{Free}(S)$, the free group with $S$ as its set of
generators, and the universal map $\eta$ is in fact `inc`{.Agda}.

[underlying set functor]: Algebra.Group.Cat.Base.html#the-underlying-set

<!--
```agda
open Free-object
```
-->

```agda
make-free-group : ∀ {ℓ} (S : Set ℓ) → Free-object Grp↪Sets S
make-free-group S .free = Free-Group ⌞ S ⌟
make-free-group S .unit = inc
make-free-group S .fold = fold-free-group
make-free-group S .commute = refl
make-free-group S .unique {H} g p =
  ext $ Free-elim-prop _ (λ _ → hlevel 1)
    (p #ₚ_)
    (λ a p b q → g.pres-⋆ a b ∙ ap₂ H._⋆_ p q)
    (λ a p → g.pres-inv ∙ ap H.inverse p)
    g.pres-id
  where
    module H = Group-on (H .snd)
    module g = is-group-hom (g .preserves)

module Free-groups {ℓ} (S : Set ℓ) = Free-object (make-free-group S)
```
