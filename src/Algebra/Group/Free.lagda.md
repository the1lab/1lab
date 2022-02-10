```agda
open import 1Lab.Prelude

open import Algebra.Group

module Algebra.Group.Free where
```

<!--
```agda
private variable
  ℓ : Level
  A : Type ℓ
```
-->

# Free Groups

We give a direct, higher-inductive constructor of the **free group
$F(A)$ on a type $A$ of generators**. While we allow the parameter to be
any type, these are best behaved in the case where $A$ is a set; In this
case, $F$ satisfies the expected universal property.

```agda
data FreeGrp (A : Type ℓ) : Type ℓ where
  inc : A → FreeGrp A
```

The higher-inductive presentation of free algebraic structures is very
direct: There is no need to describe a set of words and then quotient by
an appropriate (complicated) equivalence relation: we can define point
constructors corresponding to the operations of a group, then add in the
path constructors that make this into a group.

```agda
  _◆_ : FreeGrp A → FreeGrp A → FreeGrp A
  inv : FreeGrp A → FreeGrp A
  nil : FreeGrp A
```

We postulate precisely the data that is needed by `makeGroup`{.Agda}.
This is potentially more data than is needed, but constructing maps out
of `FreeGrp`{.Agda} is most conveniently done using the universal
property, and there, this redundancy doesn't matter.

```agda
  f-assoc : ∀ x y z → (x ◆ y) ◆ z ≡ x ◆ (y ◆ z)
  f-invl : ∀ x → inv x ◆ x ≡ nil
  f-invr : ∀ x → x ◆ inv x ≡ nil
  f-idl  : ∀ x → nil ◆ x ≡ x
  squash : isSet (FreeGrp A)
```

We can package these constructors together to give a group with
underlying set `FreeGrp`{.Agda}. See what was meant by "precisely the
data needed by `makeGroup`{.Agda}"?

```agda
Free : Type ℓ → Group ℓ
Free A .fst = FreeGrp A
Free A .snd = makeGroup squash nil _◆_ inv f-assoc f-invl f-invr f-idl
```

This lemma will be very useful later. It says that whenever you want to
prove a proposition by induction on `FreeGrp`{.Agda}, it suffices to
address the value constructors. This is because propositions
automatically respect (higher) path constructors.

```agda
Free-elimProp 
  : ∀ {ℓ} (B : FreeGrp A → Type ℓ)
  → (∀ x → isProp (B x))
  → (∀ x → B (inc x))
  → (∀ x y → B x → B y → B (x ◆ y))
  → (∀ x → B x → B (inv x))
  → B nil
  → ∀ x → B x
```

<details>
<summary>

The proof of it is a direct (by which I mean repetitive) case analysis,
so I've put it in a `<details>`{.html} tag.

</summary>

```agda
Free-elimProp B bp bi bd binv bnil = go where
  go : ∀ x → B x
  go (inc x) = bi x
  go (x ◆ y) = bd x y (go x) (go y)
  go (inv x) = binv x (go x)
  go nil = bnil
  go (f-assoc x y z i) = 
    isProp→PathP (λ i → bp (f-assoc x y z i)) 
      (bd (x ◆ y) z (bd x y (go x) (go y)) (go z))
      (bd x (y ◆ z) (go x) (bd y z (go y) (go z))) i
  go (f-invl x i) = 
    isProp→PathP (λ i → bp (f-invl x i)) (bd (inv x) x (binv x (go x)) (go x)) bnil i
  go (f-invr x i) =
    isProp→PathP (λ i → bp (f-invr x i)) (bd x (inv x) (go x) (binv x (go x))) bnil i
  go (f-idl x i) = isProp→PathP (λ i → bp (f-idl x i)) (bd nil x bnil (go x)) (go x) i
  go (squash x y p q i j) = 
    isProp→SquareP (λ i j → bp (squash x y p q i j)) 
      (λ i → go x) (λ i → go (p i)) (λ i → go (q i)) (λ i → go y) i j
```

</details>

## Universal Property

We now prove the universal property of `FreeGrp`{.Agda}: It's the left
adjoint to the inclusion $\mathrm{Grp} \hookrightarrow \set$. 

```agda
Free⊣Forget
  : ∀ {ℓ} {A : Set ℓ} {G : Group ℓ}
  → Group[ Free (A .fst) ⇒ G ] ≃ (A .fst → G .fst)
Free⊣Forget {A = A , Aset} {G = G , Ggrp} = Iso→Equiv isom where
  open isIso
  module G = GroupOn Ggrp
  module FA = GroupOn (Free A .snd)
```

We start by defining, given a $f : A \to G$, the group homorphism $F(A)
\to G$, which we call `fold`{.Agda}. The fold applies f to the
generators `inc`{.Agda}, and acts homomorphically on the group
operations of `Free`{.Agda}. In addition to being a canonical choice,
we're locked into this choice by the adjunction.

```agda
  fold : (A → G) → FreeGrp A → G
  fold f (inc x) = f x
  fold f (x ◆ y) = fold f x G.⋆ fold f y
  fold f (FreeGrp.inv x) = fold f x G.⁻¹
  fold f nil = G.unit
```

Since `fold`{.Agda} maps the group operations of `Free`{.Agda} to those
of $G$, it must also map the group _identifications_ from `Free`{.Agda}
to those of $G$.

```agda
  fold f (f-assoc x y z i) = 
    G.associative {x = fold f x} {y = fold f y} {z = fold f z} (~ i)
  fold f (f-invl x i) = G.inverseˡ {x = fold f x} i
  fold f (f-invr x i) = G.inverseʳ {x = fold f x} i
  fold f (f-idl x i) = G.idˡ {x = fold f x} i

  fold f (squash x y p q i j) = 
    G.hasIsSet (fold f x) (fold f y) (λ i → fold f (p i)) (λ i → fold f (q i)) i j

  open isGroupHom
```

By construction, the fold is a group homomorphism. It must map $x
\diamond y$ to $\mathrm{fold}(x) \star \mathrm{fold}(y)$, but it does
this by definition.

```agda
  fold-isGH : ∀ f → isGroupHom (Free A) (G , Ggrp) (fold f)
  fold-isGH f .pres-⋆ x y = refl

  isom : Iso _ _
  isom .fst (f , f-gh) x = f (inc x)
  isom .snd .isIso.inv f = fold f , fold-isGH f
  isom .snd .rinv f = refl
```

We can now turn to showing that `fold`{.Agda} has an inverse --- recall
that it's a higher-order function, so the inverse turns group
homomorphisms into functions between their underlying sets. The
construction of the inverse, and one of the homotopies, are very
straightforward. The other direction is more complicated; We must use
`Free-elimProp`{.Agda} to establish the result, which follows from the
assumption that $f$ is a group homomorphism.

```agda
  isom .snd .linv (f , f-hom) =
    Σ≡Prop 
      (λ f → isProp-isGroupHom) 
      (funext (Free-elimProp _ (λ x → G.hasIsSet _ _) 
        (λ x → refl) 
        (λ x y p q → ap₂ G._⋆_ p q ∙ sym (f-hom .pres-⋆ x y)) 
        (λ x p → ap G.inverse p ∙ sym (pres-inv f-hom x)) 
        (sym (pres-id f-hom))))
```
