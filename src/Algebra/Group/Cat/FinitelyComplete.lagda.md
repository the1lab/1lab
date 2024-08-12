<!--
```agda
open import Algebra.Group.Cat.Base
open import Algebra.Group

open import Cat.Instances.Sets.Complete as SL
open import Cat.Diagram.Terminal
open import Cat.Diagram.Initial
open import Cat.Diagram.Product
open import Cat.Diagram.Zero
open import Cat.Prelude
```
-->

```agda
module Algebra.Group.Cat.FinitelyComplete {ℓ} where
```

<!--
```agda
open is-group-hom
open Group-on
open Groups._↪_
private variable
  G H K : Group ℓ
```
-->

# Finite limits of groups

We present explicit computations of [[finite limits]] in the category of
groups, though do note that the [[terminal|terminal object]] group is
also [initial] (i.e.  it is a [zero object]). Knowing that the category
of groups admits a [[right adjoint]] functor into the category of sets
(the [underlying set] functor) drives us in computing limits of groups
as limits of sets, and equipping those with a group structure: we are
_forced_ to do this since [right adjoints preserve limits].

[terminal]: Cat.Diagram.Terminal.html
[initial]: Cat.Diagram.Initial.html
[zero object]: Cat.Diagram.Zero.html
[underlying set]: Algebra.Group.Cat.Base.html#the-underlying-set
[right adjoints preserve limits]: Cat.Functor.Adjoint.Continuous.html

## The zero group {defines="zero-group"}

The zero object in the category of groups is given by the unit type,
equipped with its unique group structure. Correspondingly, we may refer
to this group in prose either as $0$ or as $\{\star\}$.

```agda
Zero-group : ∀ {ℓ} → Group ℓ
Zero-group = to-group zg where
  zg : make-group (Lift _ ⊤)
  zg .make-group.group-is-set x y p q i j = lift tt
  zg .make-group.unit = lift tt
  zg .make-group.mul = λ x y → lift tt
  zg .make-group.inv x = lift tt
  zg .make-group.assoc x y z = refl
  zg .make-group.invl x = refl
  zg .make-group.idl x = refl

Zero-group-is-initial : is-initial (Groups ℓ) Zero-group
Zero-group-is-initial (_ , G) .centre = total-hom (λ x → G.unit) gh where
  module G = Group-on G
  gh : is-group-hom _ _ (λ x → G.unit)
  gh .pres-⋆ x y =
    G.unit            ≡˘⟨ G.idl ⟩
    G.unit G.⋆ G.unit ∎
Zero-group-is-initial (_ , G) .paths x =
  ext λ _ → sym (is-group-hom.pres-id (x .preserves))

Zero-group-is-terminal : is-terminal (Groups ℓ) Zero-group
Zero-group-is-terminal _ .centre =
  total-hom (λ _ → lift tt) record { pres-⋆ = λ _ _ _ → lift tt }
Zero-group-is-terminal _ .paths x = trivial!

Zero-group-is-zero : is-zero (Groups ℓ) Zero-group
Zero-group-is-zero = record
  { has-is-initial = Zero-group-is-initial
  ; has-is-terminal = Zero-group-is-terminal
  }

∅ᴳ : Zero (Groups ℓ)
∅ᴳ .Zero.∅ = Zero-group
∅ᴳ .Zero.has-is-zero = Zero-group-is-zero
```

## Direct products

We compute the product of two groups $G \times H$ as the product of
their underlying sets, equipped with the operation of "pointwise
addition".

```agda
Direct-product : Group ℓ → Group ℓ → Group ℓ
Direct-product (G , Gg) (H , Hg) = to-group G×Hg where
  module G = Group-on Gg
  module H = Group-on Hg

  G×Hg : make-group (∣ G ∣ × ∣ H ∣)
  G×Hg .make-group.group-is-set = hlevel 2
  G×Hg .make-group.unit = G.unit , H.unit
  G×Hg .make-group.mul (a , x) (b , y) = a G.⋆ b , x H.⋆ y
  G×Hg .make-group.inv (a , x) = a G.⁻¹ , x H.⁻¹
  G×Hg .make-group.assoc x y z = ap₂ _,_ G.associative H.associative
  G×Hg .make-group.invl x = ap₂ _,_ G.inversel H.inversel
  G×Hg .make-group.idl x = ap₂ _,_ G.idl H.idl
```

The projection maps and universal factoring are all given exactly as for
the category of sets.

```agda
proj₁ : Groups.Hom (Direct-product G H) G
proj₁ .hom = fst
proj₁ .preserves .pres-⋆ x y = refl

proj₂ : Groups.Hom (Direct-product G H) H
proj₂ .hom = snd
proj₂ .preserves .pres-⋆ x y = refl

factor : Groups.Hom G H → Groups.Hom G K → Groups.Hom G (Direct-product H K)
factor f g .hom x = f # x , g # x
factor f g .preserves .pres-⋆ x y = ap₂ _,_ (f .preserves .pres-⋆ _ _) (g .preserves .pres-⋆ _ _)

Direct-product-is-product : is-product (Groups ℓ) {G} {H} proj₁ proj₂
Direct-product-is-product {G} {H} = p where
  open is-product
  p : is-product _ _ _
  p .⟨_,_⟩ = factor
  p .π₁∘⟨⟩ = Grp↪Sets-is-faithful refl
  p .π₂∘⟨⟩ = Grp↪Sets-is-faithful refl
  p .unique p q = Grp↪Sets-is-faithful (funext λ x →
    ap₂ _,_ (happly (ap hom p) x) (happly (ap hom q) x))
```

What sets the direct product of groups apart from (e.g.) the cartesian
product of sets is that both "factors" embed into the direct product, by
taking the identity as the other coordinate: $x \hookrightarrow (x, 1)$.
Indeed, in the category of _abelian_ groups, the direct product is also
a coproduct.

```agda
inj₁ : G Groups.↪ Direct-product G H
inj₁ {G} {H} .mor .hom x = x , H .snd .unit
inj₁ {G} {H} .mor .preserves .pres-⋆ x y = ap (_ ,_) (sym (H .snd .idl))
inj₁ {G} {H} .monic g h x = Grp↪Sets-is-faithful (funext λ e i → (x i # e) .fst)

inj₂ : H Groups.↪ Direct-product G H
inj₂ {H} {G} .mor .hom x = G .snd .unit , x
inj₂ {H} {G} .mor .preserves .pres-⋆ x y = ap (_, _) (sym (G .snd .idl))
inj₂ {H} {G} .monic g h x = Grp↪Sets-is-faithful (funext λ e i → (x i # e) .snd)
```

## Equalisers

```agda
open import Cat.Diagram.Equaliser

open Equalisers
```

The equaliser of two group homomorphisms $f, g : G \to H$ is given by
their equaliser as Set-morphisms, equipped with the evident group
structure. Indeed, we go ahead and compute the actual `Equaliser`{.Agda}
in sets, and re-use all of its infrastructure to make an equaliser in
`Groups`{.Agda}.

```agda
Groups-equalisers : Equalisers (Groups ℓ)
Groups-equalisers .Equ {G} {H} f g = to-group equ-group where
  module G = Group-on (G .snd)
  module H = Group-on (H .snd)
  module f = is-group-hom (f .preserves)
  module g = is-group-hom (g .preserves)
```

Recall that points there are elements of the domain (here, a point $x :
G$) together with a proof that $f(x) = g(x)$. To "lift" the group
structure from $G$ to $\rm{equ}(f,g)$, we must prove that, if $f(x)
= g(x)$ and $f(y) = g(y)$, then $f(x\star y) = g(x\star y)$. But this
follows from $f$ and $g$ being group homomorphisms:

```agda
  equ-group : make-group (Σ[ x ∈ G ] (f # x ≡ g # x))
  equ-group .make-group.group-is-set = hlevel 2
  equ-group .make-group.mul (x , p) (y , q) =
    x G.⋆ y , ⋆-eq where abstract
      ⋆-eq : f # (x G.⋆ y) ≡ g # (x G.⋆ y)
      ⋆-eq = f.pres-⋆ _ _ ·· ap₂ H._⋆_ p q ·· sym (g.pres-⋆ _ _)
```

Similar yoga must be done for the inverse maps and the group unit.

```agda
  equ-group .make-group.unit =
    G.unit , unit-eq where abstract
      unit-eq : f # G.unit ≡ g # G.unit
      unit-eq = f.pres-id ∙ sym g.pres-id
  equ-group .make-group.inv (x , p) =
    x G.⁻¹ , inv-eq where abstract
      inv-eq : f # (G.inverse x) ≡ g # (G.inverse x)
      inv-eq = f.pres-inv ·· ap H._⁻¹ p ·· sym g.pres-inv
  equ-group .make-group.assoc x y z = Σ-prop-path! G.associative
  equ-group .make-group.invl x = Σ-prop-path! G.inversel
  equ-group .make-group.idl x = Σ-prop-path! G.idl
```

We can then, pretty effortlessly, prove that this group, together with
the canonical injection $\rm{equ}(f,g) \mono G$, equalise the group
homomorphisms $f$ and $g$.


```agda
Groups-equalisers .equ f g .hom = fst
Groups-equalisers .equ f g .preserves .pres-⋆ _ _ = refl
Groups-equalisers .equal = ext (λ x p → p)
Groups-equalisers .equalise e p .hom x = e # x , p #ₚ x
Groups-equalisers .equalise e p .preserves .pres-⋆ x y =
  Σ-prop-path! (e .preserves .pres-⋆ x y)
Groups-equalisers .equ∘equalise = trivial!
Groups-equalisers .equalise-unique p =
  ext λ x → Σ-prop-path! (p #ₚ x)
```

Putting all of these constructions together, we get the proof that
`Groups` is finitely complete, since we can compute pullbacks as certain
equalisers.

```agda
open import Cat.Diagram.Limit.Finite

Groups-finitely-complete : Finitely-complete (Groups ℓ)
Groups-finitely-complete = with-equalisers (Groups ℓ) top prod Groups-equalisers
  where
    top : Terminal (Groups ℓ)
    top .Terminal.top = Zero-group
    top .Terminal.has⊤ = Zero-group-is-terminal

    prod : Binary-products (Groups ℓ)
    prod = has-products→binary-products $ λ A B →
      Direct-product-is-product
```
