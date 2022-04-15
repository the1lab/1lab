```agda
open import Algebra.Group.Cat.Base
open import Algebra.Group

open import Cat.Instances.Sets.Complete as SL
open import Cat.Prelude

module Algebra.Group.Cat.FinitelyComplete {ℓ} where
```

<!--
```agda
open Group-hom
open Group-on
open Groups._↪_
private variable
  G H K : Group ℓ
```
-->

# Finite limits of groups

We present explicit computations of [finite limits] in the category of
groups, though do note that the [terminal] group is also [initial] (i.e.
it is a [zero object]). Knowing that the category of groups admits a
[right adjoint] functor into the category of sets (the [underlying set]
functor) drives us in computing limits of groups as limits of sets,
and equipping those with a group structure: we are _forced_ to do this
since [right adjoints preserve limits].

[finite limits]: Cat.Diagram.Limit.Finite.html
[terminal]: Cat.Diagram.Terminal.html
[initial]: Cat.Diagram.Initial.html
[zero object]: Cat.Diagram.Zero.html
[right adjoint]: Cat.Functor.Adjoint.html
[underlying set]: Algebra.Group.Cat.Base.html#the-underlying-set
[right adjoints preserve limits]: Cat.Functor.Adjoint.Continuous.html

## The zero group

```agda
open import Cat.Diagram.Terminal (Groups ℓ)
open import Cat.Diagram.Initial (Groups ℓ)
open import Cat.Diagram.Zero (Groups ℓ)
```

The zero object in the category of groups is given by the unit type,
equipped with its unique group structure. Correspondingly, we may refer
to this group in prose either as $0$ or as $\{\star\}$.

```agda
Zero-group : ∀ {ℓ} → Group ℓ
Zero-group = Lift _ ⊤ , make-group
  (λ x y p q i j → lift tt)
  (lift tt) (λ _ _ → lift tt) (λ _ → lift tt)
  (λ _ _ _ → refl) (λ x → refl) (λ x → refl) (λ x → refl)

Zero-group-is-initial : is-initial Zero-group
Zero-group-is-initial (_ , G) .centre = (λ x → G.unit) , gh where
  module G = Group-on G
  gh : Group-hom _ _ (λ x → G.unit)
  gh .pres-⋆ x y =
    G.unit            ≡˘⟨ G.idl ⟩
    G.unit G.⋆ G.unit ∎
Zero-group-is-initial (_ , G) .paths x =
  Forget-is-faithful (funext λ _ → sym (Group-hom.pres-id (x .snd)))

Zero-group-is-terminal : is-terminal Zero-group
Zero-group-is-terminal _ .centre =
  (λ _ → lift tt) , (record { pres-⋆ = λ _ _ _ → lift tt })
Zero-group-is-terminal _ .paths x = Forget-is-faithful refl

Zero-group-is-zero : is-zero Zero-group
Zero-group-is-zero = record
  { has-is-initial = Zero-group-is-initial
  ; has-is-terminal = Zero-group-is-terminal
  }

∅ᴳ : Zero
∅ᴳ .Zero.∅ = Zero-group
∅ᴳ .Zero.has-is-zero = Zero-group-is-zero
```

## Direct products

```agda
open import Cat.Diagram.Product (Groups ℓ)
```

We compute the product of two groups $G \times H$ as the product of
their underlying sets, equipped with the operation of "pointwise
addition".

```agda
Direct-product : Group ℓ → Group ℓ → Group ℓ
Direct-product (G , Gg) (H , Hg) = (G × H) , G×Hg where
  module G = Group-on Gg
  module H = Group-on Hg

  abstract
    gh-set : is-set (G × H)
    gh-set = ×-is-hlevel 2 G.has-is-set H.has-is-set

  G×Hg : Group-on (G × H)
  G×Hg = make-group gh-set
    (G.unit , H.unit)
    (λ { (a , b) (x , y) → a G.⋆ x , b H.⋆ y })
    (λ { (a , b) → a G.⁻¹ , b H.⁻¹ })
    (λ { x y z → ap₂ _,_ (sym G.associative) (sym H.associative) })
    (λ x → ap₂ _,_ G.inversel H.inversel)
    (λ x → ap₂ _,_ G.inverser H.inverser)
    (λ x → ap₂ _,_ G.idl H.idl)
```

The projection maps and universal factoring are all given exactly as for
the category of sets.

```agda
proj₁ : Groups.Hom (Direct-product G H) G
proj₁ .fst = fst
proj₁ .snd .pres-⋆ x y = refl

proj₂ : Groups.Hom (Direct-product G H) H
proj₂ .fst = snd
proj₂ .snd .pres-⋆ x y = refl

factor : Groups.Hom G H → Groups.Hom G K → Groups.Hom G (Direct-product H K)
factor f g .fst x = f .fst x , g .fst x
factor f g .snd .pres-⋆ x y = ap₂ _,_ (f .snd .pres-⋆ _ _) (g .snd .pres-⋆ _ _)

Direct-product-is-product : is-product {G} {H} proj₁ proj₂
Direct-product-is-product {G} {H} = p where
  open is-product
  p : is-product _ _
  p .⟨_,_⟩ = factor
  p .π₁∘factor = Forget-is-faithful refl
  p .π₂∘factor = Forget-is-faithful refl
  p .unique other p q = Forget-is-faithful (funext λ x →
    ap₂ _,_ (happly (ap fst p) x) (happly (ap fst q) x))
```

What sets the direct product of groups apart from (e.g.) the cartesian
product of sets is that both "factors" embed into the direct product, by
taking the identity as the other coordinate: $x \hookrightarrow (x, 1)$.
Indeed, in the category of _abelian_ groups, the direct product is also
a coproduct.

```agda
inj₁ : G Groups.↪ Direct-product G H
inj₁ {G} {H} .mor .fst x = x , H .snd .unit
inj₁ {G} {H} .mor .snd .pres-⋆ x y = ap (_ ,_) (sym (H .snd .idl))
inj₁ {G} {H} .monic g h x = Forget-is-faithful (funext λ e i → x i .fst e .fst)

inj₂ : H Groups.↪ Direct-product G H
inj₂ {H} {G} .mor .fst x = G .snd .unit , x
inj₂ {H} {G} .mor .snd .pres-⋆ x y = ap (_, _) (sym (G .snd .idl))
inj₂ {H} {G} .monic g h x = Forget-is-faithful (funext λ e i → x i .fst e .snd)
```

## Equalisers

```agda
open import Cat.Diagram.Equaliser
```

The equaliser of two group homomorphisms $f, g : G \to H$ is given by
their equaliser as Set-morphisms, equipped with the evident group
structure. Indeed, we go ahead and compute the actual `Equaliser`{.Agda}
in sets, and re-use all of its infrastructure to make an equaliser in
`Groups`{.Agda}.

```agda
module _ {G H : Group ℓ} (f g : Groups.Hom G H) where
  private
    module G = Group-on (G .snd)
    module H = Group-on (H .snd)

    module f = Group-hom (f .snd)
    module g = Group-hom (g .snd)
    module seq = Equaliser
      (SL.Sets-equalisers
        {A = G.underlying-set}
        {B = H.underlying-set}
        (fst f) (fst g))
```

Recall that points there are elements of the domain (here, a point $x :
G$) together with a proof that $f(x) = g(x)$. To "lift" the group
structure from $G$ to $\id{equ}(f,g)$, we must prove that, if $f(x)
= g(x)$ and $f(y) = g(y)$, then $f(x\star y) = g(x\star y)$. But this
follows from $f$ and $g$ being group homomorphisms:

```agda
  Equaliser-group : Group ℓ
  Equaliser-group = _ , equ-group where
    equ-⋆ : ∣ seq.apex ∣ → ∣ seq.apex ∣ → ∣ seq.apex ∣
    equ-⋆ (a , p) (b , q) = (a G.⋆ b) , r where abstract
      r : f .fst (G .snd ._⋆_ a b) ≡ g .fst (G .snd ._⋆_ a b)
      r = f.pres-⋆ a b ·· ap₂ H._⋆_ p q ·· sym (g.pres-⋆ _ _)

    equ-inv : ∣ seq.apex ∣ → ∣ seq.apex ∣
    equ-inv (x , p) = x G.⁻¹ , q where abstract
      q : f .fst (G.inverse x) ≡ g .fst (G.inverse x)
      q = f.pres-inv ·· ap H._⁻¹ p ·· sym g.pres-inv

    abstract
      invs : f .fst G.unit ≡ g .fst G.unit
      invs = f.pres-id ∙ sym g.pres-id
```

Similar yoga must be done for the inverse maps and the group unit.

```agda
    equ-group : Group-on ∣ seq.apex ∣
    equ-group = make-group
      (seq.apex .is-tr)
      (G.unit , invs) equ-⋆ equ-inv
      (λ x y z → Σ-prop-path (λ _ → H.has-is-set _ _) (sym G.associative))
      (λ x → Σ-prop-path (λ _ → H.has-is-set _ _) G.inversel)
      (λ x → Σ-prop-path (λ _ → H.has-is-set _ _) G.inverser)
      λ x → Σ-prop-path (λ _ → H.has-is-set _ _) G.idl

  open is-equaliser
  open Equaliser
```

We can then, pretty effortlessly, prove that the
`Equaliser-group`{.Agda}, together with the canonical injection
$\id{equ}(f,g) \mono G$, equalise the group homomorphisms $f$ and
$g$.

```agda
  Groups-equalisers : Equaliser (Groups ℓ) f g
  Groups-equalisers .apex = Equaliser-group
  Groups-equalisers .equ = fst , record { pres-⋆ = λ x y → refl }
  Groups-equalisers .has-is-eq .equal = Forget-is-faithful seq.equal
  Groups-equalisers .has-is-eq .limiting {F = F} {e′} p = map , lim-gh where
    map = seq.limiting {F = underlying-set (F .snd)} (ap fst p)

    lim-gh : Group-hom F Equaliser-group map
    lim-gh .pres-⋆ x y = Σ-prop-path (λ _ → H.has-is-set _ _) (e′ .snd .pres-⋆ _ _)

  Groups-equalisers .has-is-eq .universal {F = F} {p = p} = Forget-is-faithful
    (seq.universal {F = underlying-set (F .snd)} {p = ap fst p})

  Groups-equalisers .has-is-eq .unique {F = F} {p = p} q = Forget-is-faithful
    (seq.unique {F = underlying-set (F .snd)} {p = ap fst p} (ap fst q))
```

Putting all of these constructions together, we get the proof that
`Groups` is finitely complete, since we can compute pullbacks as certain
equalisers.

```agda
open import Cat.Diagram.Limit.Finite

Groups-finitely-complete : Finitely-complete (Groups ℓ)
Groups-finitely-complete = with-equalisers (Groups ℓ) top prod Groups-equalisers
  where
    top : Terminal
    top .Terminal.top = Zero-group
    top .Terminal.has⊤ = Zero-group-is-terminal

    prod : ∀ A B → Product A B
    prod A B .Product.apex = Direct-product A B
    prod A B .Product.π₁ = proj₁
    prod A B .Product.π₂ = proj₂
    prod A B .Product.has-is-product = Direct-product-is-product
```
