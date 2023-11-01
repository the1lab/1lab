<!--
```agda
open import Cat.Displayed.Univalence.Thin
open import Cat.Diagram.Product.Indexed
open import Cat.Diagram.Product
open import Cat.Displayed.Total
open import Cat.Instances.OFE
open import Cat.Prelude
```
-->

```agda
module Cat.Instances.OFE.Product where
```

# Products of OFEs

The [category of OFEs][OFE] admits [[products]]: the relations are,
levelwise, pairwise! That is, $(x, y) \within{n} (x', y')$ if $x
\within{n} x'$ and $y \within{n} y'$.  Distributing the axioms over
products is enough to establish that this is actually an OFE.

[OFE]: Cat.Instances.OFE.html
[products]: Cat.Diagram.Product.html

<!--
```agda
open OFE-Notation

module _ {ℓa ℓb ℓa' ℓb'} {A : Type ℓa} {B : Type ℓb} (O : OFE-on ℓa' A) (P : OFE-on ℓb' B)
  where
  private
    instance
      _ = O
      _ = P
    module O = OFE-on O
    module P = OFE-on P
  open OFE-H-Level O
  open OFE-H-Level P
```
-->

```agda
  ×-OFE : OFE-on (ℓa' ⊔ ℓb') (A × B)
  ×-OFE .within n (x , y) (x' , y') = (x ≈[ n ] x') × (y ≈[ n ] y')
  ×-OFE .has-is-ofe .has-is-prop n x y = hlevel 1

  ×-OFE .has-is-ofe .≈-refl  n = O.≈-refl n , P.≈-refl n
  ×-OFE .has-is-ofe .≈-sym   n (p , q) = O.≈-sym n p , P.≈-sym n q
  ×-OFE .has-is-ofe .≈-trans n (p , q) (p' , q') =
    O.≈-trans n p p' , P.≈-trans n q q'

  ×-OFE .has-is-ofe .bounded (a , b) (a' , b') = O.bounded a a' , P.bounded b b'
  ×-OFE .has-is-ofe .step n _ _ (p , p') = O.step n _ _ p , P.step n _ _ p'
  ×-OFE .has-is-ofe .limit x y f =
    ap₂ _,_ (O.limit _ _ λ n → f n .fst) (P.limit _ _ λ n → f n .snd)
```

<!--
```agda
open Product
open is-product
open Total-hom
```
-->

By construction, this OFE is actually the proper categorical product of
the OFE structures we started with: since this is a very concrete
category, most of the reasoning piggy-backs off of that for types, which
is almost definitional. Other than the noise inherent to formalisation,
the argument is immediate:

```agda
OFE-Product : ∀ {ℓ ℓ'} A B → Product (OFEs ℓ ℓ') A B
OFE-Product A B .apex = from-ofe-on (×-OFE (A .snd) (B .snd))
OFE-Product A B .π₁ .hom = fst
OFE-Product A B .π₁ .preserves .pres-≈ = fst

OFE-Product A B .π₂ .hom = snd
OFE-Product A B .π₂ .preserves .pres-≈ = snd

OFE-Product A B .has-is-product .⟨_,_⟩ f g .hom x = f # x , g # x
OFE-Product A B .has-is-product .⟨_,_⟩ f g .preserves .pres-≈ p =
  f .preserves .pres-≈ p , g .preserves .pres-≈ p

OFE-Product A B .has-is-product .π₁∘factor = trivial!
OFE-Product A B .has-is-product .π₂∘factor = trivial!
OFE-Product A B .has-is-product .unique o p q = ext λ x → p #ₚ x , q #ₚ x
```

<!--
```agda
module
  _ {ℓi ℓf ℓr} {I : Type ℓi} (F : I → Type ℓf) (P : ∀ i → OFE-on ℓr (F i)) where
  private
    instance
      P-ofe : ∀ {i} → OFE-on ℓr (F i)
      P-ofe {i} = P i
    module P {i} = OFE-on (P i)
    module _ {i} where open OFE-H-Level (P i) public
```
-->

## Indexed products

We now turn to a slightly more complicated case: _indexed_ products of
OFEs: because Agda is, by default, a predicative theory, we run into
some issues with universe levels when defining the indexed product.
Let's see them:

Suppose we have an index type $I : \ty$ in the $i$th universe, and
a family $P_i : \ty$, valued now in the $p$th universe. Moreover,
the family $P_i$ should be pointwise an OFE, with nearness relation
living in, let's say, the $r$th universe. We will define the relation on
$\prod P$ to be

$$
\forall i, f(i) \within{n} g(i) \text{,} \tag 1
$$

but this type is _too large_: Since we quantify over $i : I$, and return
one of the approximate equalities, it must live in the $(r \sqcup i)$th
universe; but if we want indexed products to be in the same category we
started with, it should live in the $r$th!

Fortunately, to us, this is an annoyance, not an impediment: here in the
1Lab, we assume [propositional resizing][omega] throughout. Since the
product type $(1)$ is a proposition, it is equivalent to a small type,
so we can put it in any universe, including the $r$th.

[omega]: 1Lab.Resizing.html

The construction is essentially the same as for binary products:
however, since resizing is explicit, we have to do a bit more faffing
about to get the actual inhabitant of $(1)$ that we're interested in.

```agda
  Π-OFE : OFE-on ℓr (∀ i → F i)
  Π-OFE .within n f g = Lift ℓr (□ (∀ i → f i ≈[ n ] g i))
  Π-OFE .has-is-ofe .has-is-prop n x y = Lift-is-hlevel 1 squash
  Π-OFE .has-is-ofe .≈-refl n = lift (inc λ i → P.≈-refl n)
  Π-OFE .has-is-ofe .≈-sym n (lift x) = lift do
    x ← x
    pure λ i → P.≈-sym n (x i)
  Π-OFE .has-is-ofe .≈-trans n (lift p) (lift q) = lift do
    p ← p
    q ← q
    pure λ i → P.≈-trans n (p i) (q i)
  Π-OFE .has-is-ofe .bounded x y = lift (inc λ i → P.bounded (x i) (y i))
  Π-OFE .has-is-ofe .step n x y (lift p) = lift do
    p ← p
    pure λ i → P.step n (x i) (y i) (p i)
  Π-OFE .has-is-ofe .limit x y wit i j = P.limit (x j) (y j) (λ n → wit' n j) i
    where
      wit' : ∀ n i → within (P i) n (x i) (y i)
      wit' n i = out! {pa = hlevel 1} (wit n .Lift.lower) i
```

<!--
```agda
open is-indexed-product
open Indexed-product
```
-->

And, again, by essentially the same argument, we can establish that this
is the categorical [_indexed_ product][ip] of $P$ in the category of
OFEs, as long as all the sizes match up.

[ip]: Cat.Diagram.Product.Indexed.html

```agda
OFE-Indexed-product
  : ∀ {ℓo ℓr} {I : Type ℓo} (F : I → OFE ℓo ℓr)
  → Indexed-product (OFEs ℓo ℓr) F
OFE-Indexed-product F .ΠF = from-ofe-on $
  Π-OFE (λ i → ∣ F i .fst ∣) (λ i → F i .snd)
OFE-Indexed-product F .π i .hom f = f i
OFE-Indexed-product F .π i .preserves .pres-≈ α =
  out! {pa = F i .snd .has-is-prop _ _ _} ((_$ i) <$> α .Lift.lower)
OFE-Indexed-product F .has-is-ip .tuple f .hom x i = f i # x
OFE-Indexed-product F .has-is-ip .tuple f .preserves .pres-≈ wit =
  lift $ inc λ i → f i .preserves .pres-≈ wit
OFE-Indexed-product F .has-is-ip .commute = trivial!
OFE-Indexed-product F .has-is-ip .unique f prf =
  ext λ x y → prf y #ₚ x
```
