<!--
```agda
open import Algebra.Group.Cat.Base
open import Algebra.Group.Ab
open import Algebra.Group

open import Cat.Functor.Adjoint
open import Cat.Prelude
```
-->

```agda
module Algebra.Group.Ab.Abelianisation where
```

# Abelianisations {defines=abelianisation}

<!--
```agda
module _ {ℓ} (Grp : Group ℓ) where
  private
    module G = Group-on (Grp .snd)
    G = ⌞ Grp ⌟
  open G
```
-->

We define the **abelianisation** of a group $G$, $G^{ab}$. Rather than
defining it a quotient group (by the commutator subgroup $[G,G]$), we
directly define a group structure on a set-coequaliser. To emphasise the
difference between the groups and their underlying sets, we'll write
$G_0$ and $G^{ab}_0$ in the prose.

```agda
  G^ab : Type ℓ
  G^ab = Coeq {A = G × G × G} (λ (x , y , z) → x ⋆ y ⋆ z)
                              (λ (x , y , z) → x ⋆ z ⋆ y)

  inc^ab : G → G^ab
  inc^ab = inc

  ab-comm : ∀ x y z → inc^ab (x ⋆ y ⋆ z) ≡ inc^ab (x ⋆ z ⋆ y)
  ab-comm x y z = glue (x , y , z)
```

The definition of `ab-comm` gives us extra flexibility in multiplying on
the right by a fixed argument $x$, which will be necessary to prove that
`G^ab`{.Agda} admits a group structure. We can recover the actual
commutativity by choosing $x$ to be the unit. Let's see how equipping
`G^ab`{.Agda} works out:

```agda
  abunit : G^ab
  abunit = inc^ab unit
```

The abelianised unit is the image of the group unit under the map $G_0
\to G^{ab}_0$. We can define the abelianised multiplication by
`coequaliser recursion`{.Agda ident=Coeq-rec₂}, which "reduces" the
problem of defining a map $G^{ab}_0 \to G^{ab}_0 \to G^{ab}_0$ to
defining:

- A map $f : G \to G \to G^{ab}_0$, which will be our multiplication,
satisfying
- for any $a, x, y, z : G$, an identification $f(axyz) = f(axzy)$ ($f$
respects the first coequaliser)
- for any $a, x, y, z : G$, an identification $f((xyz)a) = f((xzy)a)$
($f$ respects the second coequaliser)

```agda
  _ab*_ : G^ab → G^ab → G^ab
  _ab*_ = Coeq-rec₂ squash (λ x y → inc^ab (x ⋆ y)) l2 l1 where abstract
```

Showing these two conditions isn't _hard_, but it does involve a lot of
very tedious algebra. See for yourself:

```agda
    l1 : ∀ a ((x , y , z) : G × G × G)
        → inc^ab (a ⋆ x ⋆ y ⋆ z) ≡ inc^ab (a ⋆ x ⋆ z ⋆ y)
    l1 a (x , y , z) =
      inc^ab (a ⋆ x ⋆ y ⋆ z)           ≡⟨ ap inc^ab associative ⟩
      inc^ab ((a ⋆ x) ⋆ y ⋆ z) {- 1 -} ≡⟨ ab-comm _ _ _ ⟩
      inc^ab ((a ⋆ x) ⋆ z ⋆ y)         ≡⟨ ap inc^ab (sym associative) ⟩
      inc^ab (a ⋆ x ⋆ z ⋆ y)           ∎
```

That comment `{- 1 -}`{.Agda} marks the place where we had to use the
extra generality `ab-comm`{.Agda} gives us; If we had simply coequalised
$x, y \mapsto xy$ and $x, y \mapsto yx$, we'd be lost! There's some more
tedious but straightforward algebra to define the second coequaliser
condition:

```agda
    l2 : ∀ a ((x , y , z) : G × G × G)
        → inc^ab ((x ⋆ y ⋆ z) ⋆ a) ≡ inc^ab ((x ⋆ z ⋆ y) ⋆ a)
    l2 a (x , y , z) =
      inc^ab ((x ⋆ y ⋆ z) ⋆ a) ≡⟨ ap inc^ab (sym associative) ⟩
      inc^ab (x ⋆ (y ⋆ z) ⋆ a) ≡⟨ ab-comm _ _ _ ⟩
      inc^ab (x ⋆ a ⋆ y ⋆ z)   ≡⟨ l1 _ (_ , _ , _) ⟩
      inc^ab (x ⋆ a ⋆ z ⋆ y)   ≡⟨ ab-comm _ _ _ ⟩
      inc^ab (x ⋆ (z ⋆ y) ⋆ a) ≡⟨ ap inc^ab associative ⟩
      inc^ab ((x ⋆ z ⋆ y) ⋆ a) ∎
```

Now we want to define the inverse, but we must first take a detour and
prove that the operation we've defined is commutative. This is still a
bit tedious, but it follows from `ab-comm`: $xy = 1xy = 1yx = yx$.

```agda
  ab*-comm : ∀ x y → x ab* y ≡ y ab* x
  ab*-comm = Coeq-elim-prop₂ (λ _ _ → squash _ _) l1 where abstract
    l1 : ∀ x y → inc^ab (x ⋆ y) ≡ inc^ab (y ⋆ x)
    l1 x y =
      inc^ab (x ⋆ y)        ≡⟨ ap inc^ab (ap₂ _⋆_ (sym G.idl) refl ∙ sym G.associative) ⟩
      inc^ab (unit ⋆ x ⋆ y) ≡⟨ ab-comm _ _ _ ⟩
      inc^ab (unit ⋆ y ⋆ x) ≡⟨ ap inc^ab (G.associative ∙ ap₂ _⋆_ G.idl refl) ⟩
      inc^ab (y ⋆ x)        ∎
```

Now we can define the inverse map. We prove that $x \mapsto x^{-1}$
extends from a map $G_0 \to G_0$ to a map $G^{ab}_0 \to G^{ab}_0$. To
show this, we must prove that $(xyz)^{-1}$ and $(xzy)^{-1}$ are equal in
$G^{ab}_0$. This is why we showed commutativity of `_ab*_`{.Agda} before
defining the inverse map. Here, check out the cute trick embedded in the
tedious algebra:

```agda
  abinv : G^ab → G^ab
  abinv = Coeq-rec squash (λ x → inc^ab (x ⁻¹)) l1 where abstract
    l1 : ((x , y , z) : G × G × G)
        → inc^ab ((x ⋆ y ⋆ z) ⁻¹) ≡ inc^ab ((x ⋆ z ⋆ y) ⁻¹)
    l1 (x , y , z) =
      inc^ab ((x ⋆ y ⋆ z) ⁻¹)                             ≡⟨ ap inc^ab G.inv-comm ⟩
      inc^ab ((y ⋆ z) ⁻¹ — x)                             ≡⟨ ap inc^ab (ap₂ _⋆_ G.inv-comm refl) ⟩
      inc^ab ((z ⁻¹ — y) — x)                             ≡⟨⟩
```

We get to something that is definitionally equal to our `_ab*_`{.Agda}
multiplication, which _we know is commutative_, so we can swap $y^{-1}$
and $z^{-1}$ around!

```agda
      (inc^ab (z ⁻¹) ab* inc^ab (y ⁻¹)) ab* inc^ab (x ⁻¹) ≡⟨ ap₂ _ab*_ (ab*-comm (inc^ab (z ⁻¹)) (inc^ab (y ⁻¹))) (λ i → inc^ab (x ⁻¹)) ⟩
      (inc^ab (y ⁻¹) ab* inc^ab (z ⁻¹)) ab* inc^ab (x ⁻¹) ≡⟨⟩
```

That's a neat trick, isn't it. We still need some Tedious Algebra to
finish the proof:

```agda
      inc^ab ((y ⁻¹ — z) — x)                             ≡⟨ ap inc^ab (ap₂ _⋆_ (sym G.inv-comm) refl ) ⟩
      inc^ab ((z ⋆ y) ⁻¹ — x)                             ≡⟨ ap inc^ab (sym G.inv-comm) ⟩
      inc^ab ((x ⋆ z ⋆ y) ⁻¹)                             ∎
```

The beautiful thing is that, since the group operations on $G^{ab}$ are
all defined in terms of those of $G$, the group axioms are also
inherited from $G$!

```agda
  ab*-associative : ∀ x y z → x ab* (y ab* z) ≡ (x ab* y) ab* z
  ab*-associative = Coeq-elim-prop₃ (λ _ _ _ → squash _ _)
    λ _ _ _ → ap inc^ab associative

  open make-abelian-group
  Abelian-group-on-G^ab : make-abelian-group G^ab
  Abelian-group-on-G^ab .ab-is-set = squash
  Abelian-group-on-G^ab .1g  = abunit
  Abelian-group-on-G^ab .mul = _ab*_
  Abelian-group-on-G^ab .inv = abinv
  Abelian-group-on-G^ab .assoc = ab*-associative
  Abelian-group-on-G^ab .invl =
    Coeq-elim-prop (λ _ → squash _ _) (λ _ → ap inc^ab G.inversel)
  Abelian-group-on-G^ab .idl =
    Coeq-elim-prop (λ _ → squash _ _) (λ _ → ap inc^ab G.idl)
  Abelian-group-on-G^ab .comm = ab*-comm

  Abelianise : Abelian-group ℓ
  Abelianise = to-ab Abelian-group-on-G^ab
```

## Universal property

This finishes the construction of _an_ [[abelian group]] from a [[group]]. To
show that this construction is correct, we'll show that it satisfies a
universal property: The inclusion map $G \xto{i} G^{ab}$ from a group to
its abelianisation is universal among maps from groups to abelian
groups. To wit: If $H$ is some other abelian group with a map $f : G \to
H$, we can factor it uniquely as

$$
G \xto{i} G^{ab} \xto{\hat f} H
$$

for some $\hat f : G^{ab} \to H$ derived from $f$.

```agda
make-free-abelian : ∀ {ℓ} → make-left-adjoint (Ab↪Grp {ℓ = ℓ})
make-free-abelian {ℓ} = go where
  open make-left-adjoint
  go : make-left-adjoint (Ab↪Grp {ℓ = ℓ})
  go .free G = Abelianise G

  go .unit G .hom = inc^ab G
  go .unit G .preserves .is-group-hom.pres-⋆ x y = refl

  go .universal {x = G} {y = H} f .hom =
    Coeq-elim (λ _ → H.has-is-set) (f #_) (λ (a , b , c) → resp a b c) where
    module G = Group-on (G .snd)
    module H = Abelian-group-on (H .snd)
    open is-group-hom (f .preserves)
    abstract
      resp : ∀ a b c → f # (a G.⋆ (b G.⋆ c)) ≡ f # (a G.⋆ (c G.⋆ b))
      resp a b c =
        f # (a G.⋆ (b G.⋆ c))       ≡⟨ pres-⋆ _ _ ⟩
        f # a H.* f # (b G.⋆ c)     ≡⟨ ap (f # a H.*_) (pres-⋆ _ _) ⟩
        f # a H.* (f # b H.* f # c) ≡⟨ ap (f # a H.*_) H.commutes ⟩
        f # a H.* (f # c H.* f # b) ≡˘⟨ ap (f # a H.*_) (pres-⋆ _ _) ⟩
        f # a H.* f # (c G.⋆ b)     ≡˘⟨ pres-⋆ _ _ ⟩
        f # (a G.⋆ (c G.⋆ b))       ∎
  go .universal f .preserves .is-group-hom.pres-⋆ =
    Coeq-elim-prop₂ (λ _ _ → hlevel!) λ _ _ → f .preserves .is-group-hom.pres-⋆ _ _
  go .commutes f = trivial!
  go .unique p = ext (p #ₚ_)
```
