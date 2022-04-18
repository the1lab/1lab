```agda
open import Algebra.Group.Cat.Base
open import Algebra.Group.Ab
open import Algebra.Prelude
open import Algebra.Group

open import Data.Set.Coequaliser

module Algebra.Group.Ab.Free where
```

<!--
```agda
private variable
  ℓ : Level
```
-->

# Free Abelian Groups

```agda
module _ (Grp@(G , gst) : Group ℓ) where
  private module G = Group-on gst
  open G
```

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
  _ab*_ = Coeq-rec₂ squash (λ x y → inc^ab (x ⋆ y)) l2 l1
    where abstract
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
  ab*-comm = Coeq-elim-prop₂ (λ _ _ → squash _ _) l1
    where abstract
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
  abinv = Coeq-rec squash (λ x → inc^ab (x ⁻¹)) l1
    where abstract
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
  ab*-associative : ∀ x y z → (x ab* y) ab* z ≡ x ab* (y ab* z)
  ab*-associative = Coeq-elim-prop₃ (λ _ _ _ → squash _ _)
    λ _ _ _ → ap inc^ab (sym associative)

  Group-on-G^ab : Group-on G^ab
  Group-on-G^ab = make-group squash abunit _ab*_ abinv ab*-associative
    (Coeq-elim-prop (λ _ → squash _ _) (λ _ → ap inc^ab G.inversel))
    (Coeq-elim-prop (λ _ → squash _ _) (λ _ → ap inc^ab G.inverser))
    (Coeq-elim-prop (λ _ → squash _ _) (λ _ → ap inc^ab G.idl))

  Abelianise : Group ℓ
  Abelianise = _ , Group-on-G^ab

  Abelianise-is-abelian-group : is-abelian-group Abelianise
  Abelianise-is-abelian-group = ab*-comm
```

## Universal property

This finishes the construction of _an_ abelian group from a group. To
show that this construction is correct, we'll show that it satisfies a
universal property: The map `inc^ab`{.Agda}, which we write as being
from $G \to G^{ab}$, is a group homomorphism, and furthermore, it
provides a _universal_ way of mapping from $G$ to an abelian group, in
that if $H$ is an abelian group, then a map $f : G \to H$ factors
through `inc^ab`{.Agda} in a unique way.

```agda
Abelianise-universal
  : ∀ {G : Group ℓ} → Universal-morphism G Ab→Grp
Abelianise-universal {ℓ = ℓ} {G = G} = m where
  open Cat (const! {A = Groups ℓ} G ↓ Ab→Grp)
  open Initial
  module G = Group-on (G .snd)
```

Our choice of initial object was already stated in the paragraph above
--- it's the epimorphism $q : G \to G^{ab}$, i.e., the map which we
call `inc^ab`{.Agda}.

```agda
  init : Ob
  init .↓Obj.x = tt
  init .↓Obj.y = Abelianise G , Abelianise-is-abelian-group G
  init .↓Obj.map .fst = inc^ab G
  init .↓Obj.map .snd .Group-hom.pres-⋆ x y = refl

  m : Initial
  m .bot = init
  m .has⊥ other = contr factor unique where
```

<!--
```agda
    module other = ↓Obj other
    module H = AbGrp other.y
    open Σ other.map renaming (fst to f ; snd to gh)
    open Group-hom gh
```
-->

Now suppose we have an abelian group $H$ and a map $f : G \to H$. We
factor it through $G^{ab}$ as follows: Since $f$ is a homomorphism into
an abelian group, it "respects commutativity", by which I mean that
$f(ab) = f(a)f(b) = f(b)f(a) = f(ba)$, meaning in particular that it
satisfies the requirements for mapping out of `Abelianise`{.Agda} at the
level of sets.

```agda
    factor : Hom _ other
    factor .↓Hom.α = tt
    factor .↓Hom.β .fst = Coeq-elim (λ _ → H.has-is-set) f (λ (a , b , c) → resp a b c)
      where abstract
      resp : ∀ a b c → f (a G.⋆ (b G.⋆ c)) ≡ f (a G.⋆ (c G.⋆ b))
      resp a b c =
        f (a G.⋆ (b G.⋆ c))   ≡⟨ pres-⋆ _ _ ⟩
        f a H.⋆ f (b G.⋆ c)   ≡⟨ ap (f a H.⋆_) (pres-⋆ _ _) ⟩
        f a H.⋆ (f b H.⋆ f c) ≡⟨ ap (f a H.⋆_) H.commutative ⟩
        f a H.⋆ (f c H.⋆ f b) ≡˘⟨ ap (f a H.⋆_) (pres-⋆ _ _) ⟩
        f a H.⋆ f (c G.⋆ b)   ≡˘⟨ pres-⋆ _ _ ⟩
        f (a G.⋆ (c G.⋆ b))   ∎
```

To show that the map $h : G^{ab} \to H$ induced by $f$ is a group
homomorphism, it suffices to assume that we have two honest-to-god
elements $x, y : G$, and since $h$ is exactly $f$ on generators, the
required identification $f(xy) = f(x)f(y)$ follows from $f$ being a
group homomorphism.

```agda
    factor .↓Hom.β .snd .Group-hom.pres-⋆ =
      Coeq-elim-prop₂ (λ _ _ → H.has-is-set _ _) λ x y → pres-⋆ _ _
    factor .↓Hom.sq = Forget-is-faithful refl
```

Now if $h'$ is any other map which factors $G \xepi{q} G^{ab} \xto{h'}
H$, since $G \to G^{ab}$ is an epimorphism, we must have $h = h'$.

```agda
    unique : ∀ h → factor ≡ h
    unique x = ↓Hom-path _ _ refl $ Forget-is-faithful $ funext $
      Coeq-elim-prop (λ _ → H.has-is-set _ _) λ y i → x .↓Hom.sq i .fst y
```
