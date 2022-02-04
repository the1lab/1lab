```agda
open import 1Lab.Prelude

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
  private module G = GroupOn gst
  open G
```

We define the **abelianisation** of a group $G$, $G^{ab}$. Rather than
defining it a quotient group (by the commutator subgroup $[G,G]$), we
directly define a group structure on a set-coequaliser. To emphasise the
difference between the groups and their underlying sets, we'll write
$G_0$ and $G^{ab}_0$ in the prose.

```agda
  G^ab : Type ℓ
  G^ab = coeq {A = G × G × G} (λ (x , y , z) → x ⋆ y ⋆ z)
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
  ab*-comm = Coeq-elimProp₂ (λ _ _ → squash _ _) l1
    where abstract
      l1 : ∀ x y → inc^ab (x ⋆ y) ≡ inc^ab (y ⋆ x)
      l1 x y =
        inc^ab (x ⋆ y)        ≡⟨ ap inc^ab (ap₂ _⋆_ (sym G.idˡ) refl ∙ sym G.associative) ⟩ 
        inc^ab (unit ⋆ x ⋆ y) ≡⟨ ab-comm _ _ _ ⟩ 
        inc^ab (unit ⋆ y ⋆ x) ≡⟨ ap inc^ab (G.associative ∙ ap₂ _⋆_ G.idˡ refl) ⟩ 
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
      -- TODO: Explain the trick here
      l1 : ((x , y , z) : G × G × G) 
         → inc^ab ((x ⋆ y ⋆ z) ⁻¹) ≡ inc^ab ((x ⋆ z ⋆ y) ⁻¹)
      l1 (x , y , z) =
        inc^ab ((x ⋆ y ⋆ z) ⁻¹)                             ≡⟨ ap inc^ab G.inv-comm ⟩ 
        inc^ab ((y ⋆ z) ⁻¹ ⋆ x ⁻¹)                          ≡⟨ ap inc^ab (ap₂ _⋆_ G.inv-comm refl) ⟩ 
        inc^ab ((z ⁻¹ ⋆ y ⁻¹) ⋆ x ⁻¹)                       ≡⟨⟩ 
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
        inc^ab ((y ⁻¹ ⋆ z ⁻¹) ⋆ x ⁻¹)                       ≡⟨ ap inc^ab (ap₂ _⋆_ (sym G.inv-comm) refl ) ⟩
        inc^ab ((z ⋆ y) ⁻¹ ⋆ x ⁻¹)                          ≡⟨ ap inc^ab (sym G.inv-comm) ⟩ 
        inc^ab ((x ⋆ z ⋆ y) ⁻¹)                             ∎
```

The beautiful thing is that, since the group operations on $G^{ab}$ are
all defined in terms of those of $G$, the group axioms are also
inherited from $G$!

```agda
  ab*-associative : ∀ x y z → (x ab* y) ab* z ≡ x ab* (y ab* z)
  ab*-associative = Coeq-elimProp₃ (λ _ _ _ → squash _ _) 
    λ _ _ _ → ap inc^ab (sym associative)

  GroupOn-G^ab : GroupOn G^ab
  GroupOn-G^ab = makeGroup squash abunit _ab*_ abinv ab*-associative 
    (Coeq-elimProp (λ _ → squash _ _) (λ _ → ap inc^ab G.inverseˡ)) 
    (Coeq-elimProp (λ _ → squash _ _) (λ _ → ap inc^ab G.inverseʳ)) 
    (Coeq-elimProp (λ _ → squash _ _) (λ _ → ap inc^ab G.idˡ)) 

  makeAbelian : Group ℓ
  makeAbelian = _ , GroupOn-G^ab

  isAbelian-makeAbelian : isAbelian makeAbelian
  isAbelian-makeAbelian = ab*-comm
```

## Universal property

This finishes the construction of _an_ abelian group from a group. To
show that this construction is correct, we'll show that it satisfies a
universal property: `makeAbelian`{.Agda} is left adjoint to the
inclusion from abelian groups to groups. In essence, this means that any
map from $G$ to an abelian group $G'$ factors in a unique way through
the canonical map $G \to G^{ab}$.

```agda
  makeAbelian⊣Forget 
    : (G' : Group ℓ) → isAbelian G'
    → Group[ Grp ⇒ G' ] ≃ Group[ makeAbelian ⇒ G' ]
  makeAbelian⊣Forget G' G'-ab = Iso→Equiv isom where
    module G' = GroupOn (G' .snd)
    open isGroupHom
    open isIso
```

We'll factor a given group homomorphism $G \to G'$ through $G^{ab}$
using the `fold`{.agda} function below. To map out of the
abelianisation, we must show that $f(xyz) = f(xzy)$. But $f$ is a
homomorphism into an abelian group! So we have $f(xyz) = f(x)f(y)f(z) =
f(x)f(z)f(y) = f(xzy)$.

```agda
    fold : (f : G → G' .fst) → isGroupHom Grp G' f → G^ab → G' .fst
    fold f gh = Coeq-rec G'.hasIsSet f l1 
      where abstract
        l1 : ((x , y , z) : G × G × G) → f (x ⋆ y ⋆ z) ≡ f (x ⋆ z ⋆ y)
        l1 (x , y , z) = 
          f (x ⋆ y ⋆ z)         ≡⟨ gh .pres-⋆ _ _ ⟩ 
          f x G'.⋆ f (y ⋆ z)    ≡⟨ ap₂ G'._⋆_ refl (gh .pres-⋆ _ _ ) ⟩ 
          f x G'.⋆ f y G'.⋆ f z ≡⟨ ap₂ G'._⋆_ refl (G'-ab _ _) ⟩ 
          f x G'.⋆ f z G'.⋆ f y ≡⟨ ap₂ G'._⋆_ refl (sym (gh .pres-⋆ _ _ )) ⟩ 
          f x G'.⋆ f (z ⋆ y)    ≡⟨ sym (gh .pres-⋆ _ _) ⟩ 
          f (x ⋆ z ⋆ y)         ∎
```

Now it suffices to show that `fold`{.Agda} has an inverse --- I can tell
you it has one: precomposition with the universal map $G_0 \to
G^{ab}_0$, which is a group homomorphism on the nose.

```agda
    isom : Iso _ _
    isom .fst (f , g) = fold f g , r
      where abstract
        r : isGroupHom makeAbelian G' (fold f g)
        r .pres-⋆ = Coeq-elimProp₂ (λ _ _ → G'.hasIsSet _ _) (g .pres-⋆)

    isom .snd .inv (f , g) = (f ∘ inc^ab) , r
      where abstract
        r : isGroupHom (G , gst) G' (f ∘ inc^ab)
        r .pres-⋆ x y = g .pres-⋆ _ _

    isom .snd .rinv f = 
      Σ≡Prop (λ _ → isProp-isGroupHom) 
        (funext (Coeq-elimProp (λ _ → G'.hasIsSet _ _) λ _ → refl))
    isom .snd .linv f = Σ≡Prop (λ _ → isProp-isGroupHom) refl
```