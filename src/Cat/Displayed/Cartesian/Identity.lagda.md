```agda
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Univalence.Reasoning
import Cat.Displayed.Univalence
import Cat.Displayed.Morphism
import Cat.Displayed.Reasoning as Dr
import Cat.Reasoning as Cr

module Cat.Displayed.Cartesian.Identity
  {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′)
  where
```

# Identity of Cartesian lifts

In this module, we prove that Cartesian morphisms are unique up to
_vertical_ isomorphism, which, if the displayed category is univalent
(regardless of univalence of the base), can be strengthened to show that
the type of Cartesian lifts for a given "corner" is a proposition.

<!--
```agda
private
  module B = Cr B

open Cat.Displayed.Univalence.Reasoning E
open Cat.Displayed.Univalence E
open Cat.Displayed.Morphism E
open Displayed E
open Dr E
open _≅[_]_
```
-->

We'll first observe that if we have two witnesses that $f'$ is a
Cartesian morphism over $f$, then the fact that both provide _unique_
solutions to factorisation problems imply that these must be the same
solution. Therefore, since the other components are paths, a morphism
can be Cartesian in at most one way.

```agda
module _ {a b a′ b′} (f : B.Hom a b) {f′ : Hom[ f ] a′ b′}
         (c₁ c₂ : Cartesian E f f′)
  where

  private
    module c1 = Cartesian c₁
    module c2 = Cartesian c₂

  open Cartesian

  private
    univ : ∀ {u u′} (m : B.Hom u a) (h′ : Hom[ f B.∘ m ] u′ b′)
          → c1.universal m h′ ≡ c2.universal m h′
    univ m h′ = c2.unique (c1.universal m h′) (c1.commutes m h′)

  Cartesian-is-prop : c₁ ≡ c₂
  Cartesian-is-prop i .universal m h′ = univ m h′ i
  Cartesian-is-prop i .commutes m h′ =
    is-prop→pathp (λ i → Hom[ f B.∘ m ]-set _ b′ (f′ ∘′ univ m h′ i) h′)
      (c1.commutes m h′)
      (c2.commutes m h′) i
  Cartesian-is-prop i .unique {h′ = h′} m′ p =
    is-prop→pathp (λ i → Hom[ _ ]-set _ a′ m′ (univ _ h′ i))
      (c1.unique m′ p) (c2.unique m′ p) i
```

Unsurprisingly, that's the easier half of the proof. Suppose that $f_1$
and $f_2$ are both Cartesian morphisms over $f$, as in the diagram
below.

~~~{.quiver .tall-2}
\[\begin{tikzcd}
  {a_2'} \\
  & {a_1'} && {b'} \\
  \\
  a & a && b
  \arrow["{f_2}", curve={height=-12pt}, from=1-1, to=2-4]
  \arrow["{f_1}", from=2-2, to=2-4]
  \arrow["f"', from=4-2, to=4-4]
  \arrow[from=2-4, to=4-4]
  \arrow[lies over, from=2-2, to=4-2]
  \arrow[lies over, from=1-1, to=4-1]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=4-4]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=2-2, to=4-4]
  \arrow[Rightarrow, no head, from=4-1, to=4-2]
\end{tikzcd}\]
~~~

<!--
```agda
module _ {a b a₁′ a₂′ b′} (f : B.Hom a b) {f₁′ : Hom[ f ] a₁′ b′}
         {f₂′ : Hom[ f ] a₂′ b′} (c₁ : Cartesian E f f₁′) (c₂ : Cartesian E f f₂′)
  where
  private
    module c1 = Cartesian c₁
    module c2 = Cartesian c₂
```
-->

Since $f_1$ and $f_2$ are both Cartesian morphisms, we can factor $f_2$
through $a_1'$ by a map $g$, and conversely, $f_1$ through $a_2'$ by
$h$, so that we have $f_2gh = f_1h = f_2$, and $gh$ is a factorisation
of $f_2$ through $a'_2$, its own domain; but, of course, $f_2$ also
factors through its own domain by the identity map! Since $f_2$ is
Cartesian, these factorisations must be the same, hence $gh = \id{id}$.
A symmetric argument shows that $hg$ is also the identity, so $g : a_1'
\cong a_2'$.

```agda
  cartesian-domain-unique : a₁′ ≅↓ a₂′
  cartesian-domain-unique = go where
    to   = c2.universal′ (B.idr f) f₁′
    from = c1.universal′ (B.idr f) f₂′
```

<details>
<summary>A minor formalisation quibble is that working with displayed
morphisms is never easy, so showing $f_2gh = f_2$ and $f_1hg = f_1$ is
more involved than it has any right to be.</summary>

```agda
    lemma₁ : f₁′ ∘′ from ∘′ to ≡ hom[ B.intror (B.idr B.id) ] f₁′
    lemma₁ = shiftr (ap (f B.∘_) (B.idr B.id)) (pulll′ (B.idr f) (c1.commutesp (B.idr f) f₂′))
          ·· ap hom[] (shiftr (B.idr f) (c2.commutesp (B.idr f) f₁′))
          ·· hom[]-∙ _ _ ∙ reindex _ (B.intror (B.idr B.id))

    lemma₂ : f₂′ ∘′ to ∘′ from ≡ hom[ B.intror (B.idr B.id) ] f₂′
    lemma₂ = shiftr (ap (f B.∘_) (B.idr B.id)) (pulll′ (B.idr f) (c2.commutesp (B.idr f) f₁′))
          ·· ap hom[] (shiftr (B.idr f) (c1.commutesp (B.idr f) f₂′))
          ·· hom[]-∙ _ _ ∙ reindex _ (B.intror (B.idr B.id))

    go : a₁′ ≅↓ a₂′
    go .to′ = to
    go .from′ = from
    go .inverses′ .Inverses[_].invr′ =
      c1.uniquep₂ (sym _) _ _ _ _ (to-pathp⁻ lemma₁) (idr′ f₁′)
    go .inverses′ .Inverses[_].invl′ =
      c2.uniquep₂ (sym _) _ _ _ _ (to-pathp⁻ lemma₂) (idr′ f₂′)
```
</details>

By construction, our isomorphism sends $f_1$ to $f_2$!

```agda
  cartesian-map-uniquep
    : (p : f B.∘ B.id ≡ f) → f₁′ ∘′ cartesian-domain-unique .from′ ≡[ p ] f₂′
  cartesian-map-uniquep p = to-pathp⁻ $
    c1.commutes B.id _ ∙ reindex (sym (B.idr f)) (sym p)
```

<!--
```agda
module _ {a b b′} (f : B.Hom a b) (l1 l2 : Cartesian-lift E f b′) where
  open Cartesian-lift

  private
    module l1 = Cartesian-lift l1
    module l2 = Cartesian-lift l2
```
-->

Having established that being Cartesian is a property of a morphism,
that any pair of Cartesian lifts for the same $f : a \to b$ and $b'
\liesover b$ have isomorphic domains, and that this isomorphism sends
the first morphism to the second, all that remains is putting this
together into a tidy proof: If $\ca{E}$ is univalent, the space of
Cartesian lifts for $(f, b')$ is a proposition.

```agda
  Cartesian-lift-is-prop : is-category-displayed → l1 ≡ l2
  Cartesian-lift-is-prop e-cat = p where
    im = cartesian-domain-unique f l1.cartesian l2.cartesian

    obp : l1.x′ ≡ l2.x′
    obp = ≅↓-identity-system e-cat .to-path im

    pres : PathP (λ i → Hom[ f ] (obp i) b′) l1.lifting l2.lifting
    pres = Hom[]-pathp-refll-iso e-cat (B.idr f) im l1.lifting l2.lifting
      (cartesian-map-uniquep f l1.cartesian l2.cartesian (B.idr f))

    p : l1 ≡ l2
    p i .x′        = obp i
    p i .lifting   = pres i
    p i .cartesian =
      is-prop→pathp (λ i → Cartesian-is-prop {a′ = obp i} f {f′ = pres i})
        l1.cartesian l2.cartesian i
```
