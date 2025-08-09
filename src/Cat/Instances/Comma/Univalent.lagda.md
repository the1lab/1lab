<!--
```agda
open import Cat.Instances.Comma
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning
```
-->

```agda
module
  Cat.Instances.Comma.Univalent
  {xo xℓ yo yℓ zo zℓ}
  {X : Precategory xo xℓ} {Y : Precategory yo yℓ} {Z : Precategory zo zℓ}
  (F : Functor Y X) (G : Functor Z X)
  (xuniv : is-category X)
  (yuniv : is-category Y)
  (zuniv : is-category Z)
  where
```

<!--
```agda
private
  module X = Cat.Reasoning X
  module Y = Cat.Reasoning Y
  module Z = Cat.Reasoning Z
  module F = Func F
  module G = Func G
  module F↓G = Cat.Reasoning (F ↓ G)

open ↓Obj
open ↓Hom
```
-->

# Comma categories preserve univalence {defines="univalence-of-comma-category"}

**Theorem**. Let $\cY \xto{F} \cX \xot{G} \cZ$ be a [cospan] of
functors between three [[univalent categories]]. Then the comma category
$F \downarrow G$ is also univalent.

[cospan]: Cat.Instances.Shape.Cospan.html

It suffices to establish that, given an isomorphism $f : o \cong o'$ in
$F \downarrow G$, one gets an identification $\^f : o \equiv o'$, over
which $f$ is the identity map. Since $\cY$ and $\cZ$ are both
univalent categories, we get (from the components $f_\alpha$, $f_\beta$
of $f$) identifications $\^f_\alpha : o_x \equiv o'_x$ and $\^f_\beta :
o_y \equiv o'_y$.

```agda
Comma-is-category : is-category (F ↓ G)
Comma-is-category = record { to-path = objs ; to-path-over = maps } where
  module _ {ob ob'} (isom : F↓G.Isomorphism ob ob') where
    module isom = F↓G._≅_ isom

    x-is-x : ob .dom Y.≅ ob' .dom
    y-is-y : ob .cod Z.≅ ob' .cod

    x-is-x = Y.make-iso (isom.to .top) (isom.from .top) (ap top isom.invl) (ap top isom.invr)
    y-is-y = Z.make-iso (isom.to .bot) (isom.from .bot) (ap bot isom.invl) (ap bot isom.invr)
```

Observe that, over $\^f_\alpha$ and $\^f_\beta$, the map components
$o_m$ and $o'_m$ are equal (we say "equal" rather than "identified"
because Hom-sets are sets). This follows by standard abstract nonsense:
in particular, functors between univalent categories respect
isomorphisms in a strong sense (`F-map-path`{.Agda}).

This lets us reduce statements about $F$ and $G$'s object-part action on
paths to statements about their morphism parts $F_1$, $G_1$ on the
components of the isomorphisms $f_\alpha$ and $f_\beta$. But then we
have

$$
\begin{split}
G_1(f_\beta) o_m F_1(f_\alpha\inv) &= o'_m F_1(f_\alpha) F_1(f_\alpha\inv) \\
  &= o'_m F_1(f_\alpha f_\alpha\inv) \\
  &= o'_m\text{,}
\end{split}
$$

so over these isomorphisms the map parts become equal, thus establishing
an identification $o \equiv o'$.

```agda
    objs : ob ≡ ob'
    objs i .dom = yuniv .to-path x-is-x i
    objs i .cod = zuniv .to-path y-is-y i
    objs i .map = lemma' i where
      lemma' : PathP (λ i → X.Hom (F.₀ (objs i .dom)) (G.₀ (objs i .cod)))
                (ob .map) (ob' .map)
      lemma' = transport
        (λ i → PathP (λ j → X.Hom (F-map-path F yuniv xuniv x-is-x (~ i) j)
                                  (F-map-path G zuniv xuniv y-is-y (~ i) j))
                    (ob .map) (ob' .map)) $
        Univalent.Hom-pathp-iso xuniv $
          X.pulll   (sym (isom.to .com)) ∙
          X.cancelr (F.annihilate (ap top isom.invl))
```

It still remains to show that, over this identification, the isomorphism
$f$ is equal to the identity function. But this is simply a matter of
pushing the identifications down to reach the "leaf" morphisms.

```agda
    maps : PathP (λ i → ob F↓G.≅ objs i) _ isom
    maps = F↓G.≅-pathp _ _
      (↓Hom-pathp _ _ (Univalent.Hom-pathp-reflr-iso yuniv (Y.idr _))
                      (Univalent.Hom-pathp-reflr-iso zuniv (Z.idr _)))
```
