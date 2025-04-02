---
description: |
  Joint cartesian families
---
<!--
```agda
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Cartesian
import Cat.Displayed.Reasoning
import Cat.Displayed.Morphism
import Cat.Reasoning
```
-->
```agda
module Cat.Displayed.Cartesian.Joint
  {o ℓ o' ℓ'}
  {B : Precategory o ℓ} (E : Displayed B o' ℓ')
  where
```

<!--
```agda
open Cat.Displayed.Cartesian E
open Cat.Displayed.Reasoning E
open Cat.Displayed.Morphism E
open Cat.Reasoning B
open Displayed E
```
-->

# Jointly cartesian families

:::{.definition #jointly-cartesian-family}
A family of morphisms $f_{i} : \cE_{u_i}(A', B'_{i})$ over $u_{i} : \cB(A, B_{i})$
is **jointly cartesian** if it satisfies a familial version of the universal
property of a [[cartesian]] map.
:::

```agda
record is-jointly-cartesian
  {ℓi} {Ix : Type ℓi}
  {a : Ob} {bᵢ : Ix → Ob}
  {a' : Ob[ a ]} {bᵢ' : (ix : Ix) → Ob[ bᵢ ix ]}
  (uᵢ : (ix : Ix) → Hom a (bᵢ ix))
  (fᵢ : (ix : Ix) → Hom[ uᵢ ix ] a' (bᵢ' ix))
  : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ' ⊔ ℓi) where
```

Explicitly, a family $f_{i}$ is jointly cartesian if for every map
$v : \cB(X, A)$ and family of morphisms $h_{i} : \cE_{u_i \circ v}(X', B_{i}')$,
there exists a unique universal map $\langle v , h_{i} \rangle : \cE_{v}(X', A')$
such that $f_{i} \circ \langle v , h_{i} \rangle = h_{i}$.

~~~{.quiver}
\begin{tikzcd}
  {X'} \\
  && {A'} && {B_i'} \\
  X \\
  && A && {B_i}
  \arrow["{\exists!}"{description}, dashed, from=1-1, to=2-3]
  \arrow["{h_i}"{description}, curve={height=-12pt}, from=1-1, to=2-5]
  \arrow[from=1-1, to=3-1]
  \arrow["{f_i}"{description}, from=2-3, to=2-5]
  \arrow[from=2-3, to=4-3]
  \arrow[from=2-5, to=4-5]
  \arrow["v"{description}, from=3-1, to=4-3]
  \arrow["{u_i \circ v}"{description, pos=0.7}, curve={height=-12pt}, from=3-1, to=4-5]
  \arrow["{u_i}"{description}, from=4-3, to=4-5]
\end{tikzcd}
~~~

```agda
  no-eta-equality
  field
    universal
      : ∀ {x x'}
      → (v : Hom x a)
      → (∀ ix → Hom[ uᵢ ix ∘ v ] x' (bᵢ' ix))
      → Hom[ v ] x' a'
    commutes
      : ∀ {x x'}
      → (v : Hom x a)
      → (hᵢ : ∀ ix → Hom[ uᵢ ix ∘ v ] x' (bᵢ' ix))
      → ∀ ix → fᵢ ix ∘' universal v hᵢ ≡ hᵢ ix
    unique
      : ∀ {x x'}
      → {v : Hom x a}
      → {hᵢ : ∀ ix → Hom[ uᵢ ix ∘ v ] x' (bᵢ' ix)}
      → (other : Hom[ v ] x' a')
      → (∀ ix → fᵢ ix ∘' other ≡ hᵢ ix)
      → other ≡ universal v hᵢ
```

<!--
```agda
  universal'
      : ∀ {x x'}
      → {v : Hom x a} {wᵢ : ∀ ix → Hom x (bᵢ ix)}
      → (p : ∀ ix → uᵢ ix ∘ v ≡ wᵢ ix)
      → (∀ ix → Hom[ wᵢ ix ] x' (bᵢ' ix))
      → Hom[ v ] x' a'
  universal' {v = v} p hᵢ =
    universal v λ ix → hom[ p ix ]⁻ (hᵢ ix)

  commutesp
    : ∀ {x x'}
    → {v : Hom x a} {wᵢ : ∀ ix → Hom x (bᵢ ix)}
    → (p : ∀ ix → uᵢ ix ∘ v ≡ wᵢ ix)
    → (hᵢ : ∀ ix → Hom[ wᵢ ix ] x' (bᵢ' ix))
    → ∀ ix → fᵢ ix ∘' universal' p hᵢ ≡[ p ix ] hᵢ ix
  commutesp p hᵢ ix =
    to-pathp⁻ (commutes _ (λ ix → hom[ p ix ]⁻ (hᵢ ix)) ix)

  universalp
    : ∀ {x x'}
    → {v₁ v₂ : Hom x a} {wᵢ : ∀ ix → Hom x (bᵢ ix)}
    → (p : ∀ ix → uᵢ ix ∘ v₁ ≡ wᵢ ix) (q : v₁ ≡ v₂) (r : ∀ ix → uᵢ ix ∘ v₂ ≡ wᵢ ix)
    → (hᵢ : ∀ ix → Hom[ wᵢ ix ] x' (bᵢ' ix))
    → universal' p hᵢ ≡[ q ] universal' r hᵢ
  universalp p q r hᵢ =
    apd (λ i ϕ → universal' ϕ hᵢ) prop!

  uniquep
    : ∀ {x x'}
    → {v₁ v₂ : Hom x a} {wᵢ : ∀ ix → Hom x (bᵢ ix)}
    → (p : ∀ ix → uᵢ ix ∘ v₁ ≡ wᵢ ix) (q : v₁ ≡ v₂) (r : ∀ ix → uᵢ ix ∘ v₂ ≡ wᵢ ix)
    → {hᵢ : ∀ ix → Hom[ wᵢ ix ] x' (bᵢ' ix)}
    → (other : Hom[ v₁ ] x' a')
    → (∀ ix → fᵢ ix ∘' other ≡[ p ix ] hᵢ ix)
    → other ≡[ q ] universal' r hᵢ
  uniquep p q r {hᵢ} other s =
    to-pathp⁻ (unique other (λ ix → from-pathp⁻ (s ix)) ∙ from-pathp⁻ (universalp p q r hᵢ))

  uniquep₂
    : ∀ {x x'}
    → {v₁ v₂ : Hom x a} {wᵢ : ∀ ix → Hom x (bᵢ ix)}
    → (p : ∀ ix → uᵢ ix ∘ v₁ ≡ wᵢ ix) (q : v₁ ≡ v₂) (r : ∀ ix → uᵢ ix ∘ v₂ ≡ wᵢ ix)
    → {hᵢ : ∀ ix → Hom[ wᵢ ix ] x' (bᵢ' ix)}
    → (other₁ : Hom[ v₁ ] x' a')
    → (other₂ : Hom[ v₂ ] x' a')
    → (∀ ix → fᵢ ix ∘' other₁ ≡[ p ix ] hᵢ ix)
    → (∀ ix → fᵢ ix ∘' other₂ ≡[ r ix ] hᵢ ix)
    → other₁ ≡[ q ] other₂
  uniquep₂ p q r {hᵢ = hᵢ} other₁ other₂ α β =
    cast[] $
      other₁          ≡[]⟨ uniquep p refl p other₁ α ⟩
      universal' p hᵢ ≡[]⟨ symP (uniquep r (sym q) p other₂ β) ⟩
      other₂          ∎
```
-->

<!--
```agda
private variable
  ℓi : Level
  Ix Ix' : Type ℓi
  a b c : Ob
  bᵢ cᵢ : Ix → Ob
  a' b' c' : Ob[ a ]
  bᵢ' cᵢ' : (ix : Ix) → Ob[ bᵢ ix ]
  u v : Hom a b
  uᵢ vᵢ : ∀ (ix : Ix) → Hom a (bᵢ ix)
  f g : Hom[ u ] a' b'
  fᵢ fᵢ' gᵢ : ∀ (ix : Ix) → Hom[ uᵢ ix ] a' (bᵢ' ix)
```
-->

::: warning
Some sources ([@Adamek-Herrlich-Strecker:2004], [@Dubuc-Espanol:2006])
refer to jointly cartesian families as "initial families". We opt to
avoid this terminology, as it leads to unnecessary conflicts with
[[initial objects]].
:::

At first glance, jointly cartesian families appear very similar to cartesian maps.
However, replacing a single map with a family of maps has some very strong
consequences: cartesian morphisms typically behave as witnesses to [[base change]]
operations, whereas jointly cartesian families act more like a combination
of base-change maps and projections out of a product. This can be seen
by studying prototypical examples of jointly cartesian families:

- If we view the category of topological spaces as a [[displayed category]],
then the jointly cartesian maps are precisely the initial topologies.
- Jointly cartesian maps in the [[subobject fibration]] of $\Sets$ are
arise from pulling back a family of subsets $A_{i} \subset Y_{i}$ along
maps $u_{i} : X \to Y_{i}$, and then taking their intersection.

## Relating cartesian maps and jointly cartesian families

Every [[cartesian map]] can be regarded as a jointly cartesian family
over a contractible type.

```agda
cartesian→jointly-cartesian
  : is-contr Ix
  → is-cartesian u f
  → is-jointly-cartesian {Ix = Ix} (λ _ → u) (λ _ → f)
cartesian→jointly-cartesian {u = u} {f = f} ix-contr f-cart = f-joint-cart where
  module f = is-cartesian f-cart
  open is-jointly-cartesian

  f-joint-cart : is-jointly-cartesian (λ _ → u) (λ _ → f)
  f-joint-cart .universal v hᵢ =
    f.universal v (hᵢ (ix-contr .centre))
  f-joint-cart .commutes v hᵢ ix =
    f ∘' f.universal v (hᵢ (ix-contr .centre)) ≡⟨ f.commutes v (hᵢ (ix-contr .centre)) ⟩
    hᵢ (ix-contr .centre)                      ≡⟨ ap hᵢ (ix-contr .paths ix) ⟩
    hᵢ ix                                      ∎
  f-joint-cart .unique other p =
    f.unique other (p (ix-contr .centre))
```

Conversely, if the constant family $\lambda i\. f$ is a jointly cartesian
$I$-indexed family over a merely inhabited type $I$, then $f$ is cartesian.

```agda
const-jointly-cartesian→cartesian
  : ∥ Ix ∥
  → is-jointly-cartesian {Ix = Ix} (λ _ → u) (λ _ → f)
  → is-cartesian u f
const-jointly-cartesian→cartesian {Ix = Ix} {u = u} {f = f} ∥ix∥ f-joint-cart =
  rec! f-cart ∥ix∥
  where
    module f = is-jointly-cartesian f-joint-cart
    open is-cartesian

    f-cart : Ix → is-cartesian u f
    f-cart ix .universal v h = f.universal v λ _ → h
    f-cart ix .commutes v h = f.commutes v (λ _ → h) ix
    f-cart ix .unique other p = f.unique other (λ _ → p)
```

Jointly cartesian families over empty types act more like discrete objects
than pullbacks, as the space of maps into the shared domain of the family
is unique for any $v : \cE{B}(X, A)$ and $X' \liesover X$. In the displayed
category of topological spaces, such maps are precisely the discrete spaces.

```agda
empty-jointly-cartesian→discrete
  : ∀ {uᵢ : (ix : Ix) → Hom a (bᵢ ix)} {fᵢ : (ix : Ix) → Hom[ uᵢ ix ] a' (bᵢ' ix)}
  → ¬ Ix
  → is-jointly-cartesian uᵢ fᵢ
  → ∀ {x} (v : Hom x a) → (x' : Ob[ x ]) → is-contr (Hom[ v ] x' a')
empty-jointly-cartesian→discrete ¬ix fᵢ-cart v x' =
  contr (fᵢ.universal v λ ix → absurd (¬ix ix)) λ other →
    sym (fᵢ.unique other λ ix → absurd (¬ix ix))
  where
    module fᵢ = is-jointly-cartesian fᵢ-cart
```

## Closure properties of jointly cartesian families

Jointly cartesian families are closed under precomposition with [[cartesian maps]].

```agda
jointly-cartesian-cartesian-∘
  : is-jointly-cartesian uᵢ fᵢ
  → is-cartesian v g
  → is-jointly-cartesian (λ ix → uᵢ ix ∘ v) (λ ix → fᵢ ix ∘' g)
jointly-cartesian-cartesian-∘ {uᵢ = uᵢ} {fᵢ = fᵢ} {v = v} {g = g} fᵢ-cart g-cart = fᵢ∘g-cart
  where
    module fᵢ = is-jointly-cartesian fᵢ-cart
    module g = is-cartesian g-cart
    open is-jointly-cartesian

    fᵢ∘g-cart : is-jointly-cartesian (λ ix → uᵢ ix ∘ v) (λ ix → fᵢ ix ∘' g)
    fᵢ∘g-cart .universal w hᵢ =
      g.universal w $ fᵢ.universal' (λ ix → assoc (uᵢ ix) v w) hᵢ
    fᵢ∘g-cart .commutes w hᵢ ix =
      cast[] $
        (fᵢ ix ∘' g) ∘' universal fᵢ∘g-cart w hᵢ             ≡[]⟨ pullr[] _ (g.commutes w _) ⟩
        fᵢ ix ∘' fᵢ.universal' (λ ix → assoc (uᵢ ix) v w) hᵢ ≡[]⟨ fᵢ.commutesp _ hᵢ ix ⟩
        hᵢ ix                                                ∎
    fᵢ∘g-cart .unique other pᵢ =
      g.unique other $
      fᵢ.uniquep _ _ _ (g ∘' other) λ ix →
        assoc' (fᵢ ix) g other ∙[] pᵢ ix
```

Similarly, if $f_{i}$ is a family of maps with each $f_{i}$ individually
cartesian, and $g_{i}$ is jointly cartesian, then the composite $f_{i} \circ g_{i}$
is jointly cartesian.

```agda
pointwise-cartesian-jointly-cartesian-∘
  : (∀ ix → is-cartesian (uᵢ ix) (fᵢ ix))
  → is-jointly-cartesian vᵢ gᵢ
  → is-jointly-cartesian (λ ix → uᵢ ix ∘ vᵢ ix) (λ ix → fᵢ ix ∘' gᵢ ix)
pointwise-cartesian-jointly-cartesian-∘
  {uᵢ = uᵢ} {fᵢ = fᵢ} {vᵢ = vᵢ} {gᵢ = gᵢ} fᵢ-cart gᵢ-cart = fᵢ∘gᵢ-cart where
  module fᵢ ix = is-cartesian (fᵢ-cart ix)
  module gᵢ = is-jointly-cartesian gᵢ-cart
  open is-jointly-cartesian

  fᵢ∘gᵢ-cart : is-jointly-cartesian (λ ix → uᵢ ix ∘ vᵢ ix) (λ ix → fᵢ ix ∘' gᵢ ix)
  fᵢ∘gᵢ-cart .universal v hᵢ =
    gᵢ.universal v λ ix → fᵢ.universal' ix (assoc (uᵢ ix) (vᵢ ix) v) (hᵢ ix)
  fᵢ∘gᵢ-cart .commutes v hᵢ ix =
    cast[] $
      (fᵢ ix ∘' gᵢ ix) ∘' gᵢ.universal v (λ ix → fᵢ.universal' ix _ (hᵢ ix)) ≡[]⟨ pullr[] refl (gᵢ.commutes v _ ix) ⟩
      fᵢ ix ∘' fᵢ.universal' ix _ (hᵢ ix)                                    ≡[]⟨ fᵢ.commutesp ix (assoc (uᵢ ix) (vᵢ ix) v) (hᵢ ix) ⟩
      hᵢ ix                                                                  ∎
  fᵢ∘gᵢ-cart .unique other p =
    gᵢ.unique other λ ix →
    fᵢ.uniquep ix _ _ _ (gᵢ ix ∘' other)
      (assoc' (fᵢ ix) (gᵢ ix) other ∙[] p ix)
```

Like their non-familial counterparts, jointly cartesian maps are stable
under vertical retractions.

```agda
jointly-cartesian-vertical-retraction-stable
  : ∀ {fᵢ : ∀ (ix : Ix) → Hom[ uᵢ ix ] a' (cᵢ' ix)}
  → {fᵢ' : ∀ (ix : Ix) → Hom[ uᵢ ix ] b' (cᵢ' ix)}
  → {ϕ : Hom[ id ] a' b'}
  → is-jointly-cartesian uᵢ fᵢ
  → has-section↓ ϕ
  → (∀ ix → fᵢ' ix ∘' ϕ ≡[ idr _ ] fᵢ ix)
  → is-jointly-cartesian uᵢ fᵢ'
```

<!--
```agda
_ = cartesian-vertical-retraction-stable
```
-->

<details>
<summary>The proof is essentially the same as the `non-joint case`{.Agda ident=cartesian-vertical-retraction-stable},
so we omit the details.
</summary>
```agda
jointly-cartesian-vertical-retraction-stable
  {uᵢ = uᵢ} {fᵢ = fᵢ} {fᵢ' = fᵢ'} {ϕ = ϕ} fᵢ-cart ϕ-sect factor = fᵢ'-cart
  where
    module fᵢ = is-jointly-cartesian fᵢ-cart
    module ϕ = has-section[_] ϕ-sect

    fᵢ'-cart : is-jointly-cartesian uᵢ fᵢ'
    fᵢ'-cart .is-jointly-cartesian.universal v hᵢ =
      hom[ idl v ] (ϕ ∘' fᵢ.universal v hᵢ)
    fᵢ'-cart .is-jointly-cartesian.commutes v hᵢ ix =
      cast[] $
        fᵢ' ix ∘' hom[] (ϕ ∘' fᵢ.universal v hᵢ) ≡[]⟨ unwrapr (idl v) ⟩
        fᵢ' ix ∘' ϕ ∘' fᵢ.universal v hᵢ         ≡[]⟨ pulll[] (idr (uᵢ ix)) (factor ix) ⟩
        fᵢ ix ∘' fᵢ.universal v hᵢ               ≡[]⟨ fᵢ.commutes v hᵢ ix ⟩
        hᵢ ix ∎
    fᵢ'-cart .is-jointly-cartesian.unique {v = v} {hᵢ = hᵢ} other p =
      cast[] $
        other                                 ≡[]⟨ introl[] _ ϕ.is-section' ⟩
        (ϕ ∘' ϕ.section') ∘' other            ≡[]⟨ pullr[] _ (wrap (idl v) ∙[] fᵢ.unique _ unique-lemma) ⟩
        ϕ ∘' fᵢ.universal v hᵢ                ≡[]⟨ wrap (idl v) ⟩
        hom[ idl v ] (ϕ ∘' fᵢ.universal v hᵢ) ∎

      where
        unique-lemma : ∀ ix → fᵢ ix ∘' hom[ idl v ] (ϕ.section' ∘' other) ≡ hᵢ ix
        unique-lemma ix =
          cast[] $
            fᵢ ix ∘' hom[ idl v ] (ϕ.section' ∘' other) ≡[]⟨ unwrapr (idl v) ⟩
            fᵢ ix ∘' ϕ.section' ∘' other                ≡[]⟨ pulll[] _ (symP (pre-section[] ϕ-sect (factor ix))) ⟩
            fᵢ' ix ∘' other                             ≡[]⟨ p ix ⟩
            hᵢ ix                                       ∎
```
</details>


## Cancellation properties of jointly cartesian families

Every jointly cartesian family is a [[weakly monic family]].

```agda
jointly-cartesian→jointly-weak-monic
  : is-jointly-cartesian uᵢ fᵢ
  → is-jointly-weak-monic fᵢ
jointly-cartesian→jointly-weak-monic {fᵢ = fᵢ} fᵢ-cart {g = w} g h p p' =
  fᵢ.uniquep₂ (λ _ → ap₂ _∘_ refl p) p (λ _ → refl) g h p' (λ _ → refl)
  where module fᵢ = is-jointly-cartesian fᵢ-cart
```

If $f_{i} \circ g_{i}$ is jointly cartesian, and each $f_{i}$ is
[[weakly monic]], then $g_{i}$ must be jointly cartesian.

```agda
jointly-cartesian-pointwise-weak-monic-cancell
  : (∀ ix → is-weak-monic (fᵢ ix))
  → is-jointly-cartesian (λ ix → uᵢ ix ∘ vᵢ ix) (λ ix → fᵢ ix ∘' gᵢ ix)
  → is-jointly-cartesian vᵢ gᵢ
jointly-cartesian-pointwise-weak-monic-cancell
  {uᵢ = uᵢ} {fᵢ = fᵢ} {vᵢ = vᵢ} {gᵢ = gᵢ} fᵢ-weak-monic fᵢ∘gᵢ-cart = gᵢ-cart
  where
    module fᵢ∘gᵢ = is-jointly-cartesian fᵢ∘gᵢ-cart
    open is-jointly-cartesian

    gᵢ-cart : is-jointly-cartesian vᵢ gᵢ
    gᵢ-cart .universal w hᵢ =
      fᵢ∘gᵢ.universal' (λ ix → sym (assoc (uᵢ ix) (vᵢ ix) w))
        (λ ix → fᵢ ix ∘' hᵢ ix)
    gᵢ-cart .commutes w hᵢ ix =
      fᵢ-weak-monic ix _ _ refl $
      cast[] $
        fᵢ ix ∘' gᵢ ix ∘' fᵢ∘gᵢ.universal' _ (λ ix → fᵢ ix ∘' hᵢ ix)   ≡[]⟨ assoc' _ _  _ ⟩
        (fᵢ ix ∘' gᵢ ix) ∘' fᵢ∘gᵢ.universal' _ (λ ix → fᵢ ix ∘' hᵢ ix) ≡[]⟨ fᵢ∘gᵢ.commutesp _ _ ix ⟩
        fᵢ ix ∘' hᵢ ix                                                 ∎
    gᵢ-cart .unique other p =
      fᵢ∘gᵢ.uniquep _ _ _ other (λ ix → pullr[] _ (p ix))
```

We can sharpen the previous result when $g_{i}$ is a constant family.
In particular, if $f_{i} \circ g$ is jointly cartesian, and $f_{i}$ is a
[[jointly weak monic family]], then $g$ must be cartesian.

```agda
jointly-cartesian-jointly-weak-monic-cancell
  : is-jointly-weak-monic fᵢ
  → is-jointly-cartesian (λ ix → uᵢ ix ∘ v) (λ ix → fᵢ ix ∘' g)
  → is-cartesian v g
jointly-cartesian-jointly-weak-monic-cancell
  {uᵢ = uᵢ} {fᵢ = fᵢ} {v = v} {g = g} fᵢ-weak-monic fᵢ∘g-cart = g-cart
  where
    module fᵢ∘g = is-jointly-cartesian fᵢ∘g-cart
    open is-cartesian

    g-cart : is-cartesian v g
    g-cart .universal w h =
      fᵢ∘g.universal' (λ ix → sym (assoc (uᵢ ix) v w)) (λ ix → fᵢ ix ∘' h)
    g-cart .commutes w h =
      fᵢ-weak-monic _ _ refl λ ix →
      cast[] $
        fᵢ ix ∘' g ∘' fᵢ∘g.universal' _ (λ ix → fᵢ ix ∘' h)   ≡[]⟨ assoc' _ _ _ ⟩
        (fᵢ ix ∘' g) ∘' fᵢ∘g.universal' _ (λ ix → fᵢ ix ∘' h) ≡[]⟨ fᵢ∘g.commutesp _ _ ix ⟩
        fᵢ ix ∘' h                                            ∎
    g-cart .unique other p =
      fᵢ∘g.uniquep _ _ _ other (λ ix → pullr[] _ p)
```

As corollaries, we get a pair of cancellation properties for jointly
cartesian families.

```agda
jointly-cartesian-pointwise-cartesian-cancell
  : (∀ ix → is-cartesian (uᵢ ix) (fᵢ ix))
  → is-jointly-cartesian (λ ix → uᵢ ix ∘ vᵢ ix) (λ ix → fᵢ ix ∘' gᵢ ix)
  → is-jointly-cartesian vᵢ gᵢ
jointly-cartesian-pointwise-cartesian-cancell fᵢ-cart fᵢ∘gᵢ-cart =
  jointly-cartesian-pointwise-weak-monic-cancell
    (λ ix → cartesian→weak-monic (fᵢ-cart ix))
    fᵢ∘gᵢ-cart

jointly-cartesian-cartesian-cancell
  : is-jointly-cartesian uᵢ fᵢ
  → is-jointly-cartesian (λ ix → uᵢ ix ∘ v) (λ ix → fᵢ ix ∘' g)
  → is-cartesian v g
jointly-cartesian-cartesian-cancell fᵢ-cart fᵢ∘g-cart =
  jointly-cartesian-jointly-weak-monic-cancell
    (jointly-cartesian→jointly-weak-monic fᵢ-cart)
    fᵢ∘g-cart
```

## Universal properties

Jointly cartesian families have an alternative presentation of their
universal property: a family $f_{i} : \cE_{u_i}(A', B_{i}')$ is jointly
cartesian if and only if the joint postcomposition map

$$h \mapsto \lambda i.\; f_{i} \circ h$$

is an [[equivalence]].

```agda
postcompose-equiv→jointly-cartesian
  : {uᵢ : ∀ ix → Hom a (bᵢ ix)}
  → (fᵢ : ∀ ix → Hom[ uᵢ ix ] a' (bᵢ' ix))
  → (∀ {x} (v : Hom x a) → (x' : Ob[ x ])
    → is-equiv {B = ∀ ix → Hom[ uᵢ ix ∘ v ] x' (bᵢ' ix)} (λ h ix → fᵢ ix ∘' h))
  → is-jointly-cartesian uᵢ fᵢ

jointly-cartesian→postcompose-equiv
  : {uᵢ : ∀ ix → Hom a (bᵢ ix)}
  → {fᵢ : ∀ ix → Hom[ uᵢ ix ] a' (bᵢ' ix)}
  → is-jointly-cartesian uᵢ fᵢ
  → ∀ {x} (v : Hom x a) → (x' : Ob[ x ])
  → is-equiv {B = ∀ ix → Hom[ uᵢ ix ∘ v ] x' (bᵢ' ix)} (λ h ix → fᵢ ix ∘' h)
```

<details>
<summary>The proofs are just shuffling about data, so we shall skip
over the details.
</summary>
```agda
postcompose-equiv→jointly-cartesian {a = a} {uᵢ = uᵢ} fᵢ eqv = fᵢ-cart where
  module eqv {x} {v : Hom x a} {x' : Ob[ x ]} = Equiv (_ , eqv v x')
  open is-jointly-cartesian

  fᵢ-cart : is-jointly-cartesian uᵢ fᵢ
  fᵢ-cart .universal v hᵢ =
    eqv.from hᵢ
  fᵢ-cart .commutes v hᵢ ix =
    eqv.ε hᵢ ·ₚ ix
  fᵢ-cart .unique {hᵢ = hᵢ} other p =
    sym (eqv.η other) ∙ ap eqv.from (ext p)

jointly-cartesian→postcompose-equiv {uᵢ = uᵢ} {fᵢ = fᵢ} fᵢ-cart v x' .is-eqv hᵢ =
  contr (fᵢ.universal v hᵢ , ext (fᵢ.commutes v hᵢ)) λ fib →
    Σ-prop-pathp! (sym (fᵢ.unique (fib .fst) (λ ix → fib .snd ·ₚ ix)))
  where
    module fᵢ = is-jointly-cartesian fᵢ-cart
```
</details>

## Jointly cartesian lifts

:::{.definition #jointly-cartesian-lift}
A **jointly cartesian lift** of a family of objects $Y_{i}' \liesover Y_{i}$
along a family of maps $u_{i} : \cB(X, Y_{i})$ is an object
$\bigcap_{i : I} u_{i}^{*} Y_{i}$ equipped with a jointly cartesian family
$\pi_{i} : \cE_{u_i}(\bigcap_{i : I} u_{i}^{*} Y_{i}, Y_{i})$.
:::

```agda
record Joint-cartesian-lift
  {ℓi : Level} {Ix : Type ℓi}
  {x : Ob} {yᵢ : Ix → Ob}
  (uᵢ : (ix : Ix) → Hom x (yᵢ ix))
  (yᵢ' : (ix : Ix) → Ob[ yᵢ ix ])
  : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ' ⊔ ℓi)
  where
  no-eta-equality
  field
    {x'} : Ob[ x ]
    lifting : (ix : Ix) → Hom[ uᵢ ix ] x' (yᵢ' ix)
    jointly-cartesian : is-jointly-cartesian uᵢ lifting

  open is-jointly-cartesian jointly-cartesian public
```

:::{.definition #jointly-cartesian-fibration}
A **$\kappa$ jointly cartesian fibration** is a displayed category
that joint cartesian lifts of all $\kappa$-small families.
:::

```agda
Jointly-cartesian-fibration : (κ : Level) → Type _
Jointly-cartesian-fibration κ =
  ∀ (Ix : Type κ)
  → {x : Ob} {yᵢ : Ix → Ob}
  → (uᵢ : (ix : Ix) → Hom x (yᵢ ix))
  → (yᵢ' : (ix : Ix) → Ob[ yᵢ ix ])
  → Joint-cartesian-lift uᵢ yᵢ'

module Jointly-cartesian-fibration {κ} (fib : Jointly-cartesian-fibration κ) where
```

<details>
<summary>The following section defines some nice notation for jointly
cartesian fibrations, but is a bit verbose.
</summary>
```agda
  module _
    (Ix : Type κ) {x : Ob} {yᵢ : Ix → Ob}
    (uᵢ : (ix : Ix) → Hom x (yᵢ ix))
    (yᵢ' : (ix : Ix) → Ob[ yᵢ ix ])
    where
    open Joint-cartesian-lift (fib Ix uᵢ yᵢ')
      using ()
      renaming (x' to ⋂*)
      public

  module _
    {Ix : Type κ} {x : Ob} {yᵢ : Ix → Ob}
    (uᵢ : (ix : Ix) → Hom x (yᵢ ix))
    (yᵢ' : (ix : Ix) → Ob[ yᵢ ix ])
    where
    open Joint-cartesian-lift (fib Ix uᵢ yᵢ')
      using ()
      renaming (lifting to π*)
      public

  module π*
    {Ix : Type κ} {x : Ob} {yᵢ : Ix → Ob}
    {uᵢ : (ix : Ix) → Hom x (yᵢ ix)}
    {yᵢ' : (ix : Ix) → Ob[ yᵢ ix ]}
    where
    open Joint-cartesian-lift (fib Ix uᵢ yᵢ')
      hiding (x'; lifting)
      public
```
</details>

Every jointly cartesian fibration has objects that act like discrete
spaces arising from lifts of empty families.

```agda
  opaque
    Disc* : ∀ (x : Ob) → Ob[ x ]
    Disc* x = ⋂* (Lift _ ⊥) {yᵢ = λ ()} (λ ()) (λ ())

    disc*
      : ∀ {x y : Ob}
      → (u : Hom x y) (x' : Ob[ x ])
      → Hom[ u ] x' (Disc* y)
    disc* u x' = π*.universal u (λ ())

    disc*-unique
      : ∀ {x y : Ob}
      → {u : Hom x y} {x' : Ob[ x ]}
      → (other : Hom[ u ] x' (Disc* y))
      → other ≡ disc* u x'
    disc*-unique other = π*.unique other (λ ())
```
