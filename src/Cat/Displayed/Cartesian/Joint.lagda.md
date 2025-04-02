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
property of a [[cartesian|cartesian-morphism]] map.
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
  ℓi ℓi' ℓj : Level
  Ix Ix' : Type ℓi
  Jx : Ix → Type ℓj
  a b c : Ob
  bᵢ cᵢ : Ix → Ob
  cᵢⱼ : (i : Ix) → Jx i → Ob
  a' b' c' : Ob[ a ]
  bᵢ' cᵢ' : (ix : Ix) → Ob[ bᵢ ix ]
  cᵢⱼ' : (i : Ix) → (j : Jx i) → Ob[ cᵢⱼ i j ]
  u v : Hom a b
  uᵢ uⱼ vᵢ vⱼ : ∀ (ix : Ix) → Hom a (bᵢ ix)
  f g : Hom[ u ] a' b'
  fᵢ fⱼ fᵢ' gᵢ gⱼ : ∀ (ix : Ix) → Hom[ uᵢ ix ] a' (bᵢ' ix)
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

- Jointly cartesian maps in the [[subobject fibration]] of $\Sets$
arise from pulling back a family of subsets $A_{i} \subset Y_{i}$ along
maps $u_{i} : X \to Y_{i}$, and then taking their intersection.

- When $\cB$ is considered as a displayed category over the [[terminal category]],
the jointly cartesian families are precisely the [[indexed products]].
In contrast, the cartesian maps are the invertible maps.

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

Conversely, if the constant family $\lambda i.\; f$ is a jointly cartesian
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

Jointly cartesian families over empty types act more like codiscrete objects
than pullbacks, as the space of maps into the shared domain of the family
is unique for any $v : \cE{B}(X, A)$ and $X' \liesover X$. In the displayed
category of topological spaces, such maps are precisely the discrete spaces.

```agda
empty-jointly-cartesian→codiscrete
  : ∀ {uᵢ : (ix : Ix) → Hom a (bᵢ ix)} {fᵢ : (ix : Ix) → Hom[ uᵢ ix ] a' (bᵢ' ix)}
  → ¬ Ix
  → is-jointly-cartesian uᵢ fᵢ
  → ∀ {x} (v : Hom x a) → (x' : Ob[ x ]) → is-contr (Hom[ v ] x' a')
empty-jointly-cartesian→codiscrete ¬ix fᵢ-cart v x' =
  contr (fᵢ.universal v λ ix → absurd (¬ix ix)) λ other →
    sym (fᵢ.unique other λ ix → absurd (¬ix ix))
  where
    module fᵢ = is-jointly-cartesian fᵢ-cart
```

In the other direction, let $f : \cE_{u}(A', B')$ be some map.
If the constant family $\lambda b.\; f : 2 \to \cE_{u}(A', B')$
is jointly cartesian as a family over the booleans,
then the type of morphisms $\cE_{u \circ v}(X', A')$ is a [[proposition]]
for every $v : \cB(X, A)$ and $X' \liesover X$.

```agda
const-pair-joint-cartesian→thin
  : ∀ {u : Hom a b} {f : Hom[ u ] a' b'}
  → is-jointly-cartesian {Ix = Bool} (λ _ → u) (λ _ → f)
  → ∀ {x} (v : Hom x a) → (x' : Ob[ x ]) → is-prop (Hom[ u ∘ v ] x' b')
```

Let $g, h : \cE_{u \circ v}(X', A')$ be a pair of parallel maps in $\cE$.
We can view the the pair $(g, h)$ as a `Bool`{.Agda} indexed family of
maps over $u \circ v$, so by the universal property of jointly cartesian
families, there must be a universal map $\alpha$ such that $g = f \circ \alpha$
and $h = f \circ \alpha$; thus $f = g$.


```agda
const-pair-joint-cartesian→thin {b' = b'} {u = u} {f = f} f-cart v x' g h =
  cast[] $
    g                   ≡[]˘⟨ commutes v gh true ⟩
    f ∘' universal v gh ≡[]⟨ commutes v gh false ⟩
    h                   ∎
  where
    open is-jointly-cartesian f-cart

    gh : Bool → Hom[ u ∘ v ] x' b'
    gh true = g
    gh false = h
```

As a corollary, if $(id_{A'}, id_{A'})$ is a jointly cartesian family, then
every hom set $\cE_{u}(X',A')$ is a proposition.

```agda
id-pair-joint-cartesian→thin
  : is-jointly-cartesian {Ix = Bool} (λ _ → id {a}) (λ _ → id' {a} {a'})
  → ∀ {x} (u : Hom x a) → (x' : Ob[ x ]) → is-prop (Hom[ u ] x' a')
id-pair-joint-cartesian→thin id²-cart u x' f g =
  cast[] $
    f       ≡[]⟨ wrap (sym (idl u)) ⟩
    hom[] f ≡[]⟨ const-pair-joint-cartesian→thin id²-cart u x' (hom[ idl u ]⁻ f) (hom[ idl u ]⁻ g) ⟩
    hom[] g ≡[]⟨ unwrap (sym (idl u)) ⟩
    g ∎
```

## Closure properties of jointly cartesian families

If $g_{i} : X' \to_{v_i} Y_{i}'$ is an $I$-indexed jointly cartesian family, and
$f_{i,j} : Y_{i}' \to_{u_{i,j}} Z_{i,j}'$ is an $I$-indexed family of $J_{i}$-indexed
jointly cartesian families, then their composite is a $\Sigma (i : I).\; J_i$-indexed
jointly cartesian family.

```agda
jointly-cartesian-∘
  : {uᵢⱼ : (i : Ix) → (j : Jx i) → Hom (bᵢ i) (cᵢⱼ i j)}
  → {fᵢⱼ : (i : Ix) → (j : Jx i) → Hom[ uᵢⱼ i j ] (bᵢ' i) (cᵢⱼ' i j)}
  → {vᵢ : (i : Ix) → Hom a (bᵢ i)}
  → {gᵢ : (i : Ix) → Hom[ vᵢ i ] a' (bᵢ' i)}
  → (∀ i → is-jointly-cartesian (uᵢⱼ i) (fᵢⱼ i))
  → is-jointly-cartesian vᵢ gᵢ
  → is-jointly-cartesian
      (λ ij → uᵢⱼ (ij .fst) (ij .snd) ∘ vᵢ (ij .fst))
      (λ ij → fᵢⱼ (ij .fst) (ij .snd) ∘' gᵢ (ij .fst))
```

<!--
```agda
_ = cartesian-∘
```
-->

Despite the high quantifier complexity of the statement, the proof
follows the exact same plan that we use to show that `cartesian maps compose`{.Agda ident=cartesian-∘}.

```agda
jointly-cartesian-∘ {Ix = Ix} {uᵢⱼ = uᵢⱼ} {fᵢⱼ = fᵢⱼ} {vᵢ = vᵢ} {gᵢ = gᵢ} fᵢⱼ-cart gᵢ-cart =
  fᵢⱼ∘gᵢ-cart
  where
    module fᵢⱼ (i : Ix) = is-jointly-cartesian (fᵢⱼ-cart i)
    module gᵢ = is-jointly-cartesian gᵢ-cart
    open is-jointly-cartesian

    fᵢⱼ∘gᵢ-cart
      : is-jointly-cartesian
          (λ ij → uᵢⱼ (ij .fst) (ij .snd) ∘ vᵢ (ij .fst))
          (λ ij → fᵢⱼ (ij .fst) (ij .snd) ∘' gᵢ (ij .fst))
    fᵢⱼ∘gᵢ-cart .universal v hᵢⱼ =
      gᵢ.universal v λ i →
      fᵢⱼ.universal' i (λ j → assoc (uᵢⱼ i j) (vᵢ i) v) λ j →
      hᵢⱼ (i , j)
    fᵢⱼ∘gᵢ-cart .commutes w hᵢⱼ (i , j) =
      cast[] $
        (fᵢⱼ i j ∘' gᵢ i) ∘' gᵢ.universal _ (λ i → fᵢⱼ.universal' i _ (λ j → hᵢⱼ (i , j))) ≡[]⟨ pullr[] _ (gᵢ.commutes w _ i) ⟩
        fᵢⱼ i j ∘' fᵢⱼ.universal' i _ (λ j → hᵢⱼ (i , j))                                  ≡[]⟨ fᵢⱼ.commutesp i _ _ j ⟩
        hᵢⱼ (i , j) ∎
    fᵢⱼ∘gᵢ-cart .unique {hᵢ = hᵢⱼ} other p =
      gᵢ.unique other $ λ i →
      fᵢⱼ.uniquep i _ _ _ (gᵢ i ∘' other) λ j →
        fᵢⱼ i j ∘' gᵢ i ∘' other   ≡[]⟨ assoc' (fᵢⱼ i j) (gᵢ i) other ⟩
        (fᵢⱼ i j ∘' gᵢ i) ∘' other ≡[]⟨ p (i , j) ⟩
        hᵢⱼ (i , j)                ∎
```

As a nice corollary, we get that jointly cartesian families compose with
[[cartesian maps]], as cartesian maps are precisely the singleton jointly cartesian
families.

```agda
jointly-cartesian-cartesian-∘
  : is-jointly-cartesian uᵢ fᵢ
  → is-cartesian v g
  → is-jointly-cartesian (λ ix → uᵢ ix ∘ v) (λ ix → fᵢ ix ∘' g)
```

<details>
<summary>We actually opt to prove this corollary by hand to get nicer
definitional behaviour of the resulting universal maps.
</summary>

```agda
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
</details>

Similarly, if $f_{i}$ is a family of maps with each $f_{i}$ individually
cartesian, and $g_{i}$ is jointly cartesian, then the composite $f_{i} \circ g_{i}$
is jointly cartesian.

```agda
pointwise-cartesian-jointly-cartesian-∘
  : (∀ ix → is-cartesian (uᵢ ix) (fᵢ ix))
  → is-jointly-cartesian vᵢ gᵢ
  → is-jointly-cartesian (λ ix → uᵢ ix ∘ vᵢ ix) (λ ix → fᵢ ix ∘' gᵢ ix)
```

<details>
<summary>We again prove this by hand to get better definitional behaviour.
</summary>
```agda
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
</details>

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
  {uᵢ = uᵢ} {fᵢ = fᵢ} {fᵢ' = fᵢ'} {ϕ = ϕ} fᵢ-cart ϕ-sect factor
  = fᵢ'-cart
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

Every jointly cartesian family is a [[jointly weak monic family]];
this follows immediately from the uniqueness portion of the
universal property.

```agda
jointly-cartesian→jointly-weak-monic
  : is-jointly-cartesian uᵢ fᵢ
  → is-jointly-weak-monic fᵢ
jointly-cartesian→jointly-weak-monic {fᵢ = fᵢ} fᵢ-cart {g = w} g h p p' =
  fᵢ.uniquep₂ (λ _ → ap₂ _∘_ refl p) p (λ _ → refl) g h p' (λ _ → refl)
  where module fᵢ = is-jointly-cartesian fᵢ-cart
```

If $f_{i,j}$ is an $I$-indexed family of $J_{i}$-indexed
[[jointly weak monic families]] and $f_{i,j} \circ g_{i}$ is a
$\Sigma (i : I).\; J_{i}$-indexed jointly cartesian family, then
$g_{i}$ must be a $I$-indexed jointly cartesian family.

```agda
jointly-cartesian-weak-monic-cancell
  : {uᵢⱼ : (i : Ix) → (j : Jx i) → Hom (bᵢ i) (cᵢⱼ i j)}
  → {fᵢⱼ : (i : Ix) → (j : Jx i) → Hom[ uᵢⱼ i j ] (bᵢ' i) (cᵢⱼ' i j)}
  → {vᵢ : (i : Ix) → Hom a (bᵢ i)}
  → {gᵢ : (i : Ix) → Hom[ vᵢ i ] a' (bᵢ' i)}
  → (∀ i → is-jointly-weak-monic (fᵢⱼ i))
  → is-jointly-cartesian
      (λ ij → uᵢⱼ (ij .fst) (ij .snd) ∘ vᵢ (ij .fst))
      (λ ij → fᵢⱼ (ij .fst) (ij .snd) ∘' gᵢ (ij .fst))
  → is-jointly-cartesian vᵢ gᵢ
```

Like the general composition lemma for jointly cartesian families,
the statement is more complicated than the proof, which follows from
some short calculations.

```agda
jointly-cartesian-weak-monic-cancell
  {uᵢⱼ = uᵢⱼ} {fᵢⱼ} {vᵢ} {gᵢ} fᵢⱼ-weak-mono fᵢⱼ∘gᵢ-cart
  = gᵢ-cart
  where
    module fᵢⱼ∘gᵢ = is-jointly-cartesian fᵢⱼ∘gᵢ-cart
    open is-jointly-cartesian

    gᵢ-cart : is-jointly-cartesian vᵢ gᵢ
    gᵢ-cart .universal w hᵢ =
      fᵢⱼ∘gᵢ.universal' (λ (i , j) → sym (assoc (uᵢⱼ i j) (vᵢ i) w)) λ (i , j) →
        fᵢⱼ i j ∘' hᵢ i
    gᵢ-cart .commutes w hᵢ i =
      fᵢⱼ-weak-mono i _ _ refl $ λ j →
      cast[] $
        fᵢⱼ i j ∘' gᵢ i ∘' fᵢⱼ∘gᵢ.universal' _ (λ (i , j) → fᵢⱼ i j ∘' hᵢ i)   ≡[]⟨ assoc' _ _ _ ⟩
        (fᵢⱼ i j ∘' gᵢ i) ∘' fᵢⱼ∘gᵢ.universal' _ (λ (i , j) → fᵢⱼ i j ∘' hᵢ i) ≡[]⟨ fᵢⱼ∘gᵢ.commutesp _ _ (i , j) ⟩
        fᵢⱼ i j ∘' hᵢ i                                                        ∎
    gᵢ-cart .unique other p =
      fᵢⱼ∘gᵢ.uniquep _ _ _ other λ (i , j) →
        pullr[] _ (p i)
```

As an immediate corollary, we get a left cancellation property
for composites of joint cartesian families.

```agda
jointly-cartesian-cancell
  : {uᵢⱼ : (i : Ix) → (j : Jx i) → Hom (bᵢ i) (cᵢⱼ i j)}
  → {fᵢⱼ : (i : Ix) → (j : Jx i) → Hom[ uᵢⱼ i j ] (bᵢ' i) (cᵢⱼ' i j)}
  → {vᵢ : (i : Ix) → Hom a (bᵢ i)}
  → {gᵢ : (i : Ix) → Hom[ vᵢ i ] a' (bᵢ' i)}
  → (∀ i → is-jointly-cartesian (uᵢⱼ i) (fᵢⱼ i))
  → is-jointly-cartesian
      (λ ij → uᵢⱼ (ij .fst) (ij .snd) ∘ vᵢ (ij .fst))
      (λ ij → fᵢⱼ (ij .fst) (ij .snd) ∘' gᵢ (ij .fst))
  → is-jointly-cartesian vᵢ gᵢ
jointly-cartesian-cancell fᵢⱼ-cart fᵢⱼ∘gᵢ-cart =
  jointly-cartesian-weak-monic-cancell
    (λ i → jointly-cartesian→jointly-weak-monic (fᵢⱼ-cart i))
    fᵢⱼ∘gᵢ-cart
```

We also obtain a further set of corollaries that describe some special
cases of the general cancellation property.

```agda
jointly-cartesian-pointwise-weak-monic-cancell
  : (∀ ix → is-weak-monic (fᵢ ix))
  → is-jointly-cartesian (λ ix → uᵢ ix ∘ vᵢ ix) (λ ix → fᵢ ix ∘' gᵢ ix)
  → is-jointly-cartesian vᵢ gᵢ

jointly-cartesian-jointly-weak-monic-cancell
  : is-jointly-weak-monic fᵢ
  → is-jointly-cartesian (λ ix → uᵢ ix ∘ v) (λ ix → fᵢ ix ∘' g)
  → is-cartesian v g

jointly-cartesian-pointwise-cartesian-cancell
  : (∀ ix → is-cartesian (uᵢ ix) (fᵢ ix))
  → is-jointly-cartesian (λ ix → uᵢ ix ∘ vᵢ ix) (λ ix → fᵢ ix ∘' gᵢ ix)
  → is-jointly-cartesian vᵢ gᵢ

jointly-cartesian-cartesian-cancell
  : is-jointly-cartesian uᵢ fᵢ
  → is-jointly-cartesian (λ ix → uᵢ ix ∘ v) (λ ix → fᵢ ix ∘' g)
  → is-cartesian v g
```

<details>
<summary>As before, we opt to prove these results by hand to get nicer
definitional behaviour.
</summary>

```agda
jointly-cartesian-pointwise-weak-monic-cancell
  {uᵢ = uᵢ} {fᵢ = fᵢ} {vᵢ = vᵢ} {gᵢ = gᵢ} fᵢ-weak-monic fᵢ∘gᵢ-cart
  = gᵢ-cart
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

jointly-cartesian-jointly-weak-monic-cancell
  {uᵢ = uᵢ} {fᵢ = fᵢ} {v = v} {g = g} fᵢ-weak-monic fᵢ∘g-cart
  = g-cart
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

jointly-cartesian-pointwise-cartesian-cancell fᵢ-cart fᵢ∘gᵢ-cart =
  jointly-cartesian-pointwise-weak-monic-cancell
    (λ ix → cartesian→weak-monic (fᵢ-cart ix))
    fᵢ∘gᵢ-cart

jointly-cartesian-cartesian-cancell fᵢ-cart fᵢ∘g-cart =
  jointly-cartesian-jointly-weak-monic-cancell
    (jointly-cartesian→jointly-weak-monic fᵢ-cart)
    fᵢ∘g-cart

```
</details>

## Extending jointly cartesian families

This section characterises when we can extend an $I'$-indexed jointly
cartesian family $f_{i}$ to a $I$-indexed cartesian family along a map
$e : I' \to I$. Though seemingly innocent, being able to extend every family
$f_{i} : \cE_{u_i}(A', B_{i}')$ is equivalent to the displayed category
being thin!

For the forward direction, let $f_{i} : \cE{u_i}(A', B_{i}')$ be a
family such that the restriction of $f_{i}$ along a map $e : I' \to I$
thin. We can then easily extend the family $f_{i}$ along an arbitrary map
by ignoring every single equality, as all hom sets involved are thin.

```agda
thin→jointly-cartesian-extend
  : ∀ {u : (i : Ix) → Hom a (bᵢ i)} {fᵢ : (i : Ix) → Hom[ uᵢ i ] a' (bᵢ' i)}
  → (∀ {x} (v : Hom x a) → (x' : Ob[ x ]) → ∀ (i : Ix) → is-prop (Hom[ uᵢ i ∘ v ] x' (bᵢ' i)))
  → (e : Ix' → Ix)
  → is-jointly-cartesian (λ i' → uᵢ (e i')) (λ i' → fᵢ (e i'))
  → is-jointly-cartesian (λ i → uᵢ i) (λ i → fᵢ i)
thin→jointly-cartesian-extend {uᵢ = uᵢ} {fᵢ = fᵢ} uᵢ∘v-thin e fₑᵢ-cart = fᵢ-cart where
  module fₑᵢ = is-jointly-cartesian fₑᵢ-cart
  open is-jointly-cartesian

  fᵢ-cart : is-jointly-cartesian (λ i' → uᵢ i') (λ i' → fᵢ i')
  fᵢ-cart .universal v hᵢ =
    fₑᵢ.universal v (λ i' → hᵢ (e i'))
  fᵢ-cart .commutes {x} {x'} v hᵢ i =
    uᵢ∘v-thin v x' i (fᵢ i ∘' fₑᵢ.universal v (λ i' → hᵢ (e i'))) (hᵢ i)
  fᵢ-cart .unique {x} {x'} {v} {hᵢ} other p =
    fₑᵢ.unique other λ i' → uᵢ∘v-thin v x' (e i') (fᵢ (e i') ∘' other) (hᵢ (e i'))
```

For the reverse direction, suppose we could extend arbitrary families.
In particular, this means that we can extend singleton families to constant
families, which lets us transfer a proof that a morphism is cartesian to
a proof that a constant family is jointly cartesian.

In particular, this means that the pair $(\id, \id)$ is jointly cartesian,
which means that the hom set is thin!

```agda
jointly-cartesian-extend→thin
  : ∀ (extend
    : ∀ {Ix' Ix : Type} {bᵢ : Ix → Ob} {bᵢ' : (i : Ix) → Ob[ bᵢ i ]}
    → {uᵢ : (i : Ix) → Hom a (bᵢ i)} {fᵢ : (i : Ix) → Hom[ uᵢ i ] a' (bᵢ' i)}
    → (e : Ix' → Ix)
    → is-jointly-cartesian (λ i' → uᵢ (e i')) (λ i' → fᵢ (e i'))
    → is-jointly-cartesian (λ i → uᵢ i) (λ i → fᵢ i))
  → ∀ {x} (v : Hom x a) → (x' : Ob[ x ]) → is-prop (Hom[ v ] x' a')
jointly-cartesian-extend→thin extend v x' =
  id-pair-joint-cartesian→thin
    (extend (λ _ → true)
      (cartesian→jointly-cartesian ⊤-is-contr cartesian-id))
    v x'
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
      renaming (x' to ∏*)
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

Every jointly cartesian fibration has objects that act like codiscrete
spaces arising from lifts of empty families.

```agda
  opaque
    Codisc* : ∀ (x : Ob) → Ob[ x ]
    Codisc* x = ∏* (Lift _ ⊥) {yᵢ = λ ()} (λ ()) (λ ())

    codisc*
      : ∀ {x y : Ob}
      → (u : Hom x y) (x' : Ob[ x ])
      → Hom[ u ] x' (Codisc* y)
    codisc* u x' = π*.universal u (λ ())

    codisc*-unique
      : ∀ {x y : Ob}
      → {u : Hom x y} {x' : Ob[ x ]}
      → (other : Hom[ u ] x' (Codisc* y))
      → other ≡ codisc* u x'
    codisc*-unique other = π*.unique other (λ ())
```
