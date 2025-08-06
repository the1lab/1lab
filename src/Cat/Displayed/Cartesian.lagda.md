<!--
```agda
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism
import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Cartesian
  {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ') where

open Cat.Displayed.Morphism E
open Cat.Reasoning B
open DR E
```

# Cartesian morphisms and fibrations

While [[displayed categories]] give the essential framework we need to
express the idea of families of categories indexed by a category, they
do not _quite_ capture the concept precisely. The problem is that while
a category $\cE$ displayed over $\cB$ does indeed give a
_collection_ of [[fibre categories]] $\cE^*(x)$, this assignment isn't
necessarily functorial!

More precisely, we should have that a collection of categories, indexed
by a category, should be a _pseudofunctor_ $\cB\op \to \Cat$, where
$\Cat$ is a [[bicategory]] of categories. It turns out that we can
characterise this assignment entirely in terms of the displayed objects
and morphisms in $\cE$!

:::{.definition #cartesian-morphism alias="cartesian-map"}
Fix an arrow $f : a \to b$ in the base category $\cB$, an object $a'$
over $a$ (resp. $b'$ over $b$), and an arrow $f' : a' \to_f b'$ over
$f$. We say that $f'$ is **cartesian** if, up to very strong handwaving,
it fits into a "pullback diagram". The barred arrows with triangle tips
here indicate the "projection" from a displayed object to its base, and
so are implicit in the type dependency.
:::

~~~{.quiver}
\[\begin{tikzcd}
  {a'} && {b'} \\
  \\
  a && b
  \arrow["{f'}"', from=1-1, to=1-3]
  \arrow["f", from=3-1, to=3-3]
  \arrow[lies over, from=1-1, to=3-1]
  \arrow[lies over, from=1-3, to=3-3]
\end{tikzcd}\]
~~~

```agda
record
  is-cartesian {a b a' b'} (f : Hom a b) (f' : Hom[ f ] a' b') : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ')
  where
  no-eta-equality
```

More specifically, let $u : \cB$ and $u'$ be over $u$, and suppose
that we have a map $m : u \to a$ (below, in violet), and a map $h' : u'
\to_{fm} b'$ lying over the composite $fm$ (in red). The universal property
of a Cartesian map says that we have a universal factorisation of $h'$
through a map $u' \to a'$ (in green, marked $\exists!$).

~~~{.quiver}
\[\begin{tikzcd}
  \textcolor{rgb,255:red,124;green,50;blue,189}{u'} \\
  & {a'} && {b'} \\
  \textcolor{rgb,255:red,124;green,50;blue,189}{u} \\
  & a && b
  \arrow["{f'}"', from=2-2, to=2-4]
  \arrow["f", from=4-2, to=4-4]
  \arrow[lies over, from=2-2, to=4-2]
  \arrow[lies over, from=2-4, to=4-4]
  \arrow["m"', color={rgb,255:red,124;green,50;blue,189}, from=3-1, to=4-2]
  \arrow[lies over, color={rgb,255:red,124;green,50;blue,189}, from=1-1, to=3-1]
  \arrow["{h'}", color={rgb,255:red,204;green,51;blue,51}, curve={height=-12pt}, from=1-1, to=2-4]
  \arrow["{\exists!}"', color={rgb,255:red,36;green,202;blue,28}, dashed, from=1-1, to=2-2]
\end{tikzcd}\]
~~~

```agda
  field
    universal : ∀ {u u'} (m : Hom u a) (h' : Hom[ f ∘ m ] u' b') → Hom[ m ] u' a'
    commutes  : ∀ {u u'} (m : Hom u a) (h' : Hom[ f ∘ m ] u' b')
              → f' ∘' universal m h' ≡ h'
    unique    : ∀ {u u'} {m : Hom u a} {h' : Hom[ f ∘ m ] u' b'}
              → (m' : Hom[ m ] u' a') → f' ∘' m' ≡ h' → m' ≡ universal m h'
```
Given a "right corner" like that of the diagram below, and note that the
input data consists of $a$, $b$, $f : a \to b$ and $b'$ over $a$,

~~~{.quiver}
\[\begin{tikzcd}
  && {b'} \\
  \\
  a && {b\text{,}}
  \arrow[lies over, from=1-3, to=3-3]
  \arrow["f"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

We also provide some helper functions for working with morphisms that
are displayed over something that is *propositionally* equal to a
composite, rather than displayed directly over a composite.

```agda
  universal' : ∀ {u u'} {m : Hom u a} {k : Hom u b}
             → (p : f ∘ m ≡ k) (h' : Hom[ k ] u' b')
             → Hom[ m ] u' a'
  universal' {u' = u'} p h' =
    universal _ (coe1→0 (λ i → Hom[ p i ] u' b') h')

  abstract
    commutesp : ∀ {u u'} {m : Hom u a} {k : Hom u b}
              → (p : f ∘ m ≡ k) (h' : Hom[ k ] u' b')
              → f' ∘' universal' p h' ≡[ p ] h'
    commutesp {u' = u'} p h' =
      to-pathp⁻ $ commutes _ (coe1→0 (λ i → Hom[ p i ] u' b') h')

    universalp : ∀ {u u'} {m₁ m₂ : Hom u a} {k : Hom u b}
            → (p : f ∘ m₁ ≡ k) (q : m₁ ≡ m₂) (r : f ∘ m₂ ≡ k)
            → (h' : Hom[ k ] u' b')
            → universal' p h' ≡[ q ] universal' r h'
    universalp {u = u} p q r h' i =
      universal' (is-set→squarep (λ _ _ → Hom-set u b) (ap (f ∘_) q) p r refl i) h'

    uniquep : ∀ {u u'} {m₁ m₂ : Hom u a} {k : Hom u b}
            → (p : f ∘ m₁ ≡ k) (q : m₁ ≡ m₂) (r : f ∘ m₂ ≡ k)
            → {h' : Hom[ k ] u' b'}
            → (m' : Hom[ m₁ ] u' a')
            → f' ∘' m' ≡[ p ] h' → m' ≡[ q ] universal' r h'
    uniquep p q r {h' = h'} m' s =
      to-pathp⁻ (unique m' (from-pathp⁻ s) ∙ from-pathp⁻ (universalp p q r h'))

    uniquep₂
      : ∀ {u u'} {m₁ m₂ : Hom u a} {k : Hom u b}
      → (p : f ∘ m₁ ≡ k) (q : m₁ ≡ m₂) (r : f ∘ m₂ ≡ k)
      → {h' : Hom[ k ] u' b'} (m₁' : Hom[ m₁ ] u' a') (m₂' : Hom[ m₂ ] u' a')
      → f' ∘' m₁' ≡[ p ] h'
      → f' ∘' m₂' ≡[ r ] h'
      → m₁' ≡[ q ] m₂'
    uniquep₂ {u' = u'} p q r m₁' m₂' α β = to-pathp⁻ $
         unique m₁' (from-pathp⁻ α)
      ∙∙ from-pathp⁻ (universalp p q r _)
      ∙∙ ap (coe1→0 (λ i → Hom[ q i ] u' a')) (sym (unique m₂' (from-pathp⁻ β)))
```

Furthermore, if $f'' : a'' \to_{f} b'$ is also displayed over $f$,
there's a unique vertical map $a'' \to a'$. This witnesses the fact that
every cartesian map is [weakly cartesian].

[weakly cartesian]: Cat.Displayed.Cartesian.Weak.html

```agda
  universalv : ∀ {a''} (f'' : Hom[ f ] a'' b') → Hom[ id ] a'' a'
  universalv f'' = universal' (idr _) f''

  commutesv
    : ∀ {x'} → (g' : Hom[ f ] x' b')
    → f' ∘' universalv g' ≡[ idr _ ] g'
  commutesv = commutesp (idr _)

  uniquev
    : ∀ {x'} {g' : Hom[ f ] x' b'}
    → (h' : Hom[ id ] x' a')
    → f' ∘' h' ≡[ idr _ ] g'
    → h' ≡ universalv g'
  uniquev h' p = uniquep (idr f) refl (idr f) h' p

  uniquev₂
    : ∀ {x'} {g' : Hom[ f ] x' b'}
    → (h' h'' : Hom[ id ] x' a')
    → f' ∘' h' ≡[ idr _ ] g'
    → f' ∘' h'' ≡[ idr _ ] g'
    → h' ≡ h''
  uniquev₂ h' h'' p q =
    uniquep₂ (idr f) refl (idr f) h' h'' p q
```

As the name suggests, being cartesian is a property of a morphism.

```agda
is-cartesian-is-prop
  : ∀ {x y x' y'} {f : Hom x y} {f' : Hom[ f ] x' y'}
  → is-prop (is-cartesian f f')
```

<details>
<summary>The proof of this fact is a bunch of cubical nonsense.
</summary>

```agda
is-cartesian-is-prop {f' = f'} cart cart' = worker where
  open is-cartesian

  worker : cart ≡ cart'
  worker i .universal m h' =
    cart' .unique (cart .universal m h') (cart .commutes _ _) i
  worker i .commutes m h' =
    is-set→squarep (λ _ _ → Hom[ _ ]-set _ _)
      (ap (f' ∘'_) (cart' .unique _ _))
      (cart .commutes m h')
      (cart' .commutes m h')
      refl i
  worker i .unique m' p =
    is-set→squarep (λ _ _ → Hom[ _ ]-set _ _)
      refl
      (cart .unique m' p)
      (cart' .unique m' p)
      (cart' .unique _ _) i
```
</details>

<!--
```agda
instance
  H-Level-is-cartesian
    : ∀ {x y x' y'} {f : Hom x y} {f' : Hom[ f ] x' y'} {n}
    → H-Level (is-cartesian f f') (suc n)
  H-Level-is-cartesian = prop-instance is-cartesian-is-prop

subst-is-cartesian
  : ∀ {x y x' y'} {f g : Hom x y} {f' : Hom[ f ] x' y'} {g' : Hom[ g ] x' y'}
  → (p : f ≡ g) (p' : f' ≡[ p ] g')
  → is-cartesian f f'
  → is-cartesian g g'
subst-is-cartesian {g = g} {f' = f'} {g' = g'} p p' f-cart = g-cart where
  module f' = is-cartesian f-cart
  open is-cartesian

  g-cart : is-cartesian g g'
  g-cart .universal m h' =
    f'.universal' (ap (_∘ m) p) h'
  g-cart .commutes m h' =
    cast[] $
      g' ∘' f'.universal' _ h' ≡[]⟨ symP p' ⟩∘'⟨refl ⟩
      f' ∘' f'.universal' _ h' ≡[]⟨ f'.commutesp (ap (_∘ m) p) h' ⟩
      h' ∎
  g-cart .unique m' q =
    f'.uniquep _ _ _ m' ((p' ⟩∘'⟨refl) ∙[] q)
```
-->

We also provide a bundled form of cartesian morphisms.

```agda
record Cartesian-morphism
  {x y : Ob} (f : Hom x y) (x' : Ob[ x ]) (y' : Ob[ y ])
  : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
  no-eta-equality
  field
    hom' : Hom[ f ] x' y'
    cartesian : is-cartesian f hom'
```

<!--
```agda
Cartesian-morphism-pathp
  : ∀ {x y x' y'} {f g : Hom x y}
  → {f' : Cartesian-morphism f x' y'} {g' : Cartesian-morphism g x' y'}
  → {p : f ≡ g}
  → PathP (λ i → Hom[ p i ] x' y') (Cartesian-morphism.hom' f') (Cartesian-morphism.hom' g')
  → PathP (λ i → Cartesian-morphism (p i) x' y') f' g'
Cartesian-morphism-pathp q i .Cartesian-morphism.hom' = q i
Cartesian-morphism-pathp {f' = f'} {g' = g'} {p = p} q i .Cartesian-morphism.cartesian =
  is-prop→pathp (λ i → is-cartesian-is-prop {f = p i} {f' = q i})
    (Cartesian-morphism.cartesian f')
    (Cartesian-morphism.cartesian g') i

Cartesian-morphism-is-set
  : ∀ {x y x' y'} {f : Hom x y}
  → is-set (Cartesian-morphism f x' y')
Cartesian-morphism-is-set = Iso→is-hlevel 2 eqv $
  Σ-is-hlevel 2 (Hom[ _ ]-set _ _) λ _ →
  is-hlevel-suc 1 is-cartesian-is-prop
  where unquoteDecl eqv = declare-record-iso eqv (quote Cartesian-morphism)
```
-->

## Properties of cartesian morphisms

The composite of 2 cartesian morphisms is in turn cartesian.

```agda
cartesian-∘
  : ∀ {x y z} {f : Hom y z} {g : Hom x y}
  → ∀ {x' y' z'} {f' : Hom[ f ] y' z'} {g' : Hom[ g ] x' y'}
  → is-cartesian f f' → is-cartesian g g'
  → is-cartesian (f ∘ g) (f' ∘' g')
cartesian-∘ {f = f} {g = g} {f' = f'} {g' = g'} f-cart g-cart = fg-cart where

  module f' = is-cartesian f-cart
  module g' = is-cartesian g-cart

  fg-cart : is-cartesian (f ∘ g) (f' ∘' g')
  fg-cart .is-cartesian.universal m h' =
    g'.universal m (f'.universal' (assoc f g m) h')
  fg-cart .is-cartesian.commutes m h' =
    cast[] $
      (f' ∘' g') ∘' g'.universal m (f'.universal' _ h') ≡[]⟨ pullr[] _ (g'.commutes _ _) ⟩
      f' ∘' f'.universal' _ h'                          ≡[]⟨ f'.commutesp (assoc f g m) h' ⟩
      h'                                                ∎
  fg-cart .is-cartesian.unique {m = m} {h' = h'} m' p =
    g'.unique m' $ f'.uniquep _ _ _ (g' ∘' m') $
      f' ∘' g' ∘' m'   ≡[]⟨ assoc' f' g' m' ⟩
      (f' ∘' g') ∘' m' ≡[]⟨ p ⟩
      h'               ∎

_∘cart_
  : ∀ {x y z x' y' z'} {f : Hom y z} {g : Hom x y}
  → Cartesian-morphism f y' z' → Cartesian-morphism g x' y'
  → Cartesian-morphism (f ∘ g) x' z'
f' ∘cart g' = fg' where
  open Cartesian-morphism

  fg' : Cartesian-morphism _ _ _
  fg' .hom' = f' .hom' ∘' g' .hom'
  fg' .cartesian = cartesian-∘ (f' .cartesian) (g' .cartesian)
```

Furthermore, the identity morphism is cartesian.

```agda
cartesian-id : ∀ {x x'} → is-cartesian id (id' {x} {x'})
cartesian-id .is-cartesian.universal m h' = hom[ idl m ] h'
cartesian-id .is-cartesian.commutes m h' =
  from-pathp⁻ (idl' _) ∙ hom[]-∙ _ _ ∙ liberate _
cartesian-id .is-cartesian.unique m' p =
  from-pathp⁻ (symP $ idl' _) ∙ weave _ _ _ p

idcart : ∀ {x} {x' : Ob[ x ]} → Cartesian-morphism id x' x'
idcart .Cartesian-morphism.hom' = id'
idcart .Cartesian-morphism.cartesian = cartesian-id
```


In fact, every invertible map is also cartesian, as we can use
the inverse to construct the requisite factorisation.

```agda
invertible→cartesian
  : ∀ {x y} {f : Hom x y} {x' y'} {f' : Hom[ f ] x' y'}
  → (f-inv : is-invertible f)
  → is-invertible[ f-inv ] f'
  → is-cartesian f f'
invertible→cartesian
 {f = f} {f' = f'} f-inv f'-inv = f-cart where
  module f = is-invertible f-inv
  module f' = is-invertible[_] f'-inv

  f-cart : is-cartesian f f'
  f-cart .is-cartesian.universal m h' =
    hom[ cancell f.invr ] (f'.inv' ∘' h')
  f-cart .is-cartesian.commutes m h' =
    cast[] $
      f' ∘' hom[] (f'.inv' ∘' h') ≡[]⟨ unwrapr _ ⟩
      f' ∘' f'.inv' ∘' h'         ≡[]⟨ cancell[] _ f'.invl' ⟩
      h' ∎
  f-cart .is-cartesian.unique {h' = h'} m' p =
    cast[] $
      m'                    ≡[]⟨ introl[] f.invr f'.invr' ∙[] pullr[] _ p ⟩
      f'.inv' ∘' h'         ≡[]⟨ wrap (cancell f.invr) ⟩
      hom[] (f'.inv' ∘' h') ∎
```

<!--
```agda
iso→cartesian
  : ∀ {x y x' y'} {f : x ≅ y}
  → (f' : x' ≅[ f ] y')
  → is-cartesian (f .to) (f' .to')
iso→cartesian {f = f} f' =
  invertible→cartesian (iso→invertible f) (iso[]→invertible[] f')
```
-->

If $f$ is cartesian, it's also a [weak monomorphism].

[weak monomorphism]: Cat.Displayed.Morphism.html#weak-monos

```agda
cartesian→weak-monic
  : ∀ {x y} {f : Hom x y}
  → ∀ {x' y'} {f' : Hom[ f ] x' y'}
  → is-cartesian f f'
  → is-weak-monic f'
cartesian→weak-monic {f = f} {f' = f'} f-cart g' g'' p p' =
  uniquep₂ (ap (f ∘_) p) p refl g' g'' p' refl
  where
    open is-cartesian f-cart
```

We can use this fact to show that 2 cartesian lifts over the same
morphisms must have their domains related by a vertical isomorphism.
Suppose they're called $f_1$ and $f_2$, and fit into a diagram like the
one below.

~~~{.quiver}
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

Since $f_1$ and $f_2$ are both Cartesian morphisms, we can factor $f_2$
through $a_1'$ by a map $g$, and conversely, $f_1$ through $a_2'$ by
$h$.

~~~{.quiver}
\[\begin{tikzcd}
  {a_2'} \\
  {a_1'} & b'
  \arrow["g"', shift right=2, dashed, from=1-1, to=2-1]
  \arrow["h"', shift right=2, dashed, from=2-1, to=1-1]
  \arrow["{f_1}"', from=2-1, to=2-2]
  \arrow["{f_2}", from=1-1, to=2-2]
\end{tikzcd}\]
~~~

Since we're trying to prove that $h$ is an isomorphism, we want to show
that $hg=\mathrm{id}_{a_2'}$. We know that $f_2$ factors through $a'_2$,
its own domain, via the identity map. We will show that it also factors
through $hg$ to show that the two are equal, by the universal property
of $f_2$ being Cartesian. Consider the following diagram:

~~~{.quiver}
\[\begin{tikzcd}
  {a_2'} & b' \\
  {a_1'} & {a_2'}
  \arrow["g"', shift right=2, dashed, from=1-1, to=2-1]
  \arrow["{f_1}"', from=2-1, to=1-2]
  \arrow["{f_2}", from=1-1, to=1-2]
  \arrow["h"', shift right=2, dashed, from=2-1, to=2-2]
  \arrow["{f_2}"', from=2-2, to=1-2]
  \arrow["{\mathrm{id}}"{description, pos=0.2}, curve={height=12pt}, dashed, from=1-1, to=2-2]
\end{tikzcd}\]
~~~

We have $f_2hg = f_1g = f_2$. A symmetric argument shows that $gh$ is
also the identity, so $h : a_1' \cong a_2'$.

```agda
cartesian-domain-unique
  : ∀ {x y} {f : Hom x y}
  → ∀ {x' x'' y'} {f' : Hom[ f ] x' y'} {f'' : Hom[ f ] x'' y'}
  → is-cartesian f f'
  → is-cartesian f f''
  → x' ≅↓ x''
cartesian-domain-unique {f' = f'} {f'' = f''} f'-cart f''-cart =
  make-iso[ id-iso ] to* from* invl* invr* where
    module f' = is-cartesian f'-cart
    module f'' = is-cartesian f''-cart

    to* = f''.universalv f'
    from* = f'.universalv f''

    invl* : to* ∘' from* ≡[ idl id ] id'
    invl* =
      cartesian→weak-monic f''-cart (to* ∘' from*) id' (idl id) $
      cast[] $
        f'' ∘' to* ∘' from* ≡[]⟨ pulll[] _ (f''.commutesv f') ⟩
        f' ∘' from*         ≡[]⟨ f'.commutesv f'' ⟩
        f''                 ≡[]˘⟨ idr' f'' ⟩
        f'' ∘' id'          ∎

    invr* : from* ∘' to* ≡[ idl id ] id'
    invr* =
      cartesian→weak-monic f'-cart (from* ∘' to*) id' (idl id) $
      cast[] $
        f' ∘' from* ∘' to* ≡[]⟨ pulll[] _ (f'.commutesv f'') ⟩
        f'' ∘' to*         ≡[]⟨ f''.commutesv f' ⟩
        f'                 ≡[]˘⟨ idr' f' ⟩
        f' ∘' id'          ∎
```

Cartesian morphisms are also stable under vertical retractions.

```agda
cartesian-vertical-retraction-stable
  : ∀ {x y} {f : Hom x y}
  → ∀ {x' x'' y'} {f' : Hom[ f ] x' y'} {f'' : Hom[ f ] x'' y'} {ϕ : Hom[ id ] x' x''}
  → is-cartesian f f'
  → has-section↓ ϕ
  → f'' ∘' ϕ ≡[ idr _ ] f'
  → is-cartesian f f''
cartesian-vertical-retraction-stable {f' = f'} {f''} {ϕ} f-cart ϕ-sect factor = f''-cart where
  open is-cartesian f-cart
  module ϕ = has-section[_] ϕ-sect

  f''-cart : is-cartesian _ f''
  f''-cart .is-cartesian.universal m h' =
    hom[ idl m ] (ϕ ∘' universal m h')
  f''-cart .is-cartesian.commutes m h' =
    cast[] $
    f'' ∘' hom[] (ϕ ∘' universal m h') ≡[]⟨ unwrapr _ ⟩
    f'' ∘' ϕ ∘' universal m h'         ≡[]⟨ pulll[] _ factor ⟩
    f' ∘' universal m h'               ≡[]⟨ commutes m h' ⟩
    h'                                 ∎
  f''-cart .is-cartesian.unique {m = m} {h' = h'} m' p =
    from-pathp⁻ $ post-section' ϕ-sect $
    uniquep₂ _ (idl m) refl (ϕ.section' ∘' m') (universal m h')
      unique-lemma
      (commutes m h')
    where
      unique-lemma : f' ∘' ϕ.section' ∘' m' ≡[ _ ] h'
      unique-lemma =
        f' ∘' ϕ.section' ∘' m' ≡[]⟨ pulll[] _ (symP (pre-section[] ϕ-sect factor)) ⟩
        f'' ∘' m'              ≡[]⟨ p ⟩
        h'                     ∎
```

If $f' \circ g'$ is cartesian and $f'$ is a [[weak monomorphism]],
then $g'$ is cartesian.

```agda
cartesian-weak-monic-cancell
  : ∀ {x y z} {f : Hom y z} {g : Hom x y}
  → ∀ {x' y' z'} {f' : Hom[ f ] y' z'} {g' : Hom[ g ] x' y'}
  → is-weak-monic f'
  → is-cartesian (f ∘ g) (f' ∘' g')
  → is-cartesian g g'
cartesian-weak-monic-cancell {f = f} {g = g} {f' = f'} {g' = g'} f-weak-mono fg-cart = g-cart where
  module fg = is-cartesian fg-cart
  open is-cartesian

  g-cart : is-cartesian g g'
  g-cart .universal m h' =
    fg.universal' (sym (assoc f g m)) (f' ∘' h')
  g-cart .commutes m h' =
    f-weak-mono (g' ∘' fg.universal' _ (f' ∘' h')) h' refl $
    cast[] $
      f' ∘' g' ∘' fg.universal' _ (f' ∘' h')   ≡[]⟨ assoc' _ _ _ ⟩
      (f' ∘' g') ∘' fg.universal' _ (f' ∘' h') ≡[]⟨ fg.commutesp (sym (assoc f g m)) (f' ∘' h') ⟩
      f' ∘' h'                                 ∎
  g-cart .unique {m = m} m' p =
    fg.uniquep (sym (assoc f g m)) refl (sym (assoc f g m)) m' (pullr' refl p)
```

As a corollary, we get the following useful pasting lemma, which
generalizes the [[pasting law for pullbacks]].

```agda
cartesian-cancell
  : ∀ {x y z} {f : Hom y z} {g : Hom x y}
  → ∀ {x' y' z'} {f' : Hom[ f ] y' z'} {g' : Hom[ g ] x' y'}
  → is-cartesian f f'
  → is-cartesian (f ∘ g) (f' ∘' g')
  → is-cartesian g g'
cartesian-cancell f-cart fg-cart =
  cartesian-weak-monic-cancell (cartesian→weak-monic f-cart) fg-cart
```

We can prove a similar fact for bundled cartesian morphisms.

```agda
cart-paste
  : ∀ {x y z x' y' z'} {f : Hom y z} {g : Hom x y}
  → Cartesian-morphism f y' z'
  → Cartesian-morphism (f ∘ g) x' z'
  → Cartesian-morphism g x' y'
cart-paste {x' = x'} {y' = y'} {f = f} {g = g} f' fg' = g' where
  open Cartesian-morphism
  open is-cartesian
  module f' = is-cartesian (f' .cartesian)
  module fg' = is-cartesian (fg' .cartesian)

  g' : Cartesian-morphism g x' y'
  g' .hom' = f'.universal g (fg' .hom')
  g' .cartesian =
    cartesian-cancell (f' .cartesian) $
    subst-is-cartesian refl (sym (f'.commutes g (fg' .hom'))) (fg' .cartesian)
```

If a morphism is both vertical and cartesian, then it must be an
isomorphism. We can construct the inverse by factorizing the identity
morphism, which is possible due to the fact that $f'$ is vertical.

```agda
vertical+cartesian→invertible
  : ∀ {x} {x' x'' : Ob[ x ]} {f' : Hom[ id ] x' x''}
  → is-cartesian id f'
  → is-invertible↓ f'
vertical+cartesian→invertible {x' = x'} {x'' = x''} {f' = f'} f-cart =
  make-invertible↓ f⁻¹'  f'-invl f'-invr where
    open is-cartesian f-cart

    f⁻¹' : Hom[ id ] x'' x'
    f⁻¹' = universal' (idl _) id'

    f'-invl : f' ∘' f⁻¹' ≡[ idl _ ] id'
    f'-invl = commutesp _ id'

    path : f' ∘' f⁻¹' ∘' f' ≡[ elimr (idl _) ] f'
    path = cancell' (idl _) (commutesp (idl _) id')

    f'-invr : f⁻¹' ∘' f' ≡[ idl _ ] id'
    f'-invr =
      uniquep₂ _ _ _ (f⁻¹' ∘' f') id'
        (cancell[] _ f'-invl)
        (idr' f')
```

Furthermore, $f' : x' \to_{f} y'$ is cartesian if and only if the
function $f \cdot' -$ is an equivalence.

```agda
postcompose-equiv→cartesian
  : ∀ {x y x' y'} {f : Hom x y}
  → (f' : Hom[ f ] x' y')
  → (∀ {w w'} {g : Hom w x} → is-equiv {A = Hom[ g ] w' x'} (f' ∘'_))
  → is-cartesian f f'
postcompose-equiv→cartesian f' eqv .is-cartesian.universal m h' =
  equiv→inverse eqv h'
postcompose-equiv→cartesian f' eqv .is-cartesian.commutes m h' =
  equiv→counit eqv h'
postcompose-equiv→cartesian f' eqv .is-cartesian.unique m' p =
  sym (equiv→unit eqv m') ∙ ap (equiv→inverse eqv) p

cartesian→postcompose-equiv
  : ∀ {x y z x' y' z'} {f : Hom y z} {g : Hom x y} {f' : Hom[ f ] y' z'}
  → is-cartesian f f'
  → is-equiv {A = Hom[ g ] x' y'} (f' ∘'_)
cartesian→postcompose-equiv cart =
  is-iso→is-equiv $
    iso (universal _)
        (commutes _)
        (λ g' → sym (unique g' refl))
  where open is-cartesian cart
```


## Cartesian lifts {defines="cartesian-lift"}

We call an object $y'$ over $y$ together with a Cartesian arrow $f' : x'
\to y'$ a _Cartesian lift_ of $f$. Cartesian lifts, defined by universal
property as they are, are unique when they exist, so that "having
Cartesian lifts" is a _property_, not a structure.

```agda
record
  Cartesian-lift {x y} (f : Hom x y) (y' : Ob[ y ]) : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ')
  where
  no-eta-equality
  field
    {x'}      : Ob[ x ]
    lifting   : Hom[ f ] x' y'
    cartesian : is-cartesian f lifting
  open is-cartesian cartesian public
```

We note that the classical literature often differentiates between
_fibrations_ --- those displayed categories for which _there exist_
Cartesian lifts for every right corner --- and _cloven fibrations_,
those for which the Cartesian lifts are "algebraic" in a sense.  This is
because, classically, _essentially unique_ means that there are still
some choices to be made, and invoking the axiom of choice makes an
"arbitrary" set of such choices. But, in the presence of univalence,
there is exactly _one_ choice to be made, that is, no choice at all.
Thus, we do not dwell on the distinction.

:::{.definition #fibred-category alias="cartesian-fibration fibration"}
```agda
Cartesian-fibration : Type _
Cartesian-fibration = ∀ {x y} (f : Hom x y) (y' : Ob[ y ]) → Cartesian-lift f y'

module Cartesian-fibration (fib : Cartesian-fibration) where
```
:::

<!--
```agda

  module _ {x y} (f : Hom x y) (y' : Ob[ y ]) where
    open Cartesian-lift (fib f y')
      using ()
      renaming (x' to _^*_; lifting to π*)
      public

  module π* {x y} {f : Hom x y} {y' : Ob[ y ]} where
    open Cartesian-lift (fib f y')
      hiding (x'; lifting)
      public
```
-->

Note that if $\cE$ is a fibration, we can define an operation that
allows us to move vertical morphisms between fibres. This actually
extends to a collection of functors, called [base change functors].
This operation is also definable for [[weak cartesian fibrations]], as it only
uses the universal property that yields a vertical morphism.

[base change functors]: Cat.Displayed.Cartesian.Indexing.html

```agda
  rebase : ∀ {x y y' y''} → (f : Hom x y)
           → Hom[ id ] y' y''
           → Hom[ id ] (f ^* y') (f ^* y'')
  rebase f vert =
    π*.universal' id-comm (vert ∘' π* f _)
```

A Cartesian fibration is a displayed category having Cartesian lifts for
every right corner.

## Why?

Admittedly, the notion of Cartesian morphism is slightly artificial. It
arises from studying the specific properties of the [[pullback functors]]
$f^* : \cC/y \to \cC/x$ which exist in a category of pullbacks,
hence the similarity in universal property!

In fact, the quintessential example of a Cartesian fibration is the
_[[codomain fibration]]_, which is a category displayed over $\cC$,
where the fibre over $x$ is the slice category $\cC/x$. We may
investigate further (to uncover the name "codomain"): the total space of
this fibration is the arrow category $\Arr{\cC}$, and the projection
functor is the codomain functor $\Arr{\cC} \to \cC$.

This displayed category extends to a pseudofunctor exactly when $\cC$
has all pullbacks, because in a world where the vertical arrows are
"_just_" arrows, a Cartesian morphism is exactly a pullback square.

Other examples exist:

- The [family fibration] exhibits any category $\cC$ as displayed
over $\Sets$. The fibres are functor categories (with discrete domains),
reindexing is given by composition.

[family fibration]: Cat.Displayed.Instances.Family.html

- The [category of modules] is fibred over the category of rings. The
fibre over a ring $R$ is the category of $R$-modules, Cartesian lifts
are given by restriction of scalars.

[category of modules]: Algebra.Ring.Module.html
