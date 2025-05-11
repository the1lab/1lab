<!--
```agda
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Displayed.Morphism
import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Cartesian
  {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ') where

open Cat.Reasoning B
open Cat.Displayed.Reasoning E
open Cat.Displayed.Morphism E

open Total-hom
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
record is-cartesian
  {a b a' b'}
  (f : Hom a b) (f' : Hom[ f ] a' b')
  : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ')
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
    universal
      : ∀ {x x'} (h : Hom x a) (h' : Hom[ f ∘ h ] x' b') → Hom[ h ] x' a'
    commutes
      : ∀ {x x'} (h : Hom x a) (h' : Hom[ f ∘ h ] x' b')
      → f' ∘' universal h h' ≡ h'
    unique
      : ∀ {x x'} {h : Hom x a} {h' : Hom[ f ∘ h ] x' b'}
      → {other' : Hom[ h ] x' a'}
      → f' ∘' other' ≡ h'
      → other' ≡ universal h h'
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
  opaque
    unfolding hom[_]

    universalp
      : ∀ {x x'} {h : Hom x a} {h' h'' : Hom[ f ∘ h ] x' b'}
      → h' ∫≡ h''
      → universal h h' ∫≡ universal h h''
    universalp {h = h} p = path! (apd (λ i → universal h) (cast[] (ap preserves p)))

    uniquep
      : ∀ {x x'} {h k : Hom x a} {h' : Hom[ f ∘ h ] x' b'}
      → {other' : Hom[ k ] x' a'}
      → (p : h ≡ k)
      → f' ∘' other' ∫≡ h'
      → other' ∫≡ universal h h'
    uniquep {x = x} {x' = x'} {h = h} {h' = h'} {other' = other'} p q =
      other'                 ≡[]⟨ wrapped.to refl ⟩
      hom[ p ]⁻ other'       ≡[]⟨ path! (unique ((over[] ((∫.refl⟩∘⟨ unwrapped.to refl) ∙ q)))) ⟩
      universal h h'         ∎[]

    uniquep₂
      : ∀ {x x'} {h k₁ k₂ : Hom x a} {h' : Hom[ f ∘ h ] x' b'}
      → {other₁' : Hom[ k₁ ] x' a'} {other₂' : Hom[ k₂ ] x' a'}
      → (p : h ≡ k₁) (q : h ≡ k₂)
      → f' ∘' other₁' ∫≡ h'
      → f' ∘' other₂' ∫≡ h'
      → other₁' ∫≡ other₂'
    uniquep₂ p q r s = uniquep p r ∙ sym (uniquep q s)
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
    cart' .unique (cart .commutes _ _) i
  worker i .commutes m h' =
    is-set→squarep (λ _ _ → Hom[ _ ]-set _ _)
      (ap (f' ∘'_) (cart' .unique _))
      (cart .commutes m h')
      (cart' .commutes m h')
      refl i
  worker i .unique p =
    is-set→squarep (λ _ _ → Hom[ _ ]-set _ _)
      refl
      (cart .unique p)
      (cart' .unique p)
      (cart' .unique _) i
```
</details>

<!--
```agda
instance
  H-Level-is-cartesian
    : ∀ {x y x' y'} {f : Hom x y} {f' : Hom[ f ] x' y'} {n}
    → H-Level (is-cartesian f f') (suc n)
  H-Level-is-cartesian = prop-instance is-cartesian-is-prop
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

## Orthogonal factorisations

```agda
cartesian-orthogonal
  : ∀ {a x y} {a' b' x' y'}
  → {u : Hom a y} {v : Hom x y} {w : Hom a x}
  → {l' : Hom[ id ] a' b'} {r' : Hom[ v ] x' y'}
  → {f' : Hom[ u ] b' y'} {g' : Hom[ w ] a' x'}
  → {p : u ∘ id ≡ v ∘ w}
  → f' ∘' l' ≡[ p ] r' ∘' g'
  → is-cartesian v r'
  → is-contr (Σ[ α ∈ Hom[ w ] b' x' ] (α ∘' l' ≡[ idr _ ] g' × r' ∘' α ≡[ sym p ∙ idr _ ] f'))
cartesian-orthogonal {b' = b'} {x' = x'} {w = w} {l' = l'} {r' = r'} {f' = f'} {g' = g'} {p = p} q r'-cart =
  contr (filler , over[] filler∘l , over[] r∘filler) λ where
    (k' , k∘l=g , r∘k=f) →
      Σ-prop-path! $
      over[] $ uniquep₂ refl refl (wrapped.to {p = sym (idr _) ∙ p} r∘filler) (wrapped.to (path! r∘k=f))
  where
    open is-cartesian r'-cart

    filler : Hom[ w ] b' x'
    filler = universal w (hom[ sym (idr _) ∙ p ] f')

    r∘filler : r' ∘' filler ∫≡ f'
    r∘filler =
      r' ∘' filler ≡[]⟨ wrapped.from (path! (commutes _ _)) ⟩
      f'           ∎[]

    filler∘l : filler ∘' l' ∫≡ g'
    filler∘l =
      uniquep₂ (sym (idr _)) refl
        (∫.pulll r∘filler ∙ path! q)
        refl
```


-- ## Properties of cartesian morphisms

-- The composite of 2 cartesian morphisms is in turn cartesian.

-- ```agda
-- cartesian-∘
--   : ∀ {x y z} {f : Hom y z} {g : Hom x y}
--   → ∀ {x' y' z'} {f' : Hom[ f ] y' z'} {g' : Hom[ g ] x' y'}
--   → is-cartesian f f' → is-cartesian g g'
--   → is-cartesian (f ∘ g) (f' ∘' g')
-- cartesian-∘ {f = f} {g = g} {f' = f'} {g' = g'} f-cart g-cart = fg-cart where

--   module f' = is-cartesian f-cart
--   module g' = is-cartesian g-cart

--   fg-cart : is-cartesian (f ∘ g) (f' ∘' g')
--   fg-cart .is-cartesian.universal h h' =
--     g'.universal h (f'.universal (g ∘ h) (hom[ assoc f g h ]⁻ h'))
--   fg-cart .is-cartesian.commutes m h' =
--     begin[]
--       (f' ∘' g') ∘' g'.universal _ (f'.universal _ (hom[] h')) ≡[]⟨ ∫.pullr (path! (g'.commutes _ _)) ⟩
--       f' ∘' f'.universal _ (hom[] h')                          ≡[]⟨ wrapped.from (path! (f'.commutes (g ∘ m) (hom[] h'))) ⟩
--       h'                                                       ∎[]
--   fg-cart .is-cartesian.unique {h = h} {h' = h'} {other' = other'} p =
--     g'.unique $ f'.unique $
--     begin[]
--       f' ∘' g' ∘' other' ≡[]⟨ wrapped.to (∫.reassocl.to (path! p)) ⟩
--       hom[] h'           ∎[]

-- _∘cart_
--   : ∀ {x y z x' y' z'} {f : Hom y z} {g : Hom x y}
--   → Cartesian-morphism f y' z' → Cartesian-morphism g x' y'
--   → Cartesian-morphism (f ∘ g) x' z'
-- f' ∘cart g' = fg' where
--   open Cartesian-morphism

--   fg' : Cartesian-morphism _ _ _
--   fg' .hom' = f' .hom' ∘' g' .hom'
--   fg' .cartesian = cartesian-∘ (f' .cartesian) (g' .cartesian)
-- ```

-- Furthermore, the identity morphism is cartesian.

-- ```agda
-- cartesian-id : ∀ {x x'} → is-cartesian id (id' {x} {x'})
-- cartesian-id .is-cartesian.universal m h' = hom[ idl m ] h'
-- cartesian-id .is-cartesian.commutes m h' =
--   begin[]
--     id' ∘' hom[] h' ≡[]⟨ ∫.idl _ ⟩
--     hom[] h'        ≡[]⟨ unwrapped.to refl ⟩
--     h'              ∎[]
-- cartesian-id .is-cartesian.unique {h' = h'} {other' = other'} p =
--   begin[]
--     other'        ≡[]˘⟨ ∫.idl _ ⟩
--     id' ∘' other' ≡[]⟨ wrapped.to (path! p) ⟩
--     hom[] h'      ∎[]

-- idcart : ∀ {x} {x' : Ob[ x ]} → Cartesian-morphism id x' x'
-- idcart .Cartesian-morphism.hom' = id'
-- idcart .Cartesian-morphism.cartesian = cartesian-id
-- ```


-- In fact, every invertible map is also cartesian, as we can use
-- the inverse to construct the requisite factorisation.

-- ```agda
-- invertible→cartesian
--   : ∀ {x y} {f : Hom x y} {x' y'} {f' : Hom[ f ] x' y'}
--   → (f-inv : is-invertible f)
--   → is-invertible[ f-inv ] f'
--   → is-cartesian f f'
-- invertible→cartesian
--  {f = f} {f' = f'} f-inv f'-inv = f-cart where
--   module f = is-invertible f-inv
--   module f' = is-invertible[_] f'-inv

--   f-cart : is-cartesian f f'
--   f-cart .is-cartesian.universal m h' =
--     hom[ cancell f.invr ] (f'.inv' ∘' h')
--   f-cart .is-cartesian.commutes m h' =
--     begin[]
--       f' ∘' hom[] (f'.inv' ∘' h') ≡[]⟨ ∫.refl⟩∘⟨ unwrapped.to refl ⟩
--       f' ∘' f'.inv' ∘' h'         ≡[]⟨ ∫.cancell (path! f'.invl') ⟩
--       h'                          ∎[]
--   f-cart .is-cartesian.unique {h' = h'} {other' = other'} p =
--     begin[]
--       other'                    ≡[]⟨ ∫.introl (path! f'.invr') ⟩
--       (f'.inv' ∘' f') ∘' other' ≡[]⟨ wrapped.to (∫.pullr (path! p)) ⟩
--       hom[] (f'.inv' ∘' h')     ∎[]
-- ```

-- <!--
-- ```agda
-- iso→cartesian
--   : ∀ {x y x' y'} {f : x ≅ y}
--   → (f' : x' ≅[ f ] y')
--   → is-cartesian (f .to) (f' .to')
-- iso→cartesian {f = f} f' =
--   invertible→cartesian (iso→invertible f) (iso[]→invertible[] f')
-- ```
-- -->

-- If $f$ is cartesian, it's also a [weak monomorphism].

-- [weak monomorphism]: Cat.Displayed.Morphism.html#weak-monos

-- ```agda
-- cartesian→weak-monic
--   : ∀ {x y} {f : Hom x y}
--   → ∀ {x' y'} {f' : Hom[ f ] x' y'}
--   → is-cartesian f f'
--   → is-weak-monic f'
-- cartesian→weak-monic {f = f} {f' = f'} f-cart g' g'' p p' =
--   over[] $ uniquep₂ (sym p) refl
--     (path! p')
--     refl
--   where
--     open is-cartesian f-cart
-- ```

-- We can use this fact to show that 2 cartesian lifts over the same
-- morphisms must have their domains related by a vertical isomorphism.
-- Suppose they're called $f_1$ and $f_2$, and fit into a diagram like the
-- one below.

-- ~~~{.quiver}
-- \[\begin{tikzcd}
--   {a_2'} \\
--   & {a_1'} && {b'} \\
--   \\
--   a & a && b
--   \arrow["{f_2}", curve={height=-12pt}, from=1-1, to=2-4]
--   \arrow["{f_1}", from=2-2, to=2-4]
--   \arrow["f"', from=4-2, to=4-4]
--   \arrow[from=2-4, to=4-4]
--   \arrow[lies over, from=2-2, to=4-2]
--   \arrow[lies over, from=1-1, to=4-1]
--   \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=4-4]
--   \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=2-2, to=4-4]
--   \arrow[Rightarrow, no head, from=4-1, to=4-2]
-- \end{tikzcd}\]
-- ~~~

-- Since $f_1$ and $f_2$ are both Cartesian morphisms, we can factor $f_2$
-- through $a_1'$ by a map $g$, and conversely, $f_1$ through $a_2'$ by
-- $h$.

-- ~~~{.quiver}
-- \[\begin{tikzcd}
--   {a_2'} \\
--   {a_1'} & b'
--   \arrow["g"', shift right=2, dashed, from=1-1, to=2-1]
--   \arrow["h"', shift right=2, dashed, from=2-1, to=1-1]
--   \arrow["{f_1}"', from=2-1, to=2-2]
--   \arrow["{f_2}", from=1-1, to=2-2]
-- \end{tikzcd}\]
-- ~~~

-- Since we're trying to prove that $h$ is an isomorphism, we want to show
-- that $hg=\mathrm{id}_{a_2'}$. We know that $f_2$ factors through $a'_2$,
-- its own domain, via the identity map. We will show that it also factors
-- through $hg$ to show that the two are equal, by the universal property
-- of $f_2$ being Cartesian. Consider the following diagram:

-- ~~~{.quiver}
-- \[\begin{tikzcd}
--   {a_2'} & b' \\
--   {a_1'} & {a_2'}
--   \arrow["g"', shift right=2, dashed, from=1-1, to=2-1]
--   \arrow["{f_1}"', from=2-1, to=1-2]
--   \arrow["{f_2}", from=1-1, to=1-2]
--   \arrow["h"', shift right=2, dashed, from=2-1, to=2-2]
--   \arrow["{f_2}"', from=2-2, to=1-2]
--   \arrow["{\mathrm{id}}"{description, pos=0.2}, curve={height=12pt}, dashed, from=1-1, to=2-2]
-- \end{tikzcd}\]
-- ~~~

-- We have $f_2hg = f_1g = f_2$. A symmetric argument shows that $gh$ is
-- also the identity, so $h : a_1' \cong a_2'$.

-- ```agda
-- cartesian-domain-unique
--   : ∀ {x y} {f : Hom x y}
--   → ∀ {x' x'' y'} {f' : Hom[ f ] x' y'} {f'' : Hom[ f ] x'' y'}
--   → is-cartesian f f'
--   → is-cartesian f f''
--   → x' ≅↓ x''
-- cartesian-domain-unique {f = f} {f' = f'} {f'' = f''} f'-cart f''-cart =
--   make-iso[ id-iso ] to* from* invl* invr*
--   where
--     module f' = is-cartesian f'-cart
--     module f'' = is-cartesian f''-cart

--     to* = f''.universal id (hom[ idr f ]⁻ f')
--     from* = f'.universal id (hom[ idr f ]⁻ f'')

--     invl* : to* ∘' from* ≡[ idl id ] id'
--     invl* =
--       cartesian→weak-monic f''-cart (to* ∘' from*) id' (idl id) $
--       begin[]
--         f'' ∘' to* ∘' from* ≡[]⟨ ∫.pulll (wrapped.from (path! (f''.commutes _ _))) ⟩
--         f' ∘' from*         ≡[]⟨ wrapped.from (path! (f'.commutes _ _)) ⟩
--         f''                 ≡[]˘⟨ ∫.idr _ ⟩
--         f'' ∘' id'          ∎[]

--     invr* : from* ∘' to* ≡[ idl id ] id'
--     invr* =
--       cartesian→weak-monic f'-cart (from* ∘' to*) id' (idl id) $
--       begin[]
--         f' ∘' from* ∘' to* ≡[]⟨ ∫.pulll (wrapped.from (path! (f'.commutes _ _))) ⟩
--         f'' ∘' to*         ≡[]⟨ wrapped.from (path! (f''.commutes _ _)) ⟩
--         f'                 ≡[]˘⟨ ∫.idr _ ⟩
--         f' ∘' id'          ∎[]
-- ```

-- Cartesian morphisms are also stable under vertical retractions.

-- ```agda
-- cartesian-vertical-retraction-stable
--   : ∀ {x y} {f : Hom x y}
--   → ∀ {x' x'' y'} {f' : Hom[ f ] x' y'} {f'' : Hom[ f ] x'' y'} {ϕ : Hom[ id ] x' x''}
--   → is-cartesian f f'
--   → has-section↓ ϕ
--   → f'' ∘' ϕ ∫≡ f'
--   → is-cartesian f f''
-- cartesian-vertical-retraction-stable {f' = f'} {f''} {ϕ} f-cart ϕ-sect factor = f''-cart where
--   open is-cartesian f-cart
--   module ϕ = has-section[_] ϕ-sect

--   f''-cart : is-cartesian _ f''
--   f''-cart .is-cartesian.universal h h' =
--     hom[ idl h ] (ϕ ∘' universal h h')
--   f''-cart .is-cartesian.commutes h h' =
--     begin[]
--       f'' ∘' (hom[] (ϕ ∘' universal h h')) ≡[]⟨ (∫.refl⟩∘⟨ unwrapped.to refl) ∙ ∫.pulll factor ⟩
--       f' ∘' universal h h'                 ≡[]⟨ path! (commutes h h') ⟩
--       h'                                   ∎[]
--   f''-cart .is-cartesian.unique {h = h} {h' = h'} {other' = other'} p =
--     {!!}
--     -- from-pathp⁻ $ (post-section' ϕ-sect {!!})
--     -- from-pathp⁻ $ post-section' ϕ-sect $
--     -- uniquep₂ _ (idl m) refl (ϕ.section' ∘' m') (universal m h')
--     --   unique-lemma
--     --   (commutes m h')
--     -- where
--     --   unique-lemma : f' ∘' ϕ.section' ∘' m' ≡[ _ ] h'
--     --   unique-lemma =
--     --     f' ∘' ϕ.section' ∘' m' ≡[]⟨ pulll[] _ (symP (pre-section[] ϕ-sect factor)) ⟩
--     --     f'' ∘' m'              ≡[]⟨ p ⟩
--     --     h'                     ∎
-- ```

-- -- If $f' \circ g'$ is cartesian and $f'$ is a [[weak monomorphism]],
-- -- then $g'$ is cartesian.

-- -- ```agda
-- -- cartesian-weak-monic-cancell
-- --   : ∀ {x y z} {f : Hom y z} {g : Hom x y}
-- --   → ∀ {x' y' z'} {f' : Hom[ f ] y' z'} {g' : Hom[ g ] x' y'}
-- --   → is-weak-monic f'
-- --   → is-cartesian (f ∘ g) (f' ∘' g')
-- --   → is-cartesian g g'
-- -- cartesian-weak-monic-cancell {f = f} {g = g} {f' = f'} {g' = g'} f-weak-mono fg-cart = g-cart where
-- --   module fg = is-cartesian fg-cart
-- --   open is-cartesian

-- --   g-cart : is-cartesian g g'
-- --   g-cart .universal m h' =
-- --     fg.universal' (sym (assoc f g m)) (f' ∘' h')
-- --   g-cart .commutes m h' =
-- --     f-weak-mono (g' ∘' fg.universal' _ (f' ∘' h')) h' refl $
-- --     cast[] $
-- --       f' ∘' g' ∘' fg.universal' _ (f' ∘' h')   ≡[]⟨ assoc' _ _ _ ⟩
-- --       (f' ∘' g') ∘' fg.universal' _ (f' ∘' h') ≡[]⟨ fg.commutesp (sym (assoc f g m)) (f' ∘' h') ⟩
-- --       f' ∘' h'                                 ∎
-- --   g-cart .unique {m = m} m' p =
-- --     fg.uniquep (sym (assoc f g m)) refl (sym (assoc f g m)) m' (pullr' refl p)
-- -- ```

-- -- As a corollary, we get the following useful pasting lemma, which
-- -- generalizes the [[pasting law for pullbacks]].

-- -- ```agda
-- -- cartesian-cancell
-- --   : ∀ {x y z} {f : Hom y z} {g : Hom x y}
-- --   → ∀ {x' y' z'} {f' : Hom[ f ] y' z'} {g' : Hom[ g ] x' y'}
-- --   → is-cartesian f f'
-- --   → is-cartesian (f ∘ g) (f' ∘' g')
-- --   → is-cartesian g g'
-- -- cartesian-cancell f-cart fg-cart =
-- --   cartesian-weak-monic-cancell (cartesian→weak-monic f-cart) fg-cart
-- -- ```

-- -- We can prove a similar fact for bundled cartesian morphisms.

-- -- ```agda
-- -- cart-paste
-- --   : ∀ {x y z x' y' z'} {f : Hom y z} {g : Hom x y}
-- --   → Cartesian-morphism f y' z'
-- --   → Cartesian-morphism (f ∘ g) x' z'
-- --   → Cartesian-morphism g x' y'
-- -- cart-paste {x' = x'} {y' = y'} {f = f} {g = g} f' fg' = g' where
-- --   open Cartesian-morphism
-- --   open is-cartesian
-- --   module f' = is-cartesian (f' .cartesian)
-- --   module fg' = is-cartesian (fg' .cartesian)

-- --   g' : Cartesian-morphism g x' y'
-- --   g' .hom' = f'.universal g (fg' .hom')
-- --   g' .cartesian =
-- --     cartesian-cancell (f' .cartesian) $
-- --     subst-is-cartesian refl (sym (f'.commutes g (fg' .hom'))) (fg' .cartesian)
-- -- ```

-- -- If a morphism is both vertical and cartesian, then it must be an
-- -- isomorphism. We can construct the inverse by factorizing the identity
-- -- morphism, which is possible due to the fact that $f'$ is vertical.

-- -- ```agda
-- -- vertical+cartesian→invertible
-- --   : ∀ {x} {x' x'' : Ob[ x ]} {f' : Hom[ id ] x' x''}
-- --   → is-cartesian id f'
-- --   → is-invertible↓ f'
-- -- vertical+cartesian→invertible {x' = x'} {x'' = x''} {f' = f'} f-cart =
-- --   make-invertible↓ f⁻¹'  f'-invl f'-invr where
-- --     open is-cartesian f-cart

-- --     f⁻¹' : Hom[ id ] x'' x'
-- --     f⁻¹' = universal' (idl _) id'

-- --     f'-invl : f' ∘' f⁻¹' ≡[ idl _ ] id'
-- --     f'-invl = commutesp _ id'

-- --     path : f' ∘' f⁻¹' ∘' f' ≡[ elimr (idl _) ] f'
-- --     path = cancell' (idl _) (commutesp (idl _) id')

-- --     f'-invr : f⁻¹' ∘' f' ≡[ idl _ ] id'
-- --     f'-invr =
-- --       uniquep₂ _ _ _ (f⁻¹' ∘' f') id'
-- --         (cancell[] _ f'-invl)
-- --         (idr' f')
-- -- ```

-- -- Furthermore, $f' : x' \to_{f} y'$ is cartesian if and only if the
-- -- function $f \cdot' -$ is an equivalence.

-- -- ```agda
-- -- postcompose-equiv→cartesian
-- --   : ∀ {x y x' y'} {f : Hom x y}
-- --   → (f' : Hom[ f ] x' y')
-- --   → (∀ {w w'} {g : Hom w x} → is-equiv {A = Hom[ g ] w' x'} (f' ∘'_))
-- --   → is-cartesian f f'
-- -- postcompose-equiv→cartesian f' eqv .is-cartesian.universal m h' =
-- --   equiv→inverse eqv h'
-- -- postcompose-equiv→cartesian f' eqv .is-cartesian.commutes m h' =
-- --   equiv→counit eqv h'
-- -- postcompose-equiv→cartesian f' eqv .is-cartesian.unique m' p =
-- --   sym (equiv→unit eqv m') ∙ ap (equiv→inverse eqv) p

-- -- cartesian→postcompose-equiv
-- --   : ∀ {x y z x' y' z'} {f : Hom y z} {g : Hom x y} {f' : Hom[ f ] y' z'}
-- --   → is-cartesian f f'
-- --   → is-equiv {A = Hom[ g ] x' y'} (f' ∘'_)
-- -- cartesian→postcompose-equiv cart =
-- --   is-iso→is-equiv $
-- --     iso (universal _)
-- --         (commutes _)
-- --         (λ g' → sym (unique g' refl))
-- --   where open is-cartesian cart
-- -- ```


-- -- ## Cartesian lifts {defines="cartesian-lift"}

-- -- We call an object $y'$ over $y$ together with a Cartesian arrow $f' : x'
-- -- \to y'$ a _Cartesian lift_ of $f$. Cartesian lifts, defined by universal
-- -- property as they are, are unique when they exist, so that "having
-- -- Cartesian lifts" is a _property_, not a structure.

-- -- ```agda
-- -- record
-- --   Cartesian-lift {x y} (f : Hom x y) (y' : Ob[ y ]) : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ')
-- --   where
-- --   no-eta-equality
-- --   field
-- --     {x'}      : Ob[ x ]
-- --     lifting   : Hom[ f ] x' y'
-- --     cartesian : is-cartesian f lifting
-- --   open is-cartesian cartesian public
-- -- ```

-- -- We note that the classical literature often differentiates between
-- -- _fibrations_ --- those displayed categories for which _there exist_
-- -- Cartesian lifts for every right corner --- and _cloven fibrations_,
-- -- those for which the Cartesian lifts are "algebraic" in a sense.  This is
-- -- because, classically, _essentially unique_ means that there are still
-- -- some choices to be made, and invoking the axiom of choice makes an
-- -- "arbitrary" set of such choices. But, in the presence of univalence,
-- -- there is exactly _one_ choice to be made, that is, no choice at all.
-- -- Thus, we do not dwell on the distinction.

-- -- :::{.definition #fibred-category alias="cartesian-fibration fibration"}
-- -- ```agda
-- -- Cartesian-fibration : Type _
-- -- Cartesian-fibration = ∀ {x y} (f : Hom x y) (y' : Ob[ y ]) → Cartesian-lift f y'

-- -- module Cartesian-fibration (fib : Cartesian-fibration) where
-- -- ```
-- -- :::

-- -- <!--
-- -- ```agda

-- --   module _ {x y} (f : Hom x y) (y' : Ob[ y ]) where
-- --     open Cartesian-lift (fib f y')
-- --       using ()
-- --       renaming (x' to _^*_; lifting to π*)
-- --       public

-- --   module π* {x y} {f : Hom x y} {y' : Ob[ y ]} where
-- --     open Cartesian-lift (fib f y')
-- --       hiding (x'; lifting)
-- --       public
-- -- ```
-- -- -->

-- -- Note that if $\cE$ is a fibration, we can define an operation that
-- -- allows us to move vertical morphisms between fibres. This actually
-- -- extends to a collection of functors, called [base change functors].
-- -- This operation is also definable for [[weak cartesian fibrations]], as it only
-- -- uses the universal property that yields a vertical morphism.

-- -- [base change functors]: Cat.Displayed.Cartesian.Indexing.html

-- -- ```agda
-- --   rebase : ∀ {x y y' y''} → (f : Hom x y)
-- --            → Hom[ id ] y' y''
-- --            → Hom[ id ] (f ^* y') (f ^* y'')
-- --   rebase f vert =
-- --     π*.universal' id-comm (vert ∘' π* f _)
-- -- ```

-- -- A Cartesian fibration is a displayed category having Cartesian lifts for
-- -- every right corner.

-- -- ## Why?

-- -- Admittedly, the notion of Cartesian morphism is slightly artificial. It
-- -- arises from studying the specific properties of the [[pullback functors]]
-- -- $f^* : \cC/y \to \cC/x$ which exist in a category of pullbacks,
-- -- hence the similarity in universal property!

-- -- In fact, the quintessential example of a Cartesian fibration is the
-- -- _[[codomain fibration]]_, which is a category displayed over $\cC$,
-- -- where the fibre over $x$ is the slice category $\cC/x$. We may
-- -- investigate further (to uncover the name "codomain"): the total space of
-- -- this fibration is the arrow category $\Arr{\cC}$, and the projection
-- -- functor is the codomain functor $\Arr{\cC} \to \cC$.

-- -- This displayed category extends to a pseudofunctor exactly when $\cC$
-- -- has all pullbacks, because in a world where the vertical arrows are
-- -- "_just_" arrows, a Cartesian morphism is exactly a pullback square.

-- -- Other examples exist:

-- -- - The [family fibration] exhibits any category $\cC$ as displayed
-- -- over $\Sets$. The fibres are functor categories (with discrete domains),
-- -- reindexing is given by composition.

-- -- [family fibration]: Cat.Displayed.Instances.Family.html

-- -- - The [category of modules] is fibred over the category of rings. The
-- -- fibre over a ring $R$ is the category of $R$-modules, Cartesian lifts
-- -- are given by restriction of scalars.

-- -- [category of modules]: Algebra.Ring.Module.html
