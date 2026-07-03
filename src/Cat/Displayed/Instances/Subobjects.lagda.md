<!--
```agda
open import Cat.Diagram.Pullback.Properties
open import Cat.Displayed.Cocartesian.Weak
open import Cat.Displayed.Instances.Slice
open import Cat.Displayed.Cocartesian
open import Cat.Displayed.Univalence
open import Cat.Functor.Conservative
open import Cat.Displayed.Cartesian
open import Cat.Functor.Properties
open import Cat.Displayed.Functor
open import Cat.Instances.Functor
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Displayed.Fibre
open import Cat.Instances.Slice
open import Cat.Displayed.Base
open import Cat.Diagram.Image
open import Cat.Prelude

open import Order.Base
open import Order.Cat

import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Displayed.Instances.Subobjects
  {o ℓ} (B : Precategory o ℓ)
  where
```

<!--
```agda
open Cr B
open Displayed
```
-->

# The fibration of subobjects {defines="poset-of-subobjects subobject subobject-fibration"}

Given a base category $\cB$, we can define the [[displayed category]] of
_subobjects_ over $\cB$. This is, in essence, a restriction of the
[[codomain fibration]] of $\cB$, but with our attention restricted to
the monomorphisms $a \mono b$ rather than arbitrary maps $a \to b$.

```agda
record Subobject (y : Ob) : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    {dom} : Ob
    map   : Hom dom y
    monic : is-monic map

open Subobject public
```

To make formalisation smoother, we define our own version of displayed
morphisms in the subobject fibration, rather than reusing those of the
fundamental self-indexing. The reason for this is quite technical: the
type of maps in the self-indexing is only dependent on (the domains and)
the _morphisms_ being considered, meaning nothing constrains the proofs
that these are monomorphisms, causing unification to fail at the
determining the full `Subobject`{.Agda}s involved.

```agda
record ≤-over {x y} (f : Hom x y) (a : Subobject x) (b : Subobject y) : Type ℓ where
  no-eta-equality
  field
    map : Hom (a .dom) (b .dom)
    com : f ∘ Subobject.map a ≡ Subobject.map b ∘ map

open ≤-over public
```

We will denote the type of maps $x' \to_f y'$ in the subobject fibration
by $x' \le_f y'$, since there is at most one such map: if $g, h$ satisfy
$y'g = fx' = y'h$, then, since $y'$ is a mono, $g = h$.

<!--
```agda
{-# INLINE Subobject.constructor #-}
≤-over-is-prop
  : ∀ {x y} {f : Hom x y} {a : Subobject x} {b : Subobject y}
  → (p q : ≤-over f a b)
  → p ≡ q
≤-over-is-prop {f = f} {a} {b} p q = path where
  maps : p .map ≡ q .map
  maps = b .monic (p .map) (q .map) (sym (p .com) ∙ q .com)

  path : p ≡ q
  path i .map = maps i
  path i .com = is-prop→pathp (λ i → Hom-set _ _ (f ∘ a .map) (b .map ∘ maps i)) (p .com) (q .com) i

instance
  H-Level-≤-over
    : ∀ {x y} {f : Hom x y} {a : Subobject x} {b : Subobject y} {n}
    → H-Level (≤-over f a b) (suc n)
  H-Level-≤-over = prop-instance ≤-over-is-prop
```
-->

Setting up the displayed category is now nothing more than routine
verification: the identity map satisfies $\id a = a \id$, and
commutative squares can be pasted together.

```agda
Subobjects : Displayed B (o ⊔ ℓ) ℓ
Subobjects .Ob[_] y = Subobject y
Subobjects .Hom[_]  = ≤-over
Subobjects .Hom[_]-set f a b = hlevel 2

Subobjects .id' .map = id
Subobjects .id' .com = id-comm-sym

Subobjects ._∘'_ α β .map = α .map ∘ β .map
Subobjects ._∘'_ α β .com = pullr (β .com) ∙ extendl (α .com)
```

<!--
```agda
Subobjects .idr' _       = prop!
Subobjects .idl' _       = prop!
Subobjects .assoc' _ _ _ = prop!
Subobjects .hom[_] p f .map = f .map
Subobjects .hom[_] p f .com = ap₂ _∘_ (sym p) refl ∙ f .com
Subobjects .coh[_] p f = prop!

open reflects-cartesian-maps
open Weak-cocartesian-lift
open is-weak-cocartesian
open Displayed-functor
open is-fibred-functor
open Cartesian-lift
open is-cartesian
open Pullback
```
-->

The displayed category of subobjects comes with a forgetful [[vertical
functor]] to the [[fundamental fibration]] of $\cB$.

```agda
Forget-subobjects : Vertical-functor Subobjects (Slices B)
Forget-subobjects .F₀' m = cut (m .map)
Forget-subobjects .F₁' f = record { map = f .map ; com = sym (f .com) }
Forget-subobjects .F-id' = Slice-path refl
Forget-subobjects .F-∘' = Slice-path refl
```

This functor is fully faithful, hence it reflects cartesian morphisms:
a pullback square in $\cB$ determines a cartesian morphism in the
subobject fibration.
In fact, the uniqueness part follows automatically from the uniqueness
of maps in the subobject fibration!

```agda
Forget-sub-full
  : ∀ {a b} {a' : Subobject a} {b' : Subobject b} {f : Hom a b}
  → Slice-hom B f (Forget-subobjects .F₀' a') (Forget-subobjects .F₀' b')
  → ≤-over f a' b'
Forget-sub-full f' = record { map = f' .map ; com = sym (f' .com) }

Forget-sub-reflects-cartesian : reflects-cartesian-maps Forget-subobjects
Forget-sub-reflects-cartesian .reflects cart = record
  { universal = λ m m' → Forget-sub-full
      (cart .universal m (Forget-subobjects .F₁' m'))
  ; commutes = λ _ _ → prop!
  ; unique = λ _ _ → prop!
  }
```

<!--
```agda
pullback→cartesian-sub
  : ∀ {x y x' y'} {f : Hom x y} {f' : ≤-over f x' y'}
  → is-pullback B (x' .map) f (f' .map) (y' .map)
  → is-cartesian Subobjects f f'
pullback→cartesian-sub pb = Forget-sub-reflects-cartesian .reflects
  (pullback→cartesian B pb)
```
-->

## As a fibration

By exactly the same construction as [for the fundamental
self-indexing][codomain], if $\cB$ has pullbacks, the displayed category
we have built is actually a fibration. The construction is slightly
simpler now that we have no need to worry about uniqueness, but we can
remind ourselves of the universal property:

[codomain]: Cat.Displayed.Instances.Slice.html#as-a-fibration

~~~{.quiver}
\[\begin{tikzcd}
  \textcolor{rgb,255:red,214;green,92;blue,92}{u'} \\
  & \textcolor{rgb,255:red,92;green,92;blue,214}{x \times_y y'} && {y'} \\
  \textcolor{rgb,255:red,214;green,92;blue,92}{u} \\
  & x && y
  \arrow[hook, from=2-4, to=4-4]
  \arrow["f"', from=4-2, to=4-4]
  \arrow[color={rgb,255:red,92;green,92;blue,214}, hook, from=2-2, to=4-2]
  \arrow[color={rgb,255:red,92;green,92;blue,214}, from=2-2, to=2-4]
  \arrow["m"', color={rgb,255:red,214;green,92;blue,92}, from=3-1, to=4-2]
  \arrow[color={rgb,255:red,214;green,92;blue,92}, hook, from=1-1, to=3-1]
  \arrow["{\exists!}"', color={rgb,255:red,214;green,92;blue,92}, dashed, from=1-1, to=2-2]
  \arrow["h", color={rgb,255:red,214;green,92;blue,92}, curve={height=-12pt}, from=1-1, to=2-4]
\end{tikzcd}\]
~~~

On the first stage, we are given the data in black: we can complete an
open span $y' \mono y \xot{f} x$ to a Cartesian square (in blue) by
pulling $y'$ back along $f$; this base change remains a monomorphism.
Since a pullback square is cartesian, we are done.

<!--
```agda
module with-pullbacks (pb : has-pullbacks B) where
```
-->

```agda
  -- The blue square:
  pullback-subobject
    : ∀ {X Y} (h : Hom X Y) (g : Subobject Y)
    → Subobject X
  pullback-subobject h g .dom = pb h (g .map) .apex
  pullback-subobject h g .map = pb h (g .map) .p₁
  pullback-subobject h g .monic = mon where abstract
    mon : is-monic (pb h (g .map) .p₁)
    mon = is-monic→pullback-is-monic
      (g .monic) (rotate-pullback (pb h (g .map) .has-is-pb))

  Subobject-fibration : Cartesian-fibration Subobjects
  Subobject-fibration f y' = l where
    it : Pullback _ _ _
    it = pb (y' .map) f
    l : Cartesian-lift Subobjects f y'

    l .x' = pullback-subobject f y'
    l .lifting .map = pb f (y' .map) .p₂
    l .lifting .com = pb f (y' .map) .square

    l .cartesian = Forget-sub-reflects-cartesian .reflects
      (pullback→cartesian B (pb _ _ .has-is-pb))
```

## As a (weak) cocartesian fibration

If $\cB$ has an [[image factorisation]] for every morphism, then its
fibration of subobjects is a weak cocartesian fibration. By a general
fact, if $\cB$ also has pullbacks, then $\Sub(-)$ is a cocartesian
fibration.

```agda
Subobject-weak-opfibration
  : (∀ {x y} (f : Hom x y) → Image B f)
  → Weak-cocartesian-fibration Subobjects
Subobject-weak-opfibration ims f x' = l where
  module im = Image B (ims (f ∘ x' .map))
```

To understand this result, we remind ourselves of the universal property
of an image factorisation for $f : a \to b$: It is the initial subobject
through which $f$ factors. That is to say, if $m : \Sub(b)$ is another
subobject, and $f = me$ for some map $e : a \to m$, then $m \le \im f$.
Summarised diagrammatically, the universal property of an image
factorisation looks like a kite:

~~~{.quiver}
\[\begin{tikzcd}
  a && {\im f} && m \\
  \\
  && b
  \arrow[from=1-1, to=1-3]
  \arrow[hook, from=1-3, to=3-3]
  \arrow["{\exists!}"', dashed, from=1-3, to=1-5]
  \arrow[hook, from=1-5, to=3-3]
  \arrow["e"{description}, curve={height=-18pt}, from=1-1, to=1-5]
  \arrow["f"{description}, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

Now compare this with the universal property required of a weak
co-cartesian lift:

~~~{.quiver}
\[\begin{tikzcd}
  {x'} && {f_!x'} && {u'} \\
  \\
  x && y
  \arrow[hook, from=1-1, to=3-1]
  \arrow["f"', from=3-1, to=3-3]
  \arrow[hook, from=1-3, to=3-3]
  \arrow[hook, from=1-5, to=3-3]
  \arrow[from=1-1, to=1-3]
  \arrow["{\exists!}"', dashed, from=1-3, to=1-5]
  \arrow["h", curve={height=-18pt}, from=1-1, to=1-5]
\end{tikzcd}\]
~~~

By smooshing the corner $x' \mono x \to y$ together (i.e., composing
$x'$ and $f$), we see that this is exactly the kite-shaped universal
property of $\im fx'$.

```agda
  l : Weak-cocartesian-lift Subobjects f x'
  l .y' .dom   = im.Im
  l .y' .map   = im.Im→codomain
  l .y' .monic = im.Im→codomain-is-M

  l .lifting .map = im.corestrict
  l .lifting .com = sym im.image-factors

  l .weak-cocartesian .universal {x' = y'} h .map = im.universal _ (y' .monic) (h .map) (sym (h .com))
  l .weak-cocartesian .universal h .com = idl _ ∙ sym im.universal-factors

  l .weak-cocartesian .commutes g' = prop!
  l .weak-cocartesian .unique _ _  = prop!
```

The aforementioned general fact says that any cartesian and weak
cocartesian fibration must actually be a full opfibration.

```agda
Subobject-opfibration
  : (∀ {x y} (f : Hom x y) → Image B f)
  → (pb : has-pullbacks B)
  → Cocartesian-fibration Subobjects
Subobject-opfibration images pb = fibration+weak-opfibration→opfibration _
  (with-pullbacks.Subobject-fibration pb)
  (Subobject-weak-opfibration images)
```

## Subobjects over a base

We define the category $\Sub(y)$ of subobjects _of $y$_ as a fibre of
the subobject fibration.

```agda
Sub : Ob → Precategory (o ⊔ ℓ) ℓ
Sub y = Fibre Subobjects y

module Sub {y} = Cr (Sub y)
```

<!--
```agda
private variable
  y : Ob
  m n : Subobject y

_≤ₘ_ : ∀ {y} (a b : Subobject y) → Type _
_≤ₘ_ = ≤-over id

open Sub
  renaming (_≅_ to infix 7 _≅ₘ_)
  using (to ; from ; inverses)
  public

infix 7 _≤ₘ_

≤ₘ→monic : ∀ {y} {a b : Subobject y} → (f : a ≤ₘ b) → is-monic (f .map)
≤ₘ→monic {a = a} f g h α = a .monic g h $
  a .map ∘ g      ≡⟨ ap (_∘ g) (introl refl ∙ f .com) ∙ pullr refl ⟩
  _ ∘ f .map ∘ g  ≡⟨ ap₂ _∘_ refl α ⟩
  _ ∘ f .map ∘ h  ≡⟨ pulll (sym (f .com) ∙ idl _) ⟩
  a .map ∘ h      ∎

≤ₘ→mono : ∀ {y} {a b : Subobject y} → a ≤ₘ b → a .dom ↪ b .dom
≤ₘ→mono f .mor = f .map
≤ₘ→mono {a = a} f .monic = ≤ₘ→monic f

cutₛ : ∀ {x y} {f : Hom x y} → is-monic f → Subobject y
cutₛ x .dom   = _
cutₛ x .map   = _
cutₛ x .monic = x

Sub-antisym : m ≤ₘ n → n ≤ₘ m → m ≅ₘ n
Sub-antisym f g = Sub.make-iso f g prop! prop!
```
-->

There is an evident fully faithful functor from $\Sub(y) \to \cB/y$ that
forgets the property of being monic.

```agda
Sub→Slice : ∀ y → Functor (Sub y) (Slice B y)
Sub→Slice y .Functor.F₀ m = cut (m .map)
Sub→Slice y .Functor.F₁ f = record { map = f .map ; com = sym (f .com) ∙ idl _ }
Sub→Slice y .Functor.F-id = ext refl
Sub→Slice y .Functor.F-∘ _ _ = ext refl

Sub→Slice-is-ff
  : ∀ y → is-fully-faithful (Sub→Slice y)
Sub→Slice-is-ff y = is-iso→is-equiv λ where
  .is-iso.from m → record { map = m ./-Hom.map ; com = idl _ ∙ sym (m ./-Hom.com) }
  .is-iso.rinv m → ext refl
  .is-iso.linv m → prop!
```

Composing this with the forgetful functor $\cB/y \to \cB$, we obtain a
projection $\Sub(y) \to \cB$. As both forgetful functors are
[[conservative]], so is the projection, which concretely means that
we can construct isomorphisms in $\Sub(y)$ from isomorphisms in $\cB$.

```agda
Sub-cod : ∀ y → Functor (Sub y) B
Sub-cod y = Forget/ F∘ Sub→Slice y

Sub→Slice-conservative
  : ∀ y → is-conservative (Sub→Slice y)
Sub→Slice-conservative y = is-ff→is-conservative
  (Sub→Slice y) (Sub→Slice-is-ff y) _

Sub-cod-conservative
  : ∀ y → is-conservative (Sub-cod y)
Sub-cod-conservative y = F∘-is-conservative Forget/ (Sub→Slice y)
  Forget/-is-conservative
  (Sub→Slice-conservative y)

invertible→≅ₘ
  : (f : m ≤ₘ n)
  → is-invertible (f .map)
  → m ≅ₘ n
invertible→≅ₘ f inv = Sub.invertible→iso f (Sub-cod-conservative _ inv)
```

<!--
```agda
iso→≅ₘ
  : (is : m .dom ≅ n .dom)
  → m .map ≡ n .map ∘ is .to
  → m ≅ₘ n
iso→≅ₘ is com = invertible→≅ₘ
  (record { map = is .to ; com = idl _ ∙ com })
  (iso→invertible is)

≅ₘ→iso : m ≅ₘ n → m .dom ≅ n .dom
≅ₘ→iso p = F-map-iso (Sub-cod _) p

Sub-path
  : ∀ {y} {a b : Subobject y}
  → (p : a .dom ≡ b .dom)
  → PathP (λ i → Hom (p i) y) (a .map) (b .map)
  → a ≡ b
Sub-path p q i .dom = p i
Sub-path p q i .map = q i
Sub-path {a = a} {b = b} p q i .monic {c} =
  is-prop→pathp (λ i → Π-is-hlevel³ 1 λ (g h : Hom c (p i)) (_ : q i ∘ g ≡ q i ∘ h) → Hom-set _ _ g h)
    (a .monic) (b .monic) i
```
-->

## Fibrewise cartesian structure

Finite products in $\Sub(y)$ are [[created|created limit]] by the
projection to $\cB/y$; in other words, they are computed just like
[[finite products in $\cB/y$|finite limits in slices]]. We spell them
out explicitly.

The greatest element ([[terminal object]]) $\top$ in $\Sub(y)$ is given
by the identity monomorphism $y \mono y$.

```agda
⊤ₘ : ∀ {y} → Subobject y
⊤ₘ .dom   = _
⊤ₘ .map   = id
⊤ₘ .monic = id-monic

opaque
  !ₘ : ∀ {y} {m : Subobject y} → m ≤ₘ ⊤ₘ
  !ₘ {m = m} = record { map = m .map ; com = refl }

Sub-terminal : ∀ {y} → Terminal (Sub y)
Sub-terminal .Terminal.top = ⊤ₘ
Sub-terminal .Terminal.has⊤ m = contr !ₘ λ _ → prop!
```

Since products in slice categories are given by pullbacks, and pullbacks
preserve monomorphisms, if $\cB$ has pullbacks, then $\Sub(y)$ has
products, regardless of what $y$ is. Given two subobjects $\alpha, \beta
: \Sub(y)$, we write their product as $\alpha \cap \beta$ and think of
it as their *intersection*.

```agda
Sub-products
  : ∀ {y}
  → has-pullbacks B
  → has-products (Sub y)
Sub-products {y} pb a b = prod where
  it = pb (a .map) (b .map)

  prod : Product (Sub y) a b
  prod .Product.apex .dom = it .apex
  prod .Product.apex .map = a .map ∘ it .p₁
  prod .Product.apex .monic = ∘-is-monic
    (a .monic)
    (is-monic→pullback-is-monic (b .monic) (rotate-pullback (it .has-is-pb)))

  prod .Product.π₁ .map = it .p₁
  prod .Product.π₁ .com = idl _

  prod .Product.π₂ .map = it .p₂
  prod .Product.π₂ .com = idl _ ∙ it .square

  prod .Product.has-is-product .is-product.⟨_,_⟩ q≤a q≤b .map =
    it .Pullback.universal {p₁' = q≤a .map} {p₂' = q≤b .map} (sym (q≤a .com) ∙ q≤b .com)
  prod .Product.has-is-product .is-product.⟨_,_⟩ q≤a q≤b .com =
    idl _ ∙ sym (pullr (it .p₁∘universal) ∙ sym (q≤a .com) ∙ idl _)
  prod .Product.has-is-product .is-product.π₁∘⟨⟩ = prop!
  prod .Product.has-is-product .is-product.π₂∘⟨⟩ = prop!
  prod .Product.has-is-product .is-product.unique _ _ = prop!
```

## Univalence

Since identity of $m, n : \Sub(y)$ is given by identity of the
underlying objects and identity-over of the corresponding morphisms, if
$\cB$ is univalent, we can conclude that $\Sub(y)$ is, too. Since
$\Sub(y)$ is always thin, we can summarise the situation by saying that
$\Sub(y)$ is a [[partial order]] if $\cB$ is univalent.

```agda
Sub-is-category : ∀ {y} → is-category B → is-category (Sub y)
Sub-is-category b-cat .to-path {a} {b} x =
  Sub-path
    (b-cat .to-path i)
    (Univalent.Hom-pathp-refll-iso b-cat (sym (x .Sub.from .com) ∙ idl _))
  where
    i : a .dom ≅ b .dom
    i = make-iso (x .Sub.to .map) (x .Sub.from .map) (ap map (Sub.invl x)) (ap map (Sub.invr x))
Sub-is-category b-cat .to-path-over p =
  Sub.≅-pathp refl _ prop!
```

As a consequence, the collection of subobjects of any object of a
univalent category forms a [[set]].

```agda
Subobject-is-set : is-category B → ∀ {A} → is-set (Subobject A)
Subobject-is-set b-cat {A} = Poset.Ob-is-set $
  thin→poset (Sub A) (λ _ _ → ≤-over-is-prop) (Sub-is-category b-cat)
```
