<!--
```agda
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module
  Cat.Displayed.Reasoning
    {o' ℓ' o'' ℓ''}
    {B : Precategory o' ℓ'}
    (E : Displayed B o'' ℓ'')
  where
```

<!--
```agda
open Total-hom
```
-->

# Reasoning in displayed categories

Contrary to the [reasoning combinators for precategories][catr],
reasoning in a [[displayed category]] is _much_ harder. The core of the
problem is that the type `Displayed.Hom[_]`{.Agda} of displayed
morphisms is _dependent_, so all but the most trivial paths over it will
similarly be `dependent paths`{.Agda ident=PathP}.

[catr]: Cat.Reasoning.html

```agda
private
  module B = Cat.Reasoning B

module ∫ = Cat.Reasoning (∫ E)

open Displayed E public
open ∫
  hiding (Ob; Hom; id; _∘_)

private variable
  x y z : B.Ob
  x' y' z' : Ob[ x ]
  u v f g h k : B.Hom x y
  f' g' h' k' : Hom[ f ] x' y'

_∫≡_ : Hom[ u ] x' y' → Hom[ v ] x' y' → Type _
f ∫≡ g = Path (Total-hom E _ _) (total-hom _ f) (total-hom _ g)

opaque
  over[]
    : ∀ {x x' y y'} {f g : ∫.Hom (x , x') (y , y')}
    → {p : f .hom ≡ g .hom}
    → f ≡ g
    → f .preserves ≡[ p ] g .preserves
  over[] {p = p} q = cast[] (ap preserves q)

  begin[]_
    : ∀ {x x' y y'} {f g : ∫.Hom (x , x') (y , y')}
    → {p : f .hom ≡ g .hom}
    → f ≡ g
    → f .preserves ≡[ p ] g .preserves
  begin[]_ = over[]
  {-# INLINE begin[]_ #-}
```

```agda
  ≡[]⟨⟩-syntax
    : ∀ {g' h' : Total-hom E (x , x') (y , y')}
    → {f : B.Hom x y} (f' : Hom[ f ] x' y')
    → g' ≡ h' → total-hom f f' ≡ g'
    → total-hom f f' ≡ h'
  ≡[]⟨⟩-syntax f' q p = p ∙ q

  ≡[]˘⟨⟩-syntax
    : ∀ {g' h' : Total-hom E (x , x') (y , y')}
    → {f : B.Hom x y} (f' : Hom[ f ] x' y')
    → g' ≡ h' → g' ≡ total-hom f f'
    → total-hom f f' ≡ h'
  ≡[]˘⟨⟩-syntax f' q p = sym p ∙ q

  _∎[]
    : {f : B.Hom x y}
    → (f' : Hom[ f ] x' y')
    → total-hom {E = E} f f' ≡ total-hom f f'
  _∎[] f' = refl

syntax ≡[]⟨⟩-syntax f' q p = f' ≡[]⟨ p ⟩ q
syntax ≡[]˘⟨⟩-syntax f' q p = f' ≡[]˘⟨ p ⟩ q

infixr 2 ≡[]⟨⟩-syntax ≡[]˘⟨⟩-syntax
infix 1 begin[]_
infix  3 _∎[]

hom[] : ∀ {a b x y} {f g : B.Hom a b} {p : f ≡ g} → Hom[ f ] x y → Hom[ g ] x y
hom[] {p = p} f' = hom[ p ] f'

_∙[]_ : ∀ {a b x y} {f g h : B.Hom a b} {p : f ≡ g} {q : g ≡ h}
      → {f' : Hom[ f ] x y} {g' : Hom[ g ] x y} {h' : Hom[ h ] x y}
      → f' ≡[ p ] g' → g' ≡[ q ] h' → f' ≡[ p ∙ q ] h'
_∙[]_ {x = x} {y = y} p' q' = _∙P_ {B = λ f → Hom[ f ] x y} p' q'

infixr 30 _∙[]_
```

```agda
opaque
  unfolding hom[_]
  wrap
    : ∀ {f g : B.Hom x y} {f' : Hom[ f ] x' y'}
    → (p : f ≡ g)
    → f' ≡[ p ] hom[ p ] f'
  wrap p = to-pathp refl

  unwrap
    : ∀ {f g : B.Hom x y} {f' : Hom[ f ] x' y'}
    → (p : f ≡ g)
    → hom[ p ] f' ≡[ sym p ] f'
  unwrap p = to-pathp⁻ refl

  reindex
    : ∀ {a b x y} {u v w : B.Hom a b}
    → {f' : Hom[ u ] x y}
    → (p : u ≡ v) (q : u ≡ w)
    → hom[ p ] f' ≡[ sym p ∙ q ] hom[ q ] f'
  reindex p q =
    unwrap p ∙[] wrap q

module _ {x y x' y'} {u v w : B.Hom x y} where

  unwrapped
    : (f' : Hom[ u ] x' y') (g' : Hom[ w ] x' y')
    → (p : u ≡ v)
    → (f' ∫≡ g') ≃ (hom[ p ] f' ∫≡ g')
  unwrapped f' g' p = ∙-pre-equiv (path! (unwrap _))

  wrapped
    : (f' : Hom[ u ] x' y') (g' : Hom[ v ] x' y')
    → (p : v ≡ w)
    → (f' ∫≡ g') ≃ (f' ∫≡ hom[ p ] g')
  wrapped f' g' p = ∙-post-equiv (path! (wrap _))

  module unwrapped {f' : Hom[ u ] x' y'} {g' : Hom[ w ] x' y'} {p : u ≡ v} = Equiv (unwrapped f' g' p)
  module wrapped {f' : Hom[ u ] x' y'} {g' : Hom[ v ] x' y'} {p : v ≡ w} = Equiv (wrapped f' g' p)
```
