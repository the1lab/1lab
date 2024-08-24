<!--
```agda
open import Algebra.Semigroup
open import Algebra.Monoid
open import Algebra.Magma

open import Cat.Displayed.Univalence.Thin
open import Cat.Functor.Adjoint.Monadic
open import Cat.Functor.Equivalence
open import Cat.Functor.Properties
open import Cat.Functor.Adjoint
open import Cat.Prelude

open import Data.List

import Meta.Idiom
```
-->

```agda
module Algebra.Monoid.Category where
```

<!--
```
open Precategory
open is-semigroup
open is-magma
open Monoid-hom
open Monoid-on
open Functor
open _=>_
open _⊣_

private
  map : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → List A → List B
  map = Meta.Idiom.map
```
-->

# Category of monoids

<!--
```agda
_ = is-prop
```
-->

The collection of all `Monoid`{.Agda}s relative to some universe level
assembles into a precategory. This is because being a monoid
homomorphism `is a proposition`{.Agda ident=is-prop}, and so does not
raise the [h-level] of the Hom-sets.

[h-level]: 1Lab.HLevel.html

```agda
instance
  H-Level-Monoid-hom
    : ∀ {ℓ ℓ'} {s : Type ℓ} {t : Type ℓ'}
    → ∀ {x : Monoid-on s} {y : Monoid-on t} {f} {n}
    → H-Level (Monoid-hom x y f) (suc n)
  H-Level-Monoid-hom {y = M} = prop-instance λ x y i →
    record { pres-id = M .has-is-set _ _ (x .pres-id) (y .pres-id) i
           ; pres-⋆ = λ a b → M .has-is-set _ _ (x .pres-⋆ a b) (y .pres-⋆ a b) i
           }
```

It's routine to check that the identity is a monoid homomorphism and
that composites of homomorphisms are again homomorphisms; This means
that `Monoid-on`{.Agda} assembles into a structure thinly displayed over
the category of sets, so that we may appeal to general results about
[[displayed categories]] to reason about the category of monoids.

```agda
Monoid-structure : ∀ ℓ → Thin-structure ℓ Monoid-on
Monoid-structure ℓ .is-hom f A B = el! $ Monoid-hom A B f

Monoid-structure ℓ .id-is-hom .pres-id = refl
Monoid-structure ℓ .id-is-hom .pres-⋆ x y = refl

Monoid-structure ℓ .∘-is-hom f g p1 p2 .pres-id =
  ap f (p2 .pres-id) ∙ p1 .pres-id
Monoid-structure ℓ .∘-is-hom f g p1 p2 .pres-⋆ x y =
  ap f (p2 .pres-⋆ _ _) ∙ p1 .pres-⋆ _ _

Monoid-structure ℓ .id-hom-unique mh _ i .identity = mh .pres-id i
Monoid-structure ℓ .id-hom-unique mh _ i ._⋆_ x y = mh .pres-⋆ x y i
Monoid-structure ℓ .id-hom-unique {s = s} {t = t} mh _ i .has-is-monoid =
  is-prop→pathp
    (λ i → hlevel {T = is-monoid (mh .pres-id i) (λ x y → mh .pres-⋆ x y i)} 1)
    (s .has-is-monoid)
    (t .has-is-monoid)
    i

Monoids : ∀ ℓ → Precategory (lsuc ℓ) ℓ
Monoids ℓ = Structured-objects (Monoid-structure ℓ)

Monoids-is-category : ∀ {ℓ} → is-category (Monoids ℓ)
Monoids-is-category = Structured-objects-is-category (Monoid-structure _)
```

By standard nonsense, then, the category of monoids admits a [[faithful
functor]] into the category of sets.

```agda
Mon↪Sets : ∀ {ℓ} → Functor (Monoids ℓ) (Sets ℓ)
Mon↪Sets = Forget-structure (Monoid-structure _)
```

## Free monoids {defines=free-monoid}

We piece together some properties of `lists`{.Agda ident=List} to show
that, if $A$ is a set, then $\rm{List}(A)$ is an object of
`Monoids`{.Agda}; The operation is list concatenation, and the identity
element is the empty list.

```agda
List-is-monoid : ∀ {ℓ} {A : Type ℓ} → is-set A
              → Monoid-on (List A)
List-is-monoid aset .identity = []
List-is-monoid aset ._⋆_ = _++_
List-is-monoid aset .has-is-monoid .idl = refl
List-is-monoid aset .has-is-monoid .idr = ++-idr _
List-is-monoid aset .has-is-monoid .has-is-semigroup .has-is-magma .has-is-set =
  ListPath.is-set→List-is-set aset
List-is-monoid aset .has-is-monoid .has-is-semigroup .associative {x} {y} {z} =
  sym (++-assoc x y z)
```

We prove that the assignment $X \mapsto \rm{List}(X)$ is functorial;
We call this functor `Free`{.Agda}, since it is a [[left adjoint]] to the
`Forget`{.Agda} functor defined above: it solves the problem of turning
a `set`{.Agda ident=Set} into a monoid in the most efficient way.

```agda
Free-monoid : ∀ {ℓ} → Functor (Sets ℓ) (Monoids ℓ)
Free-monoid .F₀ A = el! (List ∣ A ∣) , List-is-monoid (A .is-tr)
```

The action on morphisms is given by `map`{.Agda}, which preserves the
monoid identity definitionally; We must prove that it preserves
concatenation, identity and composition by induction on the list.

```agda
Free-monoid .F₁ f = total-hom (map f) record { pres-id = refl ; pres-⋆  = map-++ f }
Free-monoid .F-id = ext map-id
Free-monoid .F-∘ f g = ext map-∘ where
  map-∘ : ∀ xs → map (λ x → f (g x)) xs ≡ map f (map g xs)
  map-∘ [] = refl
  map-∘ (x ∷ xs) = ap (f (g x) ∷_) (map-∘ xs)
```

We refer to the adjunction counit as `fold`{.Agda}, since it has the
effect of multiplying all the elements in the list together. It "folds"
it up into a single value.

```agda
fold : ∀ {ℓ} (X : Monoid ℓ) → List (X .fst) → X .fst
fold (M , m) = go where
  module M = Monoid-on m

  go : List M → M
  go [] = M.identity
  go (x ∷ xs) = x M.⋆ go xs
```

We prove that `fold` is a monoid homomorphism, and that it is a natural
transformation, hence worthy of being an adjunction counit.

```agda
fold-++ : ∀ {ℓ} {X : Monoid ℓ} (xs ys : List (X .fst))
        → fold X (xs ++ ys) ≡ Monoid-on._⋆_ (X .snd) (fold X xs) (fold X ys)
fold-++ {X = X} = go where
  module M = Monoid-on (X .snd)
  go : ∀ xs ys → _
  go [] ys = sym M.idl
  go (x ∷ xs) ys =
    fold X (x ∷ xs ++ ys)            ≡⟨⟩
    x M.⋆ fold X (xs ++ ys)          ≡⟨ ap (_ M.⋆_) (go xs ys) ⟩
    x M.⋆ (fold X xs M.⋆ fold X ys)  ≡⟨ M.associative ⟩
    fold X (x ∷ xs) M.⋆ fold X ys    ∎

fold-natural : ∀ {ℓ} {X Y : Monoid ℓ} f → Monoid-hom (X .snd) (Y .snd) f
             → ∀ xs → fold Y (map f xs) ≡ f (fold X xs)
fold-natural f mh [] = sym (mh .pres-id)
fold-natural {X = X} {Y} f mh (x ∷ xs) =
  f x Y.⋆ fold Y (map f xs) ≡⟨ ap (_ Y.⋆_) (fold-natural f mh xs) ⟩
  f x Y.⋆ f (fold X xs)     ≡⟨ sym (mh .pres-⋆ _ _) ⟩
  f (x X.⋆ fold X xs)       ∎
  where
    module X = Monoid-on (X .snd)
    module Y = Monoid-on (Y .snd)
```

Proving that it satisfies the `zig`{.Agda} triangle identity is the
lemma `fold-pure`{.Agda} below.

```agda
fold-pure : ∀ {ℓ} {X : Set ℓ} (xs : List ∣ X ∣)
          → fold (List ∣ X ∣ , List-is-monoid (X .is-tr)) (map (λ x → x ∷ []) xs)
          ≡ xs
fold-pure [] = refl
fold-pure {X = X} (x ∷ xs) = ap (x ∷_) (fold-pure {X = X} xs)

Free-monoid⊣Forget : ∀ {ℓ} → Free-monoid {ℓ} ⊣ Mon↪Sets
Free-monoid⊣Forget .unit .η _ x = x ∷ []
Free-monoid⊣Forget .unit .is-natural x y f = refl
Free-monoid⊣Forget .counit .η M = total-hom (fold _) record { pres-id = refl ; pres-⋆ = fold-++ }
Free-monoid⊣Forget .counit .is-natural x y th =
  ext $ fold-natural (th .hom) (th .preserves)
Free-monoid⊣Forget .zig {A = A} =
  ext $ fold-pure {X = A}
Free-monoid⊣Forget .zag {B = B} i x = B .snd .idr {x = x} i
```

This concludes the proof that `Monoids`{.Agda} has free objects. We now
prove that monoids are equivalently algebras for the `List`{.Agda}
monad, i.e. that the `Free-monoid⊣Forget`{.Agda} adjunction is [monadic]. More
specifically, we show that the canonically-defined `comparison`{.Agda
ident=Comparison-EM} functor is [[fully faithful]] (list algebra homomoprhisms
are equivalent to monoid homomorphisms) and that it is [[split
essentially surjective]].

[monadic]: Cat.Functor.Adjoint.Monadic.html

```agda
Monoid-is-monadic : ∀ {ℓ} → is-monadic (Free-monoid⊣Forget {ℓ})
Monoid-is-monadic {ℓ} = ff+split-eso→is-equivalence it's-ff it's-eso where
  open import Cat.Diagram.Monad

  comparison = Comparison-EM (Free-monoid⊣Forget {ℓ})
  module comparison = Functor comparison

  it's-ff : is-fully-faithful comparison
  it's-ff {x} {y} = is-iso→is-equiv (iso from from∘to to∘from) where
    module x = Monoid-on (x .snd)
    module y = Monoid-on (y .snd)
```

First, for full-faithfulness, it suffices to prove that the morphism
part of `comparison`{.Agda} is an `isomorphism`{.Agda ident=iso}. Hence,
define an inverse; It suffices to show that the underlying map of the
algebra homomorphism is a monoid homomorphism, which follows from the
properties of monoids:

```agda
    from : Algebra-hom _ (comparison.₀ x) (comparison.₀ y) → Monoids ℓ .Hom x y
    from alg .hom = alg .hom
    from alg .preserves .pres-id = happly (alg .preserves) []
    from alg .preserves .pres-⋆ a b =
      f (a x.⋆ b)                  ≡˘⟨ ap f (ap (a x.⋆_) x.idr) ⟩
      f (a x.⋆ (b x.⋆ x.identity)) ≡⟨ (λ i → alg .preserves i (a ∷ b ∷ [])) ⟩
      f a y.⋆ (f b y.⋆ y.identity) ≡⟨ ap (f a y.⋆_) y.idr ⟩
      f a y.⋆ f b                  ∎
      where f = alg .hom
```

The proofs that this is a quasi-inverse is immediate, since both "being
an algebra homomorphism" and "being a monoid homomorphism" are
properties of the underlying map.

```agda
    from∘to : is-right-inverse from comparison.₁
    from∘to x = trivial!

    to∘from : is-left-inverse from comparison.₁
    to∘from x = trivial!
```

Showing that the functor is essentially surjective is significantly more
complicated. We must show that we can recover a monoid from a List
algebra (a "fold"): We take the unit element to be the fold of the empty
list, and the binary operation $x \star y$ to be the fold of the list
$[x,y]$.

```agda
  it's-eso : is-split-eso comparison
  it's-eso (A , alg) = monoid , the-iso where
    open Algebra-on
    import Cat.Reasoning (Eilenberg-Moore (L∘R (Free-monoid⊣Forget {ℓ}))) as R

    monoid : Monoids ℓ .Ob
    monoid .fst = A
    monoid .snd .identity = alg .ν []
    monoid .snd ._⋆_ a b = alg .ν (a ∷ b ∷ [])
```

It suffices, through _incredibly_ tedious calculations, to show that
these data assembles into a monoid:

```agda
    monoid .snd .has-is-monoid = has-is-m where abstract
      has-is-m : is-monoid (alg .ν []) (monoid .snd ._⋆_)
      has-is-m .has-is-semigroup = record
        { has-is-magma = record { has-is-set = A .is-tr }
        ; associative  = λ {x} {y} {z} →
          alg .ν (⌜ x ⌝ ∷ alg .ν (y ∷ z ∷ []) ∷ [])               ≡˘⟨ ap¡ (happly (alg .ν-unit) x) ⟩
          alg .ν (alg .ν (x ∷ []) ∷ alg .ν (y ∷ z ∷ []) ∷ [])     ≡⟨ happly (alg .ν-mult) _ ⟩
          alg .ν (x ∷ y ∷ z ∷ [])                                 ≡˘⟨ happly (alg .ν-mult) _ ⟩
          alg .ν (alg .ν (x ∷ y ∷ []) ∷ ⌜ alg .ν (z ∷ []) ⌝ ∷ []) ≡⟨ ap! (happly (alg .ν-unit) z) ⟩
          alg .ν (alg .ν (x ∷ y ∷ []) ∷ z ∷ [])                   ∎
        }
      has-is-m .idl {x} =
        alg .ν (alg .ν [] ∷ ⌜ x ⌝ ∷ [])            ≡˘⟨ ap¡ (happly (alg .ν-unit) x) ⟩
        alg .ν (alg .ν [] ∷ alg .ν (x ∷ []) ∷ [])  ≡⟨ happly (alg .ν-mult) _ ⟩
        alg .ν (x ∷ [])                            ≡⟨ happly (alg .ν-unit) x ⟩
        x                                          ∎
      has-is-m .idr {x} =
        alg .ν (⌜ x ⌝ ∷ alg .ν [] ∷ [])            ≡˘⟨ ap¡ (happly (alg .ν-unit) x) ⟩
        alg .ν (alg .ν (x ∷ []) ∷ alg .ν [] ∷ [])  ≡⟨ happly (alg .ν-mult) _ ⟩
        alg .ν (x ∷ [])                            ≡⟨ happly (alg .ν-unit) x ⟩
        x                                          ∎
```

The most important lemma is that `folding`{.Agda ident=fold} a list
using this monoid recovers the original algebra multiplication, which we
can show by induction on the list:

```agda
    recover : ∀ x → fold _ x ≡ alg .ν x
    recover []       = refl
    recover (x ∷ xs) =
      alg .ν (x ∷ fold _ xs ∷ [])               ≡⟨ ap₂ (λ e f → alg .ν (e ∷ f ∷ [])) (sym (happly (alg .ν-unit) x)) (recover xs) ⟩
      alg .ν (alg .ν (x ∷ []) ∷ alg .ν xs ∷ []) ≡⟨ happly (alg .ν-mult) _ ⟩
      alg .ν (x ∷ xs ++ [])                     ≡⟨ ap (alg .ν) (++-idr _) ⟩
      alg .ν (x ∷ xs)                           ∎
```

We must then show that the image of this monoid under
`Comparison`{.Agda} is isomorphic to the original algebra. Fortunately,
this follows from the `recover`{.Agda} lemma above; The isomorphism
itself is given by the identity function in both directions, since the
recovered monoid has the same underlying type as the List-algebra!

```agda
    into : Algebra-hom _ (comparison.₀ monoid) (A , alg)
    into .hom = λ x → x
    into .preserves = funext (λ x → recover x ∙ ap (alg .ν) (sym (map-id x)))

    from : Algebra-hom _ (A , alg) (comparison.₀ monoid)
    from .hom = λ x → x
    from .preserves =
      funext (λ x → sym (recover x) ∙ ap (fold _) (sym (map-id x)))

    the-iso : comparison.₀ monoid R.≅ (A , alg)
    the-iso = R.make-iso into from trivial! trivial!
```
