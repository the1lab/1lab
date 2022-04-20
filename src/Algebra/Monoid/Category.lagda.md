```agda
open import Algebra.Semigroup
open import Algebra.Monoid
open import Algebra.Magma

open import Cat.Functor.Adjoint.Monadic
open import Cat.Functor.Equivalence
open import Cat.Instances.Delooping
open import Cat.Functor.Adjoint
open import Cat.Functor.Base
open import Cat.Prelude

open import Data.List

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
```
-->

# Category of monoids

The collection of all `Monoid`{.Agda}s relative to some universe level
assembles into a precategory. This is because being a monoid
homomorphism `is a proposition`{.Agda ident=is-prop}, and so does not
raise the [h-level] of the Hom-sets.

[h-level]: 1Lab.HLevel.html

```agda
instance
  H-Level-Monoid-hom : ∀ {ℓ} {x y : Monoid ℓ} {f} {n} → H-Level (Monoid-hom x y f) (suc n)
  H-Level-Monoid-hom {y = _ , M} = prop-instance λ x y i →
    record { pres-id = M .has-is-set _ _ (x .pres-id) (y .pres-id) i
          ; pres-⋆ = λ a b → M .has-is-set _ _ (x .pres-⋆ a b) (y .pres-⋆ a b) i
          }

Monoids : ∀ ℓ → Precategory (lsuc ℓ) ℓ
Monoids ℓ .Ob      = Monoid ℓ
Monoids ℓ .Hom A B = Σ (Monoid-hom A B)
Monoids ℓ .Hom-set _ (_ , M) = hlevel 2
  where open Monoid-on M
```

It's routine to check that the identity is a monoid homomorphism and
that composites of homomorphisms are again homomorphisms.

```agda
Monoids ℓ .id  = (λ x → x) , record { pres-id = refl ; pres-⋆ = λ _ _ → refl }
Monoids ℓ ._∘_ (f , fh) (g , gh) = f ⊙ g , fogh where
  fogh : Monoid-hom _ _ (f ⊙ g)
  fogh .pres-id    = ap f (gh .pres-id)    ∙ fh .pres-id
  fogh .pres-⋆ x y = ap f (gh .pres-⋆ x y) ∙ fh .pres-⋆ _ _

Monoids ℓ .idr f = Σ-prop-path (λ _ → hlevel 1) refl
Monoids ℓ .idl f = Σ-prop-path (λ _ → hlevel 1) refl
Monoids ℓ .assoc f g h = Σ-prop-path (λ _ → hlevel 1) refl
```

The category of monoids admits a faithful functor to the category of
sets: `Forget`{.Agda}.

```agda
Forget : ∀ {ℓ} → Functor (Monoids ℓ) (Sets ℓ)
Forget .F₀ (A , m) = A , m .has-is-set
Forget .F₁ = fst
Forget .F-id = refl
Forget .F-∘ _ _ = refl
```

## Free objects

We piece together some properties of `lists`{.Agda ident=List} to show
that, if $A$ is a set, then $\id{List}(A)$ is an object of
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

We prove that the assignment $X \mapsto \id{List}(X)$ is functorial;
We call this functor `Free`{.Agda}, since it is a [left adjoint] to the
`Forget`{.Agda} functor defined above: it solves the problem of turning
a `set`{.Agda ident=Set} into a monoid in the most efficient way.

[left adjoint]: Cat.Functor.Adjoint.html


```agda
map-id : ∀ {ℓ} {A : Type ℓ} (xs : List A) → map (λ x → x) xs ≡ xs
map-id [] = refl
map-id (x ∷ xs) = ap (x ∷_) (map-id xs)

map-++ : ∀ {ℓ} {x y : Type ℓ} (f : x → y) xs ys → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f [] ys = refl
map-++ f (x ∷ xs) ys = ap (f x ∷_) (map-++ f xs ys)

Free : ∀ {ℓ} → Functor (Sets ℓ) (Monoids ℓ)
Free .F₀ A = List ∣ A ∣ , List-is-monoid (A .is-tr)
```

The action on morphisms is given by `map`{.Agda}, which preserves the
monoid identity definitionally; We must prove that it preserves
concatenation, identity and composition by induction on the list.

```agda
Free .F₁ f = map f , record { pres-id = refl ; pres-⋆  = map-++ f }
Free .F-id = Σ-prop-path (λ _ → hlevel 1) (funext map-id)
Free .F-∘ f g = Σ-prop-path (λ _ → hlevel 1) (funext map-∘) where
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

fold-natural : ∀ {ℓ} {X Y : Monoid ℓ} f → Monoid-hom X Y f
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

Free⊣Forget : ∀ {ℓ} → Free {ℓ} ⊣ Forget
Free⊣Forget .unit .η _ x = x ∷ []
Free⊣Forget .unit .is-natural x y f = refl
Free⊣Forget .counit .η M = fold M , record { pres-id = refl ; pres-⋆ = fold-++ }
Free⊣Forget .counit .is-natural x y (f , h) =
  Σ-prop-path (λ _ → hlevel 1) (funext (fold-natural {X = x} {y} f h))
Free⊣Forget .zig {A = A} =
  Σ-prop-path (λ _ → hlevel 1) (funext (fold-pure {X = A}))
Free⊣Forget .zag {B = B} i x = B .snd .idr {x = x} i
```

This concludes the proof that `Monoids`{.Agda} has free objects. We now
prove that monoids are equivalently algebras for the `List`{.Agda}
monad, i.e. that the `Free⊣Forget`{.Agda} adjunction is [monadic]. More
specifically, we show that the canonically-defined `comparison`{.Agda
ident=Comparison} functor is [fully faithful][ff] (list algebra homomoprhisms
are equivalent to monoid homomorphisms) and that it is [split
essentially surjective][eso].

[monadic]: Cat.Functor.Adjoint.Monadic.html
[ff]: Cat.Functor.Base.html#ff-functors
[eso]: Cat.Functor.Base.html#essential-fibres

```agda
Monoid-is-monadic : ∀ {ℓ} → is-monadic (Free⊣Forget {ℓ})
Monoid-is-monadic {ℓ} = ff+split-eso→is-equivalence it's-ff it's-eso where
  open import Cat.Diagram.Monad hiding (Free⊣Forget)

  comparison = Comparison (Free⊣Forget {ℓ})
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
    from : Algebra-hom _ _ (comparison.₀ x) (comparison.₀ y) → Monoids ℓ .Hom x y
    from alg .fst = alg .Algebra-hom.morphism
    from alg .snd .pres-id = happly (alg .Algebra-hom.commutes) []
    from alg .snd .pres-⋆ a b =
      f (a x.⋆ b)                  ≡˘⟨ ap f (ap (a x.⋆_) x.idr) ⟩
      f (a x.⋆ (b x.⋆ x.identity)) ≡⟨ (λ i → alg .Algebra-hom.commutes i (a ∷ b ∷ [])) ⟩
      f a y.⋆ (f b y.⋆ y.identity) ≡⟨ ap (f a y.⋆_) y.idr ⟩
      f a y.⋆ f b                  ∎
      where f = alg .Algebra-hom.morphism
```

The proofs that this is a quasi-inverse is immediate, since both "being
an algebra homomorphism" and "being a monoid homomorphism" are
properties of the underlying map.

```agda
    from∘to : is-right-inverse from comparison.₁
    from∘to x = Algebra-hom-path _ refl

    to∘from : is-left-inverse from comparison.₁
    to∘from x = Σ-prop-path (λ _ → hlevel 1) refl
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
    open Algebra-hom
    import Cat.Reasoning (Eilenberg-Moore _ (L∘R (Free⊣Forget {ℓ}))) as R

    monoid : Monoids ℓ .Ob
    monoid .fst = ∣ A ∣
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
          alg .ν (x ∷ alg .ν (y ∷ z ∷ []) ∷ [])                ≡˘⟨ ap (λ x → alg .ν (x ∷ _)) (happly (alg .ν-unit) x) ⟩
          alg .ν (alg .ν (x ∷ []) ∷ alg .ν (y ∷ z ∷ []) ∷ [])  ≡⟨ happly (alg .ν-mult) _ ⟩
          alg .ν (x ∷ y ∷ z ∷ [])                              ≡˘⟨ happly (alg .ν-mult) _ ⟩
          alg .ν (alg .ν (x ∷ y ∷ []) ∷ alg .ν (z ∷ []) ∷ [])  ≡⟨ ap (λ x → alg .ν (_ ∷ x ∷ [])) (happly (alg .ν-unit) z) ⟩
          alg .ν (alg .ν (x ∷ y ∷ []) ∷ z ∷ [])                ∎
        }
      has-is-m .idl {x} =
        alg .ν (alg .ν [] ∷ x ∷ [])                ≡˘⟨ ap (λ x → alg .ν (alg .ν [] ∷ x ∷ [])) (happly (alg .ν-unit) x) ⟩
        alg .ν (alg .ν [] ∷ alg .ν (x ∷ []) ∷ [])  ≡⟨ happly (alg .ν-mult) _ ⟩
        alg .ν (x ∷ [])                            ≡⟨ happly (alg .ν-unit) x ⟩
        x                                          ∎
      has-is-m .idr {x} =
        alg .ν (x ∷ alg .ν [] ∷ [])                ≡˘⟨ ap (λ x → alg .ν (x ∷ _)) (happly (alg .ν-unit) x) ⟩
        alg .ν (alg .ν (x ∷ []) ∷ alg .ν [] ∷ [])  ≡⟨ happly (alg .ν-mult) _ ⟩
        alg .ν (x ∷ [])                            ≡⟨ happly (alg .ν-unit) x ⟩
        x                                          ∎
```

The most important lemma is that `folding`{.Agda ident=fold} a list
using this monoid recovers the original algebra multiplication, which we
can show by induction on the list:

```agda
    recover : ∀ x → fold monoid x ≡ alg .ν x
    recover []       = refl
    recover (x ∷ xs) =
      alg .ν (x ∷ fold monoid xs ∷ [])           ≡⟨ ap₂ (λ e f → alg .ν (e ∷ f ∷ [])) (sym (happly (alg .ν-unit) x)) (recover xs) ⟩
      alg .ν (alg .ν (x ∷ []) ∷ alg .ν xs ∷ [])  ≡⟨ happly (alg .ν-mult) _ ⟩
      alg .ν (x ∷ xs ++ [])                      ≡⟨ ap (alg .ν) (++-idr _) ⟩
      alg .ν (x ∷ xs)                            ∎
```

We must then show that the image of this monoid under
`Comparison`{.Agda} is isomorphic to the original algebra. Fortunately,
this follows from the `recover`{.Agda} lemma above; The isomorphism
itself is given by the identity function in both directions, since the
recovered monoid has the same underlying type as the List-algebra!

```agda
    into : Algebra-hom _ _ (comparison.₀ monoid) (A , alg)
    into .morphism = λ x → x
    into .commutes = funext (λ x → recover x ∙ ap (alg .ν) (sym (map-id x)))

    from : Algebra-hom _ _ (A , alg) (comparison.₀ monoid)
    from .morphism = λ x → x
    from .commutes =
      funext (λ x → sym (recover x) ∙ ap (fold monoid) (sym (map-id x)))

    the-iso : comparison.₀ monoid R.≅ (A , alg)
    the-iso = R.make-iso into from (Algebra-hom-path _ refl) (Algebra-hom-path _ refl)
```
