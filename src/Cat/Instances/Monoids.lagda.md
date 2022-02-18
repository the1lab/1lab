```agda
open import Algebra.Semigroup
open import Algebra.Monoid
open import Algebra.Magma

open import Cat.Functor.Adjoint
open import Cat.Prelude

open import Data.List

module Cat.Instances.Monoids where
```

<!--
```
open Precategory
open isSemigroup
open isMagma
open MonoidHom
open MonoidOn
open Functor
open _=>_
open _⊣_
```
-->

# Category of monoids

The collection of all `Monoid`{.Agda}s relative to some universe level
assembles into a precategory. This is because being a monoid
homomorphism `is a proposition`{.Agda ident=isProp}, and so does not
raise the [h-level] of the Hom-sets.

[h-level]: 1Lab.HLevel.html

```agda
isProp-MonoidHom : ∀ {ℓ} {x y : Monoid ℓ} f → isProp (MonoidHom x y f)
isProp-MonoidHom {y = _ , M} _ x y i = 
  record { pres-id = M .hasIsSet _ _ (x .pres-id) (y .pres-id) i 
         ; pres-⋆ = λ a b → M .hasIsSet _ _ (x .pres-⋆ a b) (y .pres-⋆ a b) i 
         }

Monoids : ∀ ℓ → Precategory (lsuc ℓ) ℓ
Monoids ℓ .Ob      = Monoid ℓ
Monoids ℓ .Hom A B = Σ (MonoidHom A B)
Monoids ℓ .Hom-set _ (_ , M) = 
  isHLevelΣ 2 (isHLevel→ 2 (M .hasIsSet)) λ f → isProp→isSet (isProp-MonoidHom f)
```

It's routine to check that the identity is a monoid homomorphism and
that composites of homomorphisms are again homomorphisms.

```agda
Monoids ℓ .id  = (λ x → x) , (record { pres-id = refl ; pres-⋆ = λ _ _ → refl })
Monoids ℓ ._∘_ (f , fh) (g , gh) = f ⊙ g , fogh where
  fogh : MonoidHom _ _ (f ⊙ g)
  fogh .pres-id    = ap f (gh .pres-id)    ∙ fh .pres-id
  fogh .pres-⋆ x y = ap f (gh .pres-⋆ x y) ∙ fh .pres-⋆ _ _

Monoids ℓ .idr f = Σ≡Prop isProp-MonoidHom refl
Monoids ℓ .idl f = Σ≡Prop isProp-MonoidHom refl
Monoids ℓ .assoc f g h = Σ≡Prop isProp-MonoidHom refl
```

The category of monoids admits a faithful functor to the category of
sets: `Forget`{.Agda}.

```agda
Forget : ∀ {ℓ} → Functor (Monoids ℓ) (Sets ℓ)
Forget .F₀ (A , m) = A , m .hasIsSet
Forget .F₁ = fst
Forget .F-id = refl
Forget .F-∘ _ _ = refl
```

## Free objects

We piece together some properties of `lists`{.Agda ident=List} to show
that, if $A$ is a set, then $\mathrm{List}(A)$ is an object of
`Monoids`{.Agda}; The operation is list concatenation, and the identity
element is the empty list.

```agda
isMonoid-List : ∀ {ℓ} {A : Type ℓ} → isSet A
              → MonoidOn (List A)
isMonoid-List aset .identity = []
isMonoid-List aset ._⋆_ = _++_
isMonoid-List aset .hasIsMonoid .idˡ = refl
isMonoid-List aset .hasIsMonoid .idʳ = ++-idʳ _
isMonoid-List aset .hasIsMonoid .hasIsSemigroup .hasIsMagma .hasIsSet = 
  ListPath.isSet→isSet-List aset
isMonoid-List aset .hasIsMonoid .hasIsSemigroup .associative {x} {y} {z} = 
  sym (++-assoc x y z)
```

We prove that the assignment $X \mapsto \mathrm{List}(X)$ is functorial;
We call this functor `Free`{.Agda}, since it is a [left adjoint] to the
`Forget`{.Agda} functor defined above: it solves the problem of turning
a `set`{.Agda ident=Set} into a monoid in the most efficient way.

[left adjoint]: Cat.Functor.Adjoint.html


```agda
Free : ∀ {ℓ} → Functor (Sets ℓ) (Monoids ℓ)
Free .F₀ (A , s) = List A , isMonoid-List s
```

The action on morphisms is given by `map`{.Agda}, which preserves the
monoid identity definitionally; We must prove that it preserves
concatenation, identity and composition by induction on the list.

```agda
Free .F₁ f = map f , record { pres-id = refl ; pres-⋆  = map-++ f } where
  map-++ : ∀ {x y} (f : x → y) xs ys → map f (xs ++ ys) ≡ map f xs ++ map f ys
  map-++ f [] ys = refl
  map-++ f (x ∷ xs) ys = ap (f x ∷_) (map-++ f xs ys)

Free .F-id = Σ≡Prop isProp-MonoidHom (funext map-id) where
  map-id : ∀ xs → map (λ x → x) xs ≡ xs
  map-id [] = refl
  map-id (x ∷ xs) = ap (x ∷_) (map-id xs)

Free .F-∘ f g = Σ≡Prop isProp-MonoidHom (funext map-∘) where
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
  module M = MonoidOn m

  go : List M → M
  go [] = M.identity
  go (x ∷ xs) = x M.⋆ go xs
```

We prove that `fold` is a monoid homomorphism, and that it is a natural
transformation, hence worthy of being an adjunction counit.

```agda
fold-++ : ∀ {ℓ} {X : Monoid ℓ} (xs ys : List (X .fst))
        → fold X (xs ++ ys) ≡ MonoidOn._⋆_ (X .snd) (fold X xs) (fold X ys)
fold-++ {X = X} = go where
  module M = MonoidOn (X .snd)
  go : ∀ xs ys → _
  go [] ys = sym M.idˡ
  go (x ∷ xs) ys = 
    fold X (x ∷ xs ++ ys)            ≡⟨⟩
    x M.⋆ fold X (xs ++ ys)          ≡⟨ ap (_ M.⋆_) (go xs ys) ⟩
    x M.⋆ (fold X xs M.⋆ fold X ys)  ≡⟨ M.associative ⟩
    fold X (x ∷ xs) M.⋆ fold X ys    ∎

fold-natural : ∀ {ℓ} {X Y : Monoid ℓ} f → MonoidHom X Y f
             → ∀ xs → fold Y (map f xs) ≡ f (fold X xs)
fold-natural f mh [] = sym (mh .pres-id)
fold-natural {X = X} {Y} f mh (x ∷ xs) = 
  f x Y.⋆ fold Y (map f xs) ≡⟨ ap (_ Y.⋆_) (fold-natural f mh xs) ⟩
  f x Y.⋆ f (fold X xs)     ≡⟨ sym (mh .pres-⋆ _ _) ⟩ 
  f (x X.⋆ fold X xs)       ∎
  where
    module X = MonoidOn (X .snd)
    module Y = MonoidOn (Y .snd)
```

Proving that it satisfies the `zig`{.Agda} triangle identity is the
lemma `fold-pure`{.Agda} below.

```agda
fold-pure : ∀ {ℓ} {X : Set ℓ} (xs : List (X .fst))
          → fold (List (X .fst) , isMonoid-List (X .snd)) (map (λ x → x ∷ []) xs) 
          ≡ xs
fold-pure [] = refl
fold-pure (x ∷ xs) = ap (x ∷_) (fold-pure xs)

Free⊣Forget : ∀ {ℓ} → Free {ℓ} ⊣ Forget
Free⊣Forget .unit .η (A , _) = λ x → x ∷ []
Free⊣Forget .unit .is-natural x y f = refl
Free⊣Forget .counit .η M = fold M , record { pres-id = refl ; pres-⋆ = fold-++ }
Free⊣Forget .counit .is-natural x y (f , h) = 
  Σ≡Prop isProp-MonoidHom (funext (fold-natural {X = x} {y} f h))
Free⊣Forget .zig {A = A} =
  Σ≡Prop isProp-MonoidHom (funext (fold-pure {X = A}))
Free⊣Forget .zag {B = B} i x = B .snd .idʳ {x = x} i
```

This concludes the proof that `Monoids`{.Agda} has free objects.