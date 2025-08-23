<!--
```agda
open import Cat.Functor.Equivalence.Path
open import Cat.Functor.Equivalence
open import Cat.Functor.Constant
open import Cat.Prelude
open import Cat.Finite

open import Data.List.Membership
open import Data.Bool.Order
open import Data.Fin.Finite
open import Data.List.Base
open import Data.Bool

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Shape.Parallel where
```
<!--
```agda
open is-precat-iso
open Functor
```
-->

# The "parallel arrows" category {defines="parallel-arrows walking-parallel-arrows"}

The parallel arrows category is the category with two objects, and two
parallel arrows between them. It is the shape of [[equaliser]] and
[coequaliser] diagrams.

[coequaliser]: Cat.Diagram.Coequaliser.html

```agda
data _·⇉·ʰ_ : Bool → Bool → Type where
  idh     : ∀ {x} → x ·⇉·ʰ x
  inl inr : false ·⇉·ʰ true
```

<!--
```agda
instance
  H-Level-·⇉·ʰ : ∀ {x y n} → H-Level (x ·⇉·ʰ y) (2 + n)
  H-Level-·⇉·ʰ = basic-instance 2 $ retract→is-hlevel 2 to from inv (hlevel 2) where
    to : ∀ {x y} → Bool × (x ≤ y) → x ·⇉·ʰ y
    to {true}  {true}  _ = idh
    to {false} {false} _ = idh
    to {false} {true} (false , _) = inl
    to {false} {true} (true  , _) = inr

    from : ∀ {x y} → x ·⇉·ʰ y → Bool × (x ≤ y)
    from idh = true  , ≤-refl
    from inl = false , _
    from inr = true  , _

    inv : ∀ {x y} (p : x ·⇉·ʰ y) → to (from p) ≡ p
    inv {true}  idh = refl
    inv {false} idh = refl
    inv inl = refl
    inv inr = refl

open is-iso
module _ where
  open Precategory
```
-->

```agda
  ·⇉· : Precategory lzero lzero
  ·⇉· .Ob          = Bool
  ·⇉· .Hom         = _·⇉·ʰ_
  ·⇉· .Hom-set _ _ = hlevel 2
  ·⇉· .id          = idh
  ·⇉· ._∘_ idh h   = h
  ·⇉· ._∘_ inl idh = inl
  ·⇉· ._∘_ inr idh = inr
  ·⇉· .idr idh = refl
  ·⇉· .idr inl = refl
  ·⇉· .idr inr = refl
  ·⇉· .idl f = refl
  ·⇉· .assoc idh g   h   = refl
  ·⇉· .assoc inl idh idh = refl
  ·⇉· .assoc inr idh idh = refl
```

<!--
```agda
instance
  Listing-·⇉·ʰ : ∀ {x y} → Listing (x ·⇉·ʰ y)
  Listing-·⇉·ʰ = record { univ = all ; has-member = find } where
    all : ∀ {x y} → List (x ·⇉·ʰ y)
    all {true}  {true}  = idh ∷ []
    all {true}  {false} = []
    all {false} {true}  = inl ∷ inr ∷ []
    all {false} {false} = idh ∷ []

    find : ∀ {x y} (h : x ·⇉·ʰ y) → is-contr (h ∈ₗ all)
    find {false} idh = contr (here reflᵢ) λ { (here reflᵢ) → refl }
    find {true}  idh = contr (here reflᵢ) λ { (here reflᵢ) → refl }
    find inl = contr (here reflᵢ) λ where
      (here reflᵢ) → refl
      (there (here ()))
      (there (there ()))
    find inr = contr (there (here reflᵢ)) λ where
      (there (here reflᵢ)) → refl

  Finite-·⇉·ʰ : ∀ {x y} → Finite (x ·⇉·ʰ y)
  Finite-·⇉·ʰ = inc auto

·⇉·-finite : is-finite-precategory ·⇉·
·⇉·-finite = finite-cat-hom λ a b → auto
```
-->

The parallel category is isomorphic to its opposite through the
involution `not`{.Agda}.

```agda
·⇇· = ·⇉· ^op

·⇇·≡·⇉· : ·⇇· ≡ ·⇉·
·⇇·≡·⇉· = Precategory-path F F-is-iso where
  F : Functor ·⇇· ·⇉·
  F .F₀ x = not x
  F .F₁ idh = idh
  F .F₁ inl = inl
  F .F₁ inr = inr
  F .F-id = refl
  F .F-∘ idh idh = refl
  F .F-∘ inl idh = refl
  F .F-∘ inr idh = refl
  F .F-∘ idh inl = refl
  F .F-∘ idh inr = refl

  un : ∀ {x y} → not x ·⇉·ʰ not y → y ·⇉·ʰ x
  un {true}  {true}  idh = idh
  un {false} {false} idh = idh
  un {true}  {false} inl = inl
  un {true}  {false} inr = inr

  ri : ∀ {x y} (h : not x ·⇉·ʰ not y) → F .F₁ (un h) ≡ h
  ri {true}  {true}  idh = refl
  ri {true}  {false} inl = refl
  ri {true}  {false} inr = refl
  ri {false} {false} idh = refl

  F-is-iso : is-precat-iso F
  F-is-iso .has-is-iso = not-is-equiv
  F-is-iso .has-is-ff = is-iso→is-equiv λ where
    .from → un
    .rinv → ri
    .linv (idh {true})  → refl
    .linv (idh {false}) → refl
    .linv inl → refl
    .linv inr → refl
```

<!--
```agda

module ·⇉· = Precategory ·⇉·
module ·⇇· = Precategory ·⇇·

module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C
  open Functor
  open _=>_
```
-->

Parallel pairs of morphisms in a category $\cC$ are equivalent to functors from the
walking parallel arrow category to $\cC$.

```agda
  Fork : ∀ {a b} (f g : Hom a b) → Functor ·⇉· C
  Fork f g .F₀ false = _
  Fork f g .F₀ true  = _
  Fork f g .F₁ idh   = id
  Fork f g .F₁ inl   = f
  Fork f g .F₁ inr   = g
  Fork f g .F-id = refl
  Fork f g .F-∘ idh h = introl refl
  Fork f g .F-∘ inl idh = intror refl
  Fork f g .F-∘ inr idh = intror refl
```

A natural transformation between two diagrams $A\
\overset{f}{\underset{g}{\tto}}\ B$ and $C\
\overset{f'}{\underset{g'}{\tto}}\ D$ is given by a pair of commutative
squares

~~~{.quiver}
\begin{tikzcd}
	A & B && A & B \\
	C & D && C & D.
	\arrow["f", from=1-1, to=1-2]
	\arrow["u"', from=1-1, to=2-1]
	\arrow["v", from=1-2, to=2-2]
	\arrow["g", from=1-4, to=1-5]
	\arrow["u"', from=1-4, to=2-4]
	\arrow["v", from=1-5, to=2-5]
	\arrow["{f'}", from=2-1, to=2-2]
	\arrow["{g'}", from=2-4, to=2-5]
\end{tikzcd}
~~~

```agda
  Fork-nt : ∀ {A B C D} {f g : Hom A B} {f' g' : Hom C D} {u : Hom A C} {v : Hom B D}  →
            (α : v ∘ f ≡ f' ∘ u) (β : v ∘ g ≡ g' ∘ u) → (Fork f g) => (Fork f' g')
  Fork-nt {u = u} _ _ .η false = u
  Fork-nt {v = v} _ _ .η true  = v
  Fork-nt _ _ .is-natural _ _ idh = id-comm
  Fork-nt α _ .is-natural _ _ inl = α
  Fork-nt _ β .is-natural _ _ inr = β

  forkl : (F : Functor ·⇉· C) → Hom (F .F₀ false) (F .F₀ true)
  forkl F = F .F₁ inl

  forkr : (F : Functor ·⇉· C) → Hom (F .F₀ false) (F .F₀ true)
  forkr F = F .F₁ inr

  Fork→Cone
    : ∀ {e} (F : Functor ·⇉· C) {equ : Hom e (F .F₀ false)}
    → forkl F ∘ equ ≡ forkr F ∘ equ
    → Const e => F
  Fork→Cone {e = e} F {equ = equ} equal = nt where
    nt : Const e => F
    nt .η true  = forkl F ∘ equ
    nt .η false = equ
    nt .is-natural _ _ idh = idr _ ∙ introl (F .F-id)
    nt .is-natural _ _ inl = idr _
    nt .is-natural _ _ inr = idr _ ∙ equal

  Cofork→Cocone
    : ∀ {e} (F : Functor ·⇉· C) {coequ : Hom (F .F₀ true) e}
    → coequ ∘ forkl F ≡ coequ ∘ forkr F
    → F => Const e
  Cofork→Cocone {e = e} F {coequ} coequal = nt where
    nt : F => Const e
    nt .η true  = coequ
    nt .η false = coequ ∘ forkl F
    nt .is-natural _ _ idh = elimr (F .F-id) ∙ sym (idl _)
    nt .is-natural _ _ inl = sym (idl _)
    nt .is-natural _ _ inr = sym coequal ∙ sym (idl _)
```
