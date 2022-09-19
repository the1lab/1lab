```agda
open import Cat.Displayed.Fibre
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Univalent
open import Cat.Prelude

import Cat.Displayed.Reasoning
import Cat.Reasoning

module Cat.Displayed.Univalence
  {o ℓ o′ ℓ′}
  {B : Precategory o ℓ}
  (E : Displayed B o′ ℓ′)
  where
```

<!--
```agda
private
  module B = Cat.Reasoning B
  module E = Cat.Displayed.Reasoning E
  module ∫E = Cat.Reasoning (∫ E)
open Displayed E
open Total-hom
```
-->

# Univalence for displayed categories

We provide equivalent characterisations of univalence for categories
$\ca{E}$ which are displayed over a univalent category $\ca{B}$. The
first thing we define is a type of _displayed isomorphisms_. If we have
an isomorphism $f : x \cong y$ in $\ca{B}$, we may define a type of
isomorphisms over $f$ to consist of maps $g : A \to_f B$ and $g^{-1} : B
\to_{f^{-1}} A$ which are inverses.

```agda
record _≅[_]_ {x y : B.Ob} (A : Ob[ x ]) (f : x B.≅ y) (B : Ob[ y ]) : Type ℓ′ where
  field
    to′   : Hom[ B.to f ] A B
    from′ : Hom[ B.from f ] B A
    invr  : PathP (λ i → Hom[ B.invr f i ] A A) (from′ ∘′ to′) id′
    invl  : PathP (λ i → Hom[ B.invl f i ] B B) (to′ ∘′ from′) id′

open _≅[_]_
```

<!--
```
≅[]-path
  : {x y : B.Ob} {A : Ob[ x ]} {B : Ob[ y ]} {f : x B.≅ y}
    {p q : A ≅[ f ] B}
  → p .to′ ≡ q .to′
  → p .from′ ≡ q .from′
  → p ≡ q
≅[]-path {p = p} {q = q} a b i .to′ = a i
≅[]-path {p = p} {q = q} a b i .from′ = b i
≅[]-path {f = f} {p = p} {q = q} a b i .invr j =
  is-set→squarep (λ i j → Hom[ f .B.invr j ]-set _ _)
    (λ i → b i ∘′ a i) (p .invr) (q .invr) (λ i → id′) i j
≅[]-path {f = f} {p = p} {q = q} a b i .invl j =
  is-set→squarep (λ i j → Hom[ f .B.invl j ]-set _ _)
    (λ i → a i ∘′ b i) (p .invl) (q .invl) (λ i → id′) i j
```
-->

Since isomorphisms over the identity map will be of particular
importance, we also define their own type: they are the _vertical
isomorphisms_.

```agda
_≅↓_ : {x : B.Ob} (A B : Ob[ x ]) → Type ℓ′
_≅↓_ = _≅[ B.id-iso ]_
```

We say a displayed category $\ca{E}$ is **univalent** when, for any $f :
x \cong y$ in $\ca{B}$ and object $A$ over $x$, the space of "objects
over $y$ isomorphic to $A$ over $f$" is a proposition.

```agda
is-category-displayed : Type _
is-category-displayed =
  ∀ {x y} (f : x B.≅ y) (A : Ob[ x ]) → is-prop (Σ[ B ∈ Ob[ y ] ] (A ≅[ f ] B))
```

This condition is sufficient for the total category $\int E$ to be
univalent, if $\ca{B}$ is, too. The proof of this is a bit nasty, so
we'll break it down into parts. Initially, observe that the type of
isomorphisms $(x, A) \cong (y, B)$ in $\int E$ is equivalent to the type

$$
\sum_{p : x \cong y} (A \cong_p B),
$$

consisting of an isomorphism $p$ in the base category and an isomorphism
$f$ over it.

```agda
module _ (base-c : is-category B) (disp-c : is-category-displayed) where
  private
    piece-together
      : ∀ {x y} (p : x B.≅ y) {A : Ob[ x ]} {B : Ob[ y ]} (f : A ≅[ p ] B)
      → (x , A) ∫E.≅ (y , B)
    piece-together p f =
      ∫E.make-iso (total-hom (p .B.to) (f .to′)) (total-hom (p .B.from) (f .from′))
        (total-hom-path E (p .B.invl) (f .invl))
        (total-hom-path E (p .B.invr) (f .invr))
```

We first tackle the case where $f : A \cong B$ is vertical, i.e. $A$ and
$B$ are in the same fibre category. But then, observe that our displayed
univalence condition, when applied to the identity morphism, gives us
exactly an identification $p : A \equiv B$ s.t. over $p$, $f$ looks like
the identity (vertical) isomorphism.

```agda
    contract-vertical-iso
      : ∀ {x} {A : Ob[ x ]} (B : Ob[ x ]) (f : A ≅↓ B)
      → Path (Σ _ ((x , A) ∫E.≅_)) ((x , A) , ∫E.id-iso)
          ((x , B) , piece-together B.id-iso f)
    contract-vertical-iso {x} {A} B f =
      Σ-pathp (λ i → x , pair i .fst)
        (∫E.≅-pathp refl _ (total-hom-pathp E _ _ refl λ i → pair i .snd .to′))
      where
        pair = disp-c B.id-iso A
          (A , record { to′ = id′; from′ = id′; invr = idl′ id′; invl = idl′ id′ })
          (B , f)
```

We can now use _isomorphism induction_ in the base category to reduce
the general case to `contract-vertical-iso`{.Agda} above. To wit: If $p
: x \cong y$ is an arbitrary isomorphism (in $\ca{B}$), it suffices to
consider the case where $y = x$ and $p$ is the identity. Here, $p$ is
the isomorphism of first components coming from the isomorphism in $\int E$.

```agda
  is-category-total : is-category (∫ E)
  is-category-total = record
    { to-path      = λ p → ap fst (wrapper _  _ _ _)
    ; to-path-over = λ p → ap snd (wrapper _ _ _ _)
    }
    where
    wrapper
      : ∀ {x y} (p : x B.≅ y) (A : Ob[ x ]) (B : Ob[ y ]) (f : A ≅[ p ] B)
      → Path (Σ _ ((x , A) ∫E.≅_))
        ((x , A) , ∫E.id-iso)
        ((y , B) , piece-together p f)
    wrapper p A =
      Univalent.J-iso base-c
        (λ y p → (B : Ob[ y ]) (f : A ≅[ p ] B)
               → ((_ , A) , ∫E.id-iso) ≡ (((y , B) , piece-together p f)))
        contract-vertical-iso
        p
```

## Fibrewise univalent categories

Using the same trick as above, we can show that a displayed category is
univalent everywhere if, and only if, it is univalent when restricted to
vertical isomorphisms:

```agda
is-category-fibrewise
  : is-category B
  → (∀ {x} (A : Ob[ x ]) → is-prop (Σ[ B ∈ Ob[ x ] ] (A ≅↓ B)))
  → is-category-displayed
is-category-fibrewise base-c wit f A =
  Univalent.J-iso base-c (λ y p → is-prop (Σ[ B ∈ Ob[ y ] ] (A ≅[ p ] B))) (wit A) f
```

Consequently, it suffices for each fibre _category_ to be univalent,
since a vertical isomorphism is no more than an isomorphism in a
particular fibre category.

```agda
is-category-fibrewise′
  : is-category B
  → (∀ x → is-category (Fibre E x))
  → is-category-displayed
is-category-fibrewise′ b wit = is-category-fibrewise b wit′ where
  wit′ : ∀ {x} (A : Ob[ x ]) → is-prop (Σ[ B ∈ Ob[ x ] ] (A ≅↓ B))
  wit′ {x} A =
    is-contr→is-prop $ retract→is-contr
      (λ (x , i) → x , record
        { to′   = i .F.to
        ; from′ = i .F.from
        ; invr  = to-pathp (i .F.invr)
        ; invl  = to-pathp (i .F.invl)
        })
      (λ (x , i) → x , F.make-iso (i .to′) (i .from′)
        (from-pathp (i .invl)) (from-pathp (i .invr)))
      (λ (x , i) → Σ-pathp refl (≅[]-path refl refl))
      (is-contr-ΣR (wit x))
    where module F = Cat.Reasoning (Fibre E x)
```
