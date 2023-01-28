```agda
{-# OPTIONS --lossy-unification -vtc.decl:5 #-}
open import Algebra.Monoid

open import Cat.Displayed.Univalence.Thin
open import Cat.Functor.Adjoint
open import Cat.Prelude

open import Data.Bool

open import Order.Instances.Lower.Cocompletion
open import Order.Instances.Pointwise
open import Order.Semilattice.Order
open import Order.Instances.Lower
open import Order.Semilattice
open import Order.Diagram.Glb
open import Order.Diagram.Lub
open import Order.Frame
open import Order.Base

import Order.Frame.Reasoning as Frm
import Order.Reasoning as Poset

module Order.Frame.Free where
```

# Free cocompletions

A [frame] is, in particular, a [semilattice]: the semilattice of
[meets]. Frame homomorphisms preserve finite meets, so they are also
homomorphisms for the meet semilattice. Since equality of homomorphisms
is defined by equality of the underlying functions, these remarks
assemble into a functor $\thecat{Frames} \to \thecat{SLat}$.

[frame]: Order.Frame.html
[semilattice]: Order.Semilattice.html
[meets]: Order.Diagram.Glb.html

<!--
```agda
open Functor
open make-left-adjoint
open Monoid-hom
```
-->

```agda
Frame↪SLat : ∀ {ℓ} → Functor (Frames ℓ) (Semilattices ℓ)
Frame↪SLat .F₀ A = Frm.meets A

Frame↪SLat .F₁ f .hom = f .hom
Frame↪SLat .F₁ f .preserves .Monoid-hom.pres-id = f .preserves .is-frame-hom.pres-⊤
Frame↪SLat .F₁ f .preserves .Monoid-hom.pres-⋆ = f .preserves .is-frame-hom.pres-∩

Frame↪SLat .F-id = Homomorphism-path λ _ → refl
Frame↪SLat .F-∘ f g = Homomorphism-path λ _ → refl
```

The question this module seeks to answer is: is there a way to freely
turn a semilattice $A$ into a frame $D(A)$, such that the meets in
$D(A)$ are preserved by the inclusion $A \to D(A)$? And if so, how?

Fortunately the answer is positive: otherwise this module would be much
longer (and probably rely on silly cardinality arguments). The free
frame on a semilattice is the free _cocompletion_ of that semilattice,
its [poset of lower sets][low]. The lower sets of _any_ poset are a
frame, because meets and joins are computed pointwise in the [poset of
propositions], $\Omega$.

[poset of propositions]: Order.Instances.Props.html

[low]: Order.Instances.Lower.html

```agda
Lower-sets-frame : ∀ {ℓ} → Semilattice ℓ → Frame ℓ
Lower-sets-frame A = Lower-sets A.po .fst , to-frame-on mk↓A where
  module A = Semilattice A
  module DA = Poset (Lower-sets A.po)

  module fcp = Finitely-complete-poset
  DA-meets : Finitely-complete-poset _ _
  DA-meets .fcp.poset = Lower-sets A.po
  DA-meets .fcp._∩_ x y             = Lower-sets-meets A.po x y .fst
  DA-meets .fcp.has-is-meet {x} {y} = Lower-sets-meets A.po x y .snd
  DA-meets .fcp.top = Lower-sets-complete A.po absurd .fst
  DA-meets .fcp.has-is-top {x} =
    Lower-sets-complete A.po absurd .snd .is-glb.greatest x λ x → absurd x
  DAm = fc-poset→semilattice DA-meets
  module DAm = Semilattice DAm

  mk↓A : make-frame (Lower-set A.po)
  mk↓A .make-frame.has-is-set  = hlevel!
  mk↓A .make-frame.top         = DAm.top
  mk↓A .make-frame._cap_       = DAm._∩_
  mk↓A .make-frame.cup {I} f   = Lower-sets-cocomplete A.po f .fst
  mk↓A .make-frame.identity    = DAm.∩-idl
  mk↓A .make-frame.idempotent  = DAm.∩-idempotent
  mk↓A .make-frame.commutative = DAm.∩-commutative
  mk↓A .make-frame.associative {x} {y} {z} = DAm.∩-assoc {x} {y} {z}

  mk↓A .make-frame.universal {x = x} f p =
    fcp.le→meet DA-meets {y = x} $ Lower-sets-cocomplete A.po f .snd .is-lub.least x
      λ i → fcp.meet→le DA-meets {y = x} (p i)

  mk↓A .make-frame.colimiting i f =
    fcp.le→meet DA-meets {y = Lower-sets-cocomplete A.po f .fst} $
      Lower-sets-cocomplete A.po f .snd .is-lub.fam≤lub i

  mk↓A .make-frame.distrib x f = Σ-prop-path! $ funext λ arg →
    Ω-ua (λ { (x , box) → □-map (λ { (i , arg∈fi) → i , x , arg∈fi }) box })
         (□-rec! λ { (i , x , arg∈fi) → x , inc (i , arg∈fi) })
```

The unit map $A \to D(A)$ sends an element of $A$ to its down-set,
$\darr A$. By a decategorification of the similar arguments about the
[Yoneda embedding], the map $A \mapsto \darr A$ preserves finite meets
(really, it preserves _all_ glbs that exist in $A$); and for a complete
lattice $B$, the [left Kan extension] $\Lan_{\darr}(f) : D(A) \to B$ of
a map $f : A \to B$ along $\darr$ is always cocontinuous, and left exact
whenever $f$ is. Since we're extending semilattice homomorphisms, this
means that $\Lan_{\darr}(f)$ is a frame homomorphism.

[Yoneda embedding]: Cat.Functor.Hom.html#the-yoneda-embedding
[left Kan extension]: Cat.Functor.Kan.html#kan-extensions

Note the similarity between the construction of free frames outlined in
the paragraph above and [Diaconescu's theorem]: “A map of frames $D(A)
\to B$ corresponds to a lex monotone map $A \to B$” is precisely the
decategorification of “A geometric morphism $B \to D(A)$ is a flat
functor $A \to B$”.

[Diaconescu's theorem]: Topoi.Classifying.Diaconescu.html


```agda
make-free-cocompletion : ∀ {ℓ} → make-left-adjoint (Frame↪SLat {ℓ})
make-free-cocompletion {ℓ} = go where
```

Anwyay, that was a _very_ dense explanation of the universal property.
Let's go through it again, this time commenting on everything as we
encounter it. We start by packaging together the extension of a
semilattice homomorphism $A \to B$ to a frame homomorphism $DA \to B$.

```agda
  module Mk (A : Semilattice ℓ) (B : Frame ℓ)
            (f : Precategory.Hom (Semilattices ℓ) A (Frm.meets B))
    where
    module A  = Semilattice A
    module B  = Frm B
```

We've already seen that every semilattice homomorphism is a monotone
map, but we'll need to refer to "f-as-a-monotone-map" while we're
performing this construction. Let's abbreviate it:

```agda
    f-monotone : ⌞ Monotone A.po B.po ⌟
    f-monotone = f .hom , Meet-semi-lattice .F₁ f .preserves
```

The easy part is an appeal to the existing machinery for free
cocompletions: Any monotone map $A \to B$ extneds to a _cocontinuous_
map $DA \to B$, because $B$, being a frame, is cocomplete.

```agda
    mkhom : Frames.Hom ℓ (Lower-sets-frame A) B
    mkhom .hom = Lan↓₀ A.po B.po B.cocomplete f-monotone
    mkhom .preserves .is-frame-hom.pres-⋃ g =
      Lan↓-cocontinuous A.po B.po B.cocomplete f-monotone g
```

The harder part is showing that the cocontinuous extension of a
semilattice homomorphism is still a semilattice homomorphism. It
preserves the top element, since the cocontinuous extension takes
$\top_A$ to $\int_{B} \top_A$, which is readily calculated to
equal $\top_B$:

```agda
    mkhom .preserves .is-frame-hom.pres-⊤ = B.≤-antisym
      (B.⋃-universal _ λ { i → sym B.∩-idr })
      (  sym (f .preserves .pres-id)
      ·· B.⋃-colimiting (A.top , inc λ j → absurd j) (λ i → f .hom (i .fst))
      ·· ap₂ B._∩_ (f .preserves .pres-id) refl)
```

Slightly harder, but still a bit of algebra, is computing that binary
meets are preserved as well. Note that the second step is because $f$
preserves meets, and the third step follows from the infinite
distributive law in $B$.

```agda
    mkhom .preserves .is-frame-hom.pres-∩ (S , s-lower) (T , t-lower) =
      B.⋃ {I = Σ _ λ a → a ∈ S × a ∈ T} (λ i → f # i .fst)  ≡⟨ lemma ⟩
      B.⋃ (λ i → f # (i .fst .fst A.∩ i .snd .fst))         ≡⟨ ap B.⋃ (funext λ i → f .preserves .pres-⋆ _ _) ⟩
      B.⋃ (λ i → f # i .fst .fst B.∩ f # i .snd .fst)       ≡˘⟨ B.⋃-∩-product _ _ ⟩
      B.⋃ (λ i → f # i .fst) B.∩ B.⋃ (λ i → f # i .fst)     ∎
```

<details>
<summary>This calculation relies on a lemma about computing the join of
an intersection of two lower sets as a join of their intersection.
</summary>

```agda
      where
        lemma : B.⋃ {I = Σ _ λ a → a ∈ S × a ∈ T} (λ i → f # i .fst)
              ≡ B.⋃ {I = (Σ _ (_∈ S)) × (Σ _ (_∈ T))}
                    (λ i → f # (i .fst .fst A.∩ i .snd .fst))
        lemma = B.≤-antisym
          (B.⋃-universal _ (λ { (i , i∈S , i∈T) →
            f # i                                          B.=˘⟨ ap (f #_) A.∩-idempotent ⟩
            f # (i A.∩ i)                                  B.≤⟨ B.⋃-colimiting ((i , i∈S) , i , i∈T) _ ⟩
            B.⋃ (λ i → f # (i .fst .fst A.∩ i .snd .fst))  B.≤∎}))
          (B.⋃-universal _ (λ { ((i , i∈S) , j , i∈T) →
            B.⋃-colimiting (i A.∩ j , s-lower _ _ A.∩≤l i∈S , t-lower _ _ A.∩≤r i∈T) _
            }))
```

</details>

It's also free from the definition of cocompletions that the extended
map $\widehat{f}$ satisfies $\widehat{f}(\darr x) = f(x)$.

```agda
    mkcomm : ∀ x → f .hom x ≡ mkhom .hom (↓ A.po x)
    mkcomm x = sym (Lan↓-commutes A.po B.po B.cocomplete f-monotone x)
```

Now we must define the unit map. We've already committed to defining
$\eta_a = \darr a$, so we have to show that $\darr$ preserves finite
meets. This is true because $\darr$ lands in _lower sets_, so it
suffices to show an equivalence between (e.g.) being _under $a$ and
under $b$_ and being _under $a \land b$_. But that's the definition of
$\land$.

```agda
  the-unit
    : (S : Semilattice ℓ)
    → Precategory.Hom (Semilattices ℓ) S (Frame↪SLat .F₀ (Lower-sets-frame S))
  the-unit S = go where
    module S = Semilattice S
    go : Precategory.Hom (Semilattices ℓ) S (Frame↪SLat .F₀ (Lower-sets-frame S))
    go .hom = ↓ (Semilattice.po S)

    go .preserves .pres-id = Σ-prop-path! $ funext λ b →
      Ω-ua (λ _ → inc λ j → absurd j)
           (λ _ → inc (sym S.∩-idr))

    go .preserves .pres-⋆ x y = Σ-prop-path! $ funext λ b → Ω-ua
      (□-rec! {pa = Σ-is-hlevel 1 squash λ _ → squash} λ b≤x∩y →
          inc (S.≤-trans b≤x∩y S.∩≤l)
        , inc (S.≤-trans b≤x∩y S.∩≤r))
      λ { (□b≤x , □b≤y) → inc (
        S.∩-univ b (out! {pa = S.≤-thin} □b≤x)
                   (out! {pa = S.≤-thin} □b≤y))
        }
```

We're already 80% done with the adjunction. The final thing to do is to
put it all together, bringing in the result about uniqueness of
cocontinuous extensions to tie everything up:

```agda
  go : make-left-adjoint (Frame↪SLat {ℓ})
  go .free = Lower-sets-frame
  go .unit = the-unit
  go .universal {A} {B} f = Mk.mkhom A B f
  go .commutes {A} {B} f = Homomorphism-path (Mk.mkcomm A B f)
  go .unique {A} {B} {f = f} {g} wit = Homomorphism-path q where
    open Mk A B f
    p = Lan↓-unique A.po B.po B.cocomplete f-monotone
      (g .hom , λ x y w → Meet-semi-lattice .F₁ (Frame↪SLat .F₁ g) .preserves x y
        (le-meet (Lower-sets A.po) w (Lower-sets-meets A.po x y .snd)))
      (g .preserves .is-frame-hom.pres-⋃)
      λ x → ap (_# x) (sym wit)

    q : ∀ x → Lan↓₀ A.po B.po B.cocomplete f-monotone x ≡ g .hom x
    q x = ap fst (sym p) $ₚ x
```
