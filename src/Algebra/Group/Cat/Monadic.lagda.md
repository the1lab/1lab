```agda
open import Algebra.Group.Cat.Base
open import Algebra.Group.Free
open import Algebra.Prelude
open import Algebra.Monoid
open import Algebra.Group

open import Cat.Functor.Adjoint.Monadic
open import Cat.Functor.Adjoint.Monad
open import Cat.Functor.Equivalence
open import Cat.Functor.Base
open import Cat.Diagram.Monad

import Algebra.Group.Cat.Base as Grp
import Cat.Reasoning

module Algebra.Group.Cat.Monadic {ℓ} where
```

<!--
```agda
private
  F : Functor (Sets ℓ) (Groups ℓ)
  F = universal-maps→L (Grp.Forget {ℓ = ℓ}) Free-universal-maps

  F⊣U : F ⊣ _
  F⊣U = universal-maps→L⊣R (Grp.Forget {ℓ = ℓ}) Free-universal-maps

  K = Comparison F⊣U

  T : Monad (Sets ℓ)
  T = Adjunction→Monad F⊣U
  module F = Functor F
  module T = Monad T
  module K = Functor K
  module Sets^T = Cat.Reasoning (Eilenberg-Moore (Sets ℓ) T)
```
-->

# Monadicity of the category of groups

We prove that the category $\ht{Groups}_\kappa$ is monadic over
$\sets_\kappa$, or more specifically that the [free group] adjunction $F
\dashv U$ is [monadic]. Rather than appealing to a monadicity theorem,
we show this directly by calculation. This actually gives us a slightly
sharper result, too: rather than showing that the [comparison functor]
is an equivalence, we show directly that it is an isomorphism of
categories. This doesn't exactly matter since $\sets_\kappa$ and
$\ht{Groups}_\kappa$ are both [univalent categories], but it's interesting
that it's easier to construct an isomorphism than it is to construct an
equivalence.

[free group]: Algebra.Group.Free.html
[monadic]: Cat.Functor.Adjoint.Monadic.html
[univalent categories]: Cat.Univalent.html

Let us abbreviate the [monad induced] by the free group adjunction by
$T$. What we must show is that any $T$-algebra structure on a set $G$
gives rise to a group structure on $G$, and that this process is
reversible: If $\nu$ is our original algebra, applying our process then
applying the comparison functor has to give $\nu$ back.

[monad induced]: Cat.Functor.Adjoint.Monad.html
[comparison functor]: Cat.Functor.Adjoint.Monad.html#Comparison

```agda
Algebra-on→group-on : {G : Set ℓ} → Algebra-on (Sets ℓ) T G → Group-on ∣ G ∣
Algebra-on→group-on {G = G} alg = grp where
  open Algebra-on alg

  mult : ∣ G ∣ → ∣ G ∣ → ∣ G ∣
  mult x y = ν (inc x ◆ inc y)
```

The thing to keep in mind is that a $T$-algebra structure is a way of
"folding" a word built up from generators in the set $G$, so that if we
build a word from two generators $x, y$, folding that should be the same
thing as a binary multiplication $xy$. That's the definition of the
induced multiplication structure! We now must show that this definition
is indeed a group structure, which is an incredibly boring calculation.

<details>
<summary>I'm not exaggerating, it's _super_ boring.</summary>

```agda
  abstract
    assoc : ∀ x y z → mult (mult x y) z ≡ mult x (mult y z)
    assoc x y z =
      ν (inc (ν (inc x ◆ inc y)) ◆ inc z)                ≡⟨ (λ i → ν (inc (ν (inc x ◆ inc y)) ◆ inc (ν-unit (~ i) z))) ⟩
      ν (inc (ν (inc x ◆ inc y)) ◆ inc (ν (inc z)))      ≡⟨ happly ν-mult (inc _ ◆ inc _) ⟩
      ν (T.mult.η G (inc (inc x ◆ inc y) ◆ inc (inc z))) ≡⟨ ap ν (f-assoc _ _ _) ⟩
      ν (T.mult.η G (inc (inc x) ◆ inc (inc y ◆ inc z))) ≡˘⟨ happly ν-mult (inc _ ◆ inc _) ⟩
      ν (inc (ν (inc x)) ◆ inc (ν (inc y ◆ inc z)))      ≡⟨ (λ i → ν (inc (ν-unit i x) ◆ inc (ν (inc y ◆ inc z)))) ⟩
      ν (inc x ◆ inc (ν (inc y ◆ inc z)))                ∎

    invl : ∀ x → mult (ν (inv (inc x))) x ≡ ν nil
    invl x =
      ν (inc (ν (inv (inc x))) ◆ inc x)                ≡⟨ (λ i → ν (inc (ν (inv (inc x))) ◆ inc (ν-unit (~ i) x))) ⟩
      ν (inc (ν (inv (inc x))) ◆ inc (ν (inc x)))      ≡⟨ happly ν-mult (inc _ ◆ inc _) ⟩
      ν (T.mult.η G (inc (inv (inc x)) ◆ inc (inc x))) ≡⟨ ap ν (f-invl _) ⟩
      ν (T.mult.η G (inc nil))                         ≡⟨⟩
      ν nil                                            ∎

    invr : ∀ x → mult x (ν (inv (inc x))) ≡ ν nil
    invr x =
      ν (inc x ◆ inc (ν (inv (inc x))))                ≡⟨ (λ i → ν (inc (ν-unit (~ i) x) ◆ inc (ν (inv (inc x))))) ⟩
      ν (inc (ν (inc x)) ◆ inc (ν (inv (inc x))))      ≡⟨ happly ν-mult (inc _ ◆ inc _) ⟩
      ν (T.mult.η G (inc (inc x) ◆ inc (inv (inc x)))) ≡⟨ ap ν (f-invr _) ⟩
      ν (T.mult.η G (inc nil))                         ≡⟨⟩
      ν nil                                            ∎

    idl′ : ∀ x → mult (ν nil) x ≡ x
    idl′ x =
      ν (inc (ν nil) ◆ inc x)            ≡⟨ (λ i → ν (inc (ν nil) ◆ inc (ν-unit (~ i) x))) ⟩
      ν (inc (ν nil) ◆ inc (ν (inc x)))  ≡⟨ happly ν-mult (inc _ ◆ inc _) ⟩
      ν (T.mult.η G (nil ◆ inc (inc x))) ≡⟨ ap ν (f-idl _) ⟩
      ν (inc x)                          ≡⟨ happly ν-unit x ⟩
      x                                  ∎

  grp : Group-on ∣ G ∣
  grp .Group-on._⋆_ = mult
  grp .Group-on.has-is-group =
    make-group (G .is-tr)
      (ν nil) mult (λ x → ν (inv (inc x)))
      assoc
      invl
      invr
      idl′ .Group-on.has-is-group
```
</details>

We now show that this construction fits into defining an inverse (on the
nose!) to the comparison functor. This is slightly easier than it sounds
like: We must show that the functor is fully faithful, and that our
mapping above is indeed invertible.

Fully faithfulness is almost immediate: a homomorphism of $T$-algebras
$K(G) \to K(H)$ preserves underlying multiplication _because_ the
algebra structure of $K(G)$ (resp. $K(H)$) is defined in terms of that
multiplication. Since we leave the underlying map intact, and being a
homomorphism (either kind) is a property, the comparison functor is
fully faithful.

```agda
Group-is-monadic : is-monadic F⊣U
Group-is-monadic = is-precat-iso→is-equivalence
  record { has-is-ff = ff ; has-is-iso = is-iso→is-equiv isom } where
  open Algebra-hom
  open Algebra-on

  k₁inv : ∀ {G H} → Algebra-hom (Sets ℓ) T (K.₀ G) (K.₀ H) → Groups.Hom G H
  k₁inv hom .fst = hom .morphism
  k₁inv hom .snd .Group-hom.pres-⋆ x y = happly (hom .commutes) (inc x ◆ inc y)

  ff : is-fully-faithful K
  ff = is-iso→is-equiv $ iso k₁inv (λ x → Algebra-hom-path (Sets ℓ) refl)
                                   (λ x → Grp.Forget-is-faithful refl)
```

To show that the object mapping of the comparison functor is invertible,
we appeal to univalence. Since the _types_ are kept the same, it
suffices to show that passing between a multiplication and an algebra
map doesn't lose any information. This is immediate in one direction,
but the other direction is by induction on "words".

```agda
  isom : is-iso K.₀
  isom .is-iso.inv (A , alg) = ∣ A ∣ , Algebra-on→group-on alg
  isom .is-iso.linv x = sip Group-univalent $
    (_ , id-equiv) , record { pres-⋆ = λ x y → refl }
  isom .is-iso.rinv x = Σ-pathp ext (Algebra-on-pathp _ _ go) where
    open n-Type (x .fst) hiding (∣_∣)
    ext : (∣ x .fst ∣ , x .fst .is-tr) ≡ x .fst
    ext i .∣_∣ = ∣ x .fst ∣
    ext i .is-tr = x .fst .is-tr

    alg = x .snd
    grp = Algebra-on→group-on alg
    rec = fold-free-group {G = ∣ x .fst ∣ , grp} (λ x → x)
    module G = Group-on grp

    alg-gh : Group-hom (Free-Group ∣ x .fst ∣) (_ , grp) (x .snd .ν)
    alg-gh .Group-hom.pres-⋆ x y = sym (happly (alg .ν-mult) (inc _ ◆ inc _))

    go : rec .fst ≡ x .snd .ν
    go = funext $ Free-elim-prop _ (λ _ → hlevel 1)
      (λ x → sym (happly (alg .ν-unit) x))
      (λ x y p q → rec .snd .Group-hom.pres-⋆ x y
                ·· ap₂ G._⋆_ p q
                ·· happly (alg .ν-mult) (inc _ ◆ inc _))
      (λ x p → Group-hom.pres-inv (rec .snd) {x = x}
              ·· ap G.inverse p
              ·· sym (Group-hom.pres-inv alg-gh {x = x}))
      refl
```
