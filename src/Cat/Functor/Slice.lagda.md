<!--
```agda
open import Cat.Diagram.Limit.Finite
open import Cat.Functor.Properties
open import Cat.Diagram.Terminal
open import Cat.Functor.Pullback
open import Cat.Functor.Adjoint
open import Cat.Instances.Slice
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Functor.Slice where
```

# Slicing functors

Let $F : \cC \to \cD$ be a functor and $X : \cC$ an object. By
a standard tool in category theory (namely "whacking an entire
commutative diagram with a functor"), $F$ restricts to a functor $F/X :
\cC/X \to \cD/F(X)$. We call this "slicing" the functor $F$. This
module investigates some of the properties of sliced functors.

<!--
```agda
open Functor
open /-Obj
open /-Hom
open _=>_
open _⊣_
```
-->

```agda
Sliced : ∀ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
       → (F : Functor C D) (X : ⌞ C ⌟)
       → Functor (Slice C X) (Slice D (F .F₀ X))
Sliced F X .F₀ ob = cut (F .F₁ (ob .map))
Sliced F X .F₁ sh = sh' where
  sh' : /-Hom _ _
  sh' .map = F .F₁ (sh .map)
  sh' .commutes = sym (F .F-∘ _ _) ∙ ap (F .F₁) (sh .commutes)
Sliced F X .F-id = ext (F .F-id)
Sliced F X .F-∘ f g = ext (F .F-∘ _ _)
```

# Faithful, fully faithful

Slicing preserves faithfulness and fully-faithfulness. It does _not_
preserve fullness: Even if, by fullness, we get a map $f : x \to y \in
\cC$ from a map $h : F(x) \to F(y) \in \cD/F(X)$, it does not
necessarily restrict to a map in $\cC/X$. We'd have to show
$F(y)h=F(x)$ and $h=F(f)$ implies $yf=x$, which is possible only if $F$
is faithful.

```agda
module _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
         {F : Functor C D} {X : ⌞ C ⌟} where
  private
    module D = Cat.Reasoning D
```

However, if $F$ is [[faithful|faithful functor]], then so are any of its
slices $F/X$, and additionally, if $F$ is [[full|full functor]], then
the sliced functors are also [[fully faithful]].

```agda
  Sliced-faithful : is-faithful F → is-faithful (Sliced F X)
  Sliced-faithful faith p = ext (faith (ap map p))

  Sliced-ff : is-fully-faithful F → is-fully-faithful (Sliced F X)
  Sliced-ff eqv = is-iso→is-equiv isom where
    isom : is-iso _
    isom .is-iso.inv sh = record
      { map = equiv→inverse eqv (sh .map)
      ; commutes = ap fst $ is-contr→is-prop (eqv .is-eqv _)
        (_ , F .F-∘ _ _ ∙ ap₂ D._∘_ refl (equiv→counit eqv _) ∙ sh .commutes) (_ , refl)
      }
    isom .is-iso.rinv x = ext (equiv→counit eqv _)
    isom .is-iso.linv x = ext (equiv→unit eqv _)
```

# Left exactness

If $F$ is [[left exact|left exact functor]] (meaning it preserves
[[pullbacks]] and the [[terminal object]]), then $F/X$ is lex as well.
We note that it (by definition) preserves [[products]], since products
in $\cC/X$ are equivalently pullbacks in $\cC/X$. Pullbacks are also
immediately shown to be preserved, since a square in $\cC/X$ is a
pullback iff it is a pullback in $\cC$.

```agda
Sliced-lex
  : ∀ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
  → {F : Functor C D} {X : ⌞ C ⌟}
  → is-lex F
  → is-lex (Sliced F X)
Sliced-lex {C = C} {D = D} {F = F} {X = X} flex = lex where
  module D = Cat.Reasoning D
  module Dx = Cat.Reasoning (Slice D (F .F₀ X))
  module C = Cat.Reasoning C
  open is-lex
  lex : is-lex (Sliced F X)
  lex .pres-pullback = pullback-above→pullback-below
                     ⊙ flex .pres-pullback
                     ⊙ pullback-below→pullback-above
```

That the slice of lex functor preserves the terminal object is slightly
more involved, but not by a lot. The gist of the argument is that _we
know what the terminal object is_: It's the identity map! So we can
cheat: Since we know that $T$ is terminal, we know that $T \cong
\id$ --- but $F$ preserves this isomorphism, so we have $F(T) \cong
F(\id)$. But $F(\id)$ is $\id$ again, now in $\cD$, so
$F(T)$, being isomorphic to the terminal object, is itself terminal!

```agda
  lex .pres-⊤ {T = T} term =
    is-terminal-iso (Slice D (F .F₀ X))
      (subst (Dx._≅ cut (F .F₁ (T .map))) (ap cut (F .F-id))
        (F-map-iso (Sliced F X)
          (⊤-unique (Slice C X) Slice-terminal-object (record { has⊤ = term }))))
      Slice-terminal-object'
```

# Sliced adjoints

A _very_ important property of sliced functors is that, if $L \dashv R$,
then $R/X$ is also a right adjoint. The [[left adjoint]] isn't quite $L/X$,
because the types there don't match, nor is it $L/R(x)$ --- but it's
quite close. We can adjust that functor by postcomposition with the
counit $\eps : LR(x) \to x$A to get a functor left adjoint to $R/X$.

```agda
Sliced-adjoints
  : ∀ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
  → {L : Functor C D} {R : Functor D C} (adj : L ⊣ R) {X : ⌞ D ⌟}
  → (Σf (adj .counit .η _) F∘ Sliced L (R .F₀ X)) ⊣ Sliced R X
Sliced-adjoints {C = C} {D} {L} {R} adj {X} = adj' where
  module adj = _⊣_ adj
  module L = Functor L
  module R = Functor R
  module C = Cat.Reasoning C
  module D = Cat.Reasoning D

  adj' : (Σf (adj .counit .η _) F∘ Sliced L (R .F₀ X)) ⊣ Sliced R X
  adj' .unit .η x .map         = adj.η _
  adj' .unit .is-natural x y f = ext (adj.unit.is-natural _ _ _)

  adj' .counit .η x .map         = adj.ε _
  adj' .counit .η x .commutes    = sym (adj.counit.is-natural _ _ _)
  adj' .counit .is-natural x y f = ext (adj.counit.is-natural _ _ _)

  adj' .zig = ext adj.zig
  adj' .zag = ext adj.zag
```

80% of the adjunction transfers as-is (I didn't quite count, but the
percentage must be way up there --- just look at the definition above!).
The hard part is proving that the adjunction unit restricts to a map in
slice categories, which we can compute:

```agda
  adj' .unit .η x .commutes =
    R.₁ (adj.ε _ D.∘ L.₁ (x .map)) C.∘ adj.η _         ≡⟨ C.pushl (R.F-∘ _ _) ⟩
    R.₁ (adj.ε _) C.∘ R.₁ (L.₁ (x .map)) C.∘ adj.η _   ≡˘⟨ ap (R.₁ _ C.∘_) (adj.unit.is-natural _ _ _) ⟩
    R.₁ (adj.ε _) C.∘ adj.η _ C.∘ x .map               ≡⟨ C.cancell adj.zag ⟩
    x .map                                             ∎
```
