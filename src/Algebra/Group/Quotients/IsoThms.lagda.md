```agda
open import 1Lab.Prelude

open import Algebra.Group.Quotients
open import Algebra.Group.Subgroup
open import Algebra.Group

open import Data.Set.Coequaliser
open import Data.Power

module Algebra.Group.Quotients.IsoThms where
```

# First Isomorphism Theorem

The first isomorphism theorem states that, for a group homomorphism $f :
A \to B$, we have an isomorphism between $\mathrm{im}(f)$ and
$A/\mathrm{ker}(f)$.

```agda
module _ {ℓ} {A B : Group ℓ} (φ : A .fst → B .fst) (h : isGroupHom A B φ) where
  private
    imφ = im φ h
    A/kerφ = A /ᴳ ker φ h

    module A = GroupOn (A .snd)
    module B = GroupOn (B .snd)
      
    open isGroupHom h
```

We first define a map from the image group $\mathrm{im}(f)$ to the
quotient. Recall that to construct an element of the quotient, it
suffices (by `inc`{.Agda}) to give an element of the underlying group,
in this case $A$; Recall also that an element of $\mathrm{im}(f)$ is
given by an $b : B$ such that [_there exists_] an $a : A$ such that
$f(a) = b$ --- and hence the elements of the image look like $(y,w)$
where $w$ is a witness of that existential statement. 

Since the $a : A$ is propositionally truncated, we can not directly
project it from the proof, since $A/\mathrm{ker}(f)$ is not a
proposition in general.  

[_there exists_]: 1Lab.HIT.Truncation.html

```agda
    func : imφ .fst → A/kerφ .fst
    func (f*x , x) = 
      ∥-∥-recSet (λ x → inc (x .fst)) f-const squash x
      where abstract
```

However, we _can_ project it, as long as the map we're defining is
constant. To prove that it's constant, we have to show that for a fixed
$b$, for _any_ $a_1, a_2 : A$ with $f(a_i) = b$, the inclusions
$\mathrm{inc}(a_i) : A/\mathrm{ker}(f)$ coincide. Since the latter type
is a quotient, it suffices to show that $f(a_1 - a_2)$ is in the
kernel of $f$; But this follows by $f(a_1 - a_2) = f(a_1) - f(a_2)
= y - y = 0$.

```agda
        f-const : ∀ (x y : Σ[ x ∈ A .fst ] (φ x ≡ f*x)) 
                → Path (A/kerφ .fst) (inc (x .fst)) (inc (y .fst))
        f-const (x , p) (z , q) = quot _ _ (
            pres-⋆ _ _ 
          ·· ap₂ B._⋆_ refl (pres-inv _) 
          ·· (ap₂ B._⋆_ p (ap B.inverse q) ∙ B.inverseʳ))

    im* = imφ .snd .GroupOn._⋆_
    ak* = A/kerφ .snd .GroupOn._⋆_
```

The map `func`{.Agda} we have defined is evidently a group homomorphism,
but to convince Agda of this fact, we must again move the propositional
truncations out of the way.

```agda
    abstract
      func-hom : isGroupHom imφ A/kerφ func
      func-hom .isGroupHom.pres-⋆ (f*x , p) (f*y , q) = 
        ∥-∥-elim₂
          {P = λ p q → func (im* (f*x , p) (f*y , q)) 
                     ≡ ak* (func (f*x , p)) (func (f*y , q))} 
          (λ _ _ → squash _ _) 
          (λ _ _ → refl) p q
```

We now construct an inverse map to `func`{.Agda}. Fortunately, we will
not have to show that this is a group homomorphism, we just have to show
it is well defined. Given an element $x : A$, we want to send this to
$f(x)$ in the image (with the evident preimage $x$ and identification
$f(x) = f(x)$).

To show this map descends to the quotient, we must show that if $f(x -
y) = 0$, then $f(x) = f(y)$. This also follows quite handily from the
properties of group homomorphisms.

```agda
    inv : A/kerφ .fst → imφ .fst
    inv = Coeq-rec (im φ h .snd .GroupOn.hasIsSet) 
      (λ x → φ x , inc (x , refl))
      (λ (x , y , p) → Σ≡Prop (λ _ → squash) 
        (B.zero-diff→≡
          (subst (_≡ B.unit) (pres-⋆ _ _ ∙ ap₂ B._⋆_ refl (pres-inv _)) p)))

    open isIso hiding (inv)
```

We now turn to showing that `func`{.Agda} and `inv`{.Agda} are indeed
inverses. 

```agda
    isom : isIso func
    isom .isIso.inv = inv
```

For the direction `func(inv(x)) = x`, it suffices to cover the case
where $x = \mathrm{inc}(y)$, where $y : A$; But then (the relevant part
of) `inv(x)` computes to `f(y) , y , refl`, and `func (f(y) , y , refl)
= inc y`, so this direction follows essentially by `refl`{.Agda}.

```agda
    isom .rinv x =
      Coeq-elimProp {C = λ x → func (inv x) ≡ x} 
        (λ _ → squash _ _) (λ _ → refl) x
```

For the other direction, suppose we have some $(x, p)$ in
$\mathrm{im}(f)$. We wish to show that $\mathrm{inv}(\mathrm{func}(x,
p)) = (x, p)$. Since we're proving a proposition, we can assume that $p$
is a literal pair $(y, h_x)$, with $h_x : f(y) = x$. Since $p$ is a
proposition, it suffices to show that the first components are equal,
but the first component of $\mathrm{inv}(\mathrm{func}(x, p))$ is $f(y)$
--- and we already have that $f(y) = x$, by $h_x$, so we are done!

```agda
    isom .linv (x , p) =
      ∥-∥-elim {P = λ p → inv (func (x , p)) ≡ (x , p) } 
        (λ _ → imφ .snd .GroupOn.hasIsSet _ _) 
        (λ { (y , hx) → Σ≡Prop (λ _ → squash) hx }) 
        p
```

We thus have an equivalence $\mathrm{im}(f) \simeq A/\mathrm{ker}(f)$,
with an underlying map that is a group homomorphism; By the `structure
identity principle`{.Agda}, this gives an identification $\mathrm{im}(f)
\equiv A/\mathrm{ker}(f)$.

```agda
  1st-Iso-Theorem : imφ ≡ A/kerφ
  1st-Iso-Theorem = sip Group-univalent ((func , isIso→isEquiv isom) , func-hom)
```
