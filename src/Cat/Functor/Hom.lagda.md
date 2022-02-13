```agda
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Functor.Base
open import Cat.Prelude

module Cat.Functor.Hom {o h} (C : Precategory o h) where
```

# The Hom functor

We prove that the assignment of $\hom$-sets in a `Precategory`{.Agda}
$\ca{C}$ is a `functor`{.Agda}, specifically a bifunctor from $\ca{C}\op
\times_\cat \ca{C}$ to $\sets$. The action of $(f, h)$ on a morphism $g$
is given by $h \circ g \circ f$; Since $f$ is acting by precomposition,
the first coordinate is contravariant ($\ca{C}\op$).

<!--
```agda
open Precategory C
open Functor
open _=>_
private variable
  a b : Ob
```
-->

```agda
Hom[-,-] : Functor ((C ^op) ×Cat C) (Sets h)
Hom[-,-] .F₀ (a , b) = Hom a b , Hom-set a b
Hom[-,-] .F₁ (f , h) g = h ∘ g ∘ f
Hom[-,-] .F-id = funext λ x → ap (_ ∘_) (idr _) ∙ idl _
Hom[-,-] .F-∘ (f , h) (f' , h') = funext λ where
  g → (h ∘ h') ∘ g ∘ f' ∘ f ≡⟨ solve C ⟩
      h ∘ (h' ∘ g ∘ f') ∘ f ∎
```

## The Yoneda embedding

Abstractly and nonsensically, one could say that the Yoneda embedding
`よ`{.Agda} is the [exponential transpose] of `flipping`{.Agda
ident=Flip} the `Hom[-,-]`{.Agda} [bifunctor]. However, this
construction generates _awful_ terms, so in the interest of
computational efficiency we build up the functor explicitly.

[exponential transpose]: Cat.Instances.Functor.html#currying
[bifunctor]: Cat.Functor.Bifunctor.html

```agda
module _ where private
  よ : Functor C (Cat[ C ^op , Sets h ])
  よ = Curry Flip where 
    open import 
      Cat.Functor.Bifunctor {C = C ^op} {D = C} {E = Sets h} Hom[-,-]
```

We can describe the object part of this functor as taking an object $c$
to the functor $\hom(-,c)$ of map into $c$, with the transformation
$\hom(x,y) \to \hom(x,z)$ given by precomposition.

```agda
よ₀ : Ob → Functor (C ^op) (Sets h)
よ₀ c .F₀ x    = Hom x c , Hom-set _ _
よ₀ c .F₁ f    = _∘ f
よ₀ c .F-id    = funext idr
よ₀ c .F-∘ f g = funext λ h → assoc _ _ _
```

The morphism part takes a map $f$ to the transformation given by
postcomposition; This is natural because we must show $f \circ x \circ g
= (f \circ x) \circ g$, which is given by associativity in $C$.

```agda
よ₁ : Hom a b → よ₀ a => よ₀ b
よ₁ f .η _ g            = f ∘ g
よ₁ f .is-natural x y g = funext λ x → assoc f x g
```

The other category laws from $\ca{C}$ ensure that this assigment of
natural transformations is indeed functorial:

```agda
よ : Functor C Cat[ C ^op , Sets h ]
よ .F₀      = よ₀
よ .F₁      = よ₁
よ .F-id    = Nat-path λ _ i g → idl g i
よ .F-∘ f g = Nat-path λ _ i h → assoc f g h (~ i)
```

The morphism mapping `よ₁`{.Agda} has an inverse, given by evaluating the
natural transformation with the identity map; Hence, the Yoneda
embedding functor is fully faithful.

```agda
よ-Ff : isFf よ
よ-Ff = isIso→isEquiv isom where
  open isIso

  isom : isIso よ₁
  isom .inv nt = nt .η _ id
  isom .rinv nt = Nat-path λ c → funext λ g → 
    happly (sym (nt .is-natural _ _ _)) _ ∙ ap (nt .η c) (idl g)
  isom .linv _ = idr _
```
