<!--
```agda
open import Cat.Diagram.Pullback.Properties
open import Cat.Instances.Functor.Limits
open import Cat.Instances.Sets.Complete
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Subterminal
open import Cat.Functor.Adjoint.Hom
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Functor
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Functor.Morphism
open import Cat.Diagram.Product
open import Cat.Functor.Adjoint
open import Cat.Cartesian
open import Cat.Prelude

import Cat.Functor.Reasoning.Presheaf as PSh
import Cat.Reasoning as Cat

open Functor
open _=>_
```
-->

```agda
module Cat.Instances.Presheaf.Limits {o ℓ} (κ : Level) (C : Precategory o ℓ) where
```

<!--
```agda
private
  module C = Cat C
  module PShc = Cat (PSh κ C)

open C
```
-->

# Limits in presheaf categories {defines="limits-in-presheaf-categories"}

We present an explicit construction of finite limits in the category
$\psh(\cC)$ of presheaves on $\cC$. These are computed pointwise, with
the value of e.g. $(A \times B)(c)$ being the set $A(c) \times B(c)$.
Therefore, the constructions below are mostly rote.

First, the [[terminal]] presheaf is constantly the unit set, and all the
laws (functoriality, naturality, universality) are trivial. More
generally, a presheaf is [[terminal]] if it is valued in [[contractible]]
types, and [[subterminal]] if it is valued in [[propositions]].

```agda
⊤PSh : ⌞ PSh κ C ⌟
⊤PSh .F₀ x = el! (Lift κ ⊤)
⊤PSh .F₁ _ _ = lift tt
⊤PSh .F-id = refl
⊤PSh .F-∘ _ _ = refl

contr→is-terminal-PSh
  : ∀ (T : ⌞ PSh κ C ⌟)
  → ⦃ ∀ {c n} → H-Level ⌞ T .F₀ c ⌟ n ⦄
  → is-terminal (PSh κ C) T
contr→is-terminal-PSh T _ .centre .η _ _ = hlevel!
contr→is-terminal-PSh T _ .centre .is-natural _ _ _ = prop!
contr→is-terminal-PSh T _ .paths _ = ext λ _ _ → prop!

prop→is-subterminal-PSh
  : ∀ (T : ⌞ PSh κ C ⌟)
  → ⦃ ∀ {c} → H-Level ⌞ T .F₀ c ⌟ 1 ⦄
  → is-subterminal (PSh κ C) T
prop→is-subterminal-PSh T _ _ _ = ext λ _ _ → prop!

PSh-terminal : Terminal (PSh κ C)
PSh-terminal = record { has⊤ = contr→is-terminal-PSh ⊤PSh }
```

The product presheaf is as described in the introduction, now with all
the laws being componentwise; the projection maps are componentwise the
product projections from $\Sets$, and the pairing $\langle f, g \rangle$
is, componentwise, pairing.

```agda
_×PSh_ : ⌞ PSh κ C ⌟ → ⌞ PSh κ C ⌟ → ⌞ PSh κ C ⌟
(A ×PSh B) .F₀ x = el! (∣ A .F₀ x ∣ × ∣ B .F₀ x ∣)
(A ×PSh B) .F₁ f (x , y) = A .F₁ f x , B .F₁ f y
(A ×PSh B) .F-id i (x , y) = A .F-id i x , B .F-id i y
(A ×PSh B) .F-∘ f g i (x , y) = A .F-∘ f g i x , B .F-∘ f g i y

PSh-products : (A B : ⌞ PSh κ C ⌟) → Product (PSh κ C) A B
PSh-products A B = prod where
  open is-product
  open Product

  prod : Product (PSh _ C) A B
  prod .apex = A ×PSh B
  prod .π₁ = NT (λ x → fst) (λ _ _ _ → refl)
  prod .π₂ = NT (λ x → snd) (λ _ _ _ → refl)
  prod .has-is-product .⟨_,_⟩ f g =
    NT (λ i x → f .η i x , g .η i x) λ x y h i a →
      f .is-natural x y h i a , g .is-natural x y h i a
  prod .has-is-product .π₁∘⟨⟩ = ext λ _ _ → refl
  prod .has-is-product .π₂∘⟨⟩ = ext λ _ _ → refl
  prod .has-is-product .unique p q = ext λ i x → unext p i x ,ₚ unext q i x
```

<!--
```agda
PSh-pullbacks
  : ∀ {X Y Z} (f : X => Z) (g : Y => Z)
  → Pullback (PSh κ C) f g
PSh-pullbacks {X} {Y} {Z} f g = pb where
  module X = Functor X
  module Y = Functor Y
  module Z = Functor Z
  module f = _=>_ f
  module g = _=>_ g
  open Pullback
  open is-pullback

  pb-path
    : ∀ {i} {x y : Σ[ x ∈ X.₀ i ] Σ[ y ∈ Y.₀ i ] f.η i x ≡ g.η i y}
    → x .fst ≡ y .fst
    → x .snd .fst ≡ y .snd .fst
    → x ≡ y
  pb-path p q i .fst = p i
  pb-path p q i .snd .fst = q i
  pb-path {idx} {x} {y} p q i .snd .snd j =
    is-set→squarep (λ _ _ → Z.₀ idx .is-tr)
      (ap (f .η idx) p) (x .snd .snd) (y .snd .snd) (ap (g .η idx) q)
      i j
```
-->

Finally, we also construct pullbacks. As above, the construction is
straightforwardly given by the relevant constructions on $\Sets$,
componentwise.

```agda
  pb : Pullback (PSh κ C) f g
  pb .apex .F₀ i = el! (Σ[ x ∈ X.₀ i ] Σ[ y ∈ Y.₀ i ] f.η i x ≡ g.η i y)
  pb .apex .F₁ {x} {y} h (a , b , p) = X.₁ h a , Y.₁ h b , path where abstract
    path : f.η y (X.₁ h a) ≡ g.η y (Y.₁ h b)
    path = happly (f.is-natural _ _ _) _
        ∙∙ (λ i → Z.₁ h (p i))
        ∙∙ sym (happly (g.is-natural _ _ _) _)
  pb .apex .F-id = funext λ (a , b , _) → pb-path (X.F-id $ₚ a) (Y.F-id $ₚ b)
  pb .apex .F-∘ f g = funext λ (a , b , _) → pb-path (X.F-∘ f g $ₚ a) (Y.F-∘ f g $ₚ b)
  pb .p₁ .η idx (a , b , _) = a
  pb .p₁ .is-natural _ _ _ = refl
  pb .p₂ .η x (a , b , _) = b
  pb .p₂ .is-natural _ _ _ = refl
  pb .has-is-pb .square = ext λ _ _ _ p → p
  pb .has-is-pb .universal path .η idx arg = _ , _ , unext path _ _
  pb .has-is-pb .universal {p₁' = p₁'} {p₂'} path .is-natural x y f = funext λ x →
    pb-path (happly (p₁' .is-natural _ _ _) _) (happly (p₂' .is-natural _ _ _) _)
  pb .has-is-pb .p₁∘universal = ext λ _ _ → refl
  pb .has-is-pb .p₂∘universal = ext λ _ _ → refl
  pb .has-is-pb .unique p q = ext λ _ _ →
    pb-path (unext p _ _) (unext q _ _)
```

<!--
```agda
open Cartesian-category using (products ; terminal)
open Finitely-complete
PSh-finite-limits : Finitely-complete (PSh κ C)
PSh-finite-limits = record
  { Finitely-complete (with-pullbacks (PSh κ C) PSh-terminal PSh-pullbacks) hiding (products)
  ; products = PSh-products
  }

PSh-cartesian : Cartesian-category (PSh κ C)
PSh-cartesian .products = PSh-products
PSh-cartesian .terminal = PSh-terminal
```
-->

## Continuity of evaluation

We can also show abstractly that *every* limit of presheaves is computed
pointwise, in line with the finitary constructions above. First, note
that the operation $F \mapsto F(c)$, for a fixed $c : \cC$, is
functorial on presheaves; this is the **evaluation functor**.

```agda
private
  ev : ∀ {ℓs} c → Functor (PSh ℓs C) (Sets ℓs)
  ev c .F₀ F    = F · c
  ev c .F₁ h i  = h .η _ i
  ev c .F-id    = refl
  ev c .F-∘ f g = refl
```

This functor has a [[left adjoint]], and since [[right adjoints preserve
limits|rapl]], we conclude that if $L$ is any limit of a diagram $F$,
then we can conclude that $L(c)$ is the limit of the $F(-)(c)$s.

```agda
  clo : ∀ {ℓs} c → Functor (Sets ℓs) (PSh (ℓs ⊔ ℓ) C)
  clo c .F₀ A = λ where
    .F₀ d         → el! (⌞ A ⌟ × Hom d c)
    .F₁ g (a , f) → a , f ∘ g
    .F-id         → ext λ a h → refl ,ₚ idr h
    .F-∘ f g      → ext λ a h → refl ,ₚ assoc h g f

  clo c .F₁ f .η i (a , g) = f a , g
  clo c .F₁ f .is-natural x y g = refl
  clo c .F-id    = ext λ _ _ _ → refl
  clo c .F-∘ f g = ext λ _ _ _ → refl

  clo⊣ev : ∀ c → clo {ℓ} c ⊣ ev c
  clo⊣ev c = hom-iso→adjoints (λ f x → f .η _ (x , id)) (is-iso→is-equiv iiso) λ g h x → refl where
    open is-iso

    iiso : ∀ {x y} → is-iso {A = clo c · x => y} (λ f x → f .η c (x , id))
    iiso {y = y} .from f .η x (a , g) = y ⟪ g ⟫ (f a)
    iiso {y = y} .from f .is-natural x z g = ext λ a h → PSh.expand y refl
    iiso {y = y} .rinv x = ext λ a → PSh.F-id y
    iiso {y = y} .linv x = ext (λ i y h → sym (x .is-natural _ _ _ $ₚ _) ∙ ap (x .η i) (refl ,ₚ idl h))
```

As an important consequence is that if a natural transformation $X \to
Y$ is monic, then so are all of its components --- this follows from the
above and from the observation that being a monomorphism is a limit
property.

```agda
abstract
  is-monic→is-embedding-at
    : ∀ {X Y} {m : X => Y}
    → Cat.is-monic (PSh ℓ C) m
    → ∀ {i} → is-embedding (m .η i)
  is-monic→is-embedding-at {Y = Y} {m} mono {i} =
    monic→is-embedding (hlevel 2) λ {C} g h →
      right-adjoint→is-monic _ (clo⊣ev i) mono {C} g h
```
<!--
```agda
PSh-complete : is-complete κ κ (PSh κ C)
PSh-complete = Functor-cat-is-complete $ Sets-is-complete {ι = κ} {κ} {κ}
```
-->
