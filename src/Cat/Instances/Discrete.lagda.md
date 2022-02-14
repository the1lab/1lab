```agda
open import Cat.Univalent
open import Cat.Prelude

module Cat.Instances.Discrete where
```

<!--
```agda
private variable
  ℓ ℓ' : Level
  X : Type ℓ
  C : Precategory ℓ ℓ'
  
open Precategory
open Functor
```
-->

# Discrete categories

Given a groupoid $A$, we can build the category $\mathrm{Disc}(A)$ with
space of objects $A$ and a single morphism $x \to y$ whenever $x \equiv
y$.

```agda
Disc : (A : Type ℓ) → isGroupoid A → Precategory ℓ ℓ
Disc A A-grpd .Ob = A
Disc A A-grpd .Hom = _≡_
Disc A A-grpd .Hom-set = A-grpd
Disc A A-grpd .id = refl
Disc A A-grpd ._∘_ p q = q ∙ p
Disc A A-grpd .idr _ = ∙-id-l _
Disc A A-grpd .idl _ = ∙-id-r _
Disc A A-grpd .assoc _ _ _ = sym (∙-assoc _ _ _)

Disc′ : Set ℓ → Precategory ℓ ℓ
Disc′ (A , aset) = Disc A h where abstract
  h : isGroupoid A
  h = isHLevel-suc 2 aset
```

We can lift any function between the underlying types to a functor
between discrete categories. This is because every function
automatically respects equality in a functorial way.

```agda
liftDisc 
  : ∀ {A : Set ℓ} {B : Set ℓ'}
  → (A .fst → B .fst)
  → Functor (Disc′ A) (Disc′ B)
liftDisc f .F₀ = f
liftDisc f .F₁ = ap f
liftDisc f .F-id = refl
liftDisc f .F-∘ p q = ap-comp-path f q p
```

<!--
```agda
Codisc′ : ∀ {ℓ'} → Type ℓ → Precategory ℓ ℓ'
Codisc′ x .Ob = x
Codisc′ x .Hom _ _ = Lift _ ⊤
Codisc′ x .Hom-set _ _ = isProp→isSet (λ _ _ i → lift tt)
Codisc′ x .id = lift tt
Codisc′ x ._∘_ _ _ = lift tt
Codisc′ x .idr _ = refl
Codisc′ x .idl _ = refl
Codisc′ x .assoc _ _ _ = refl
```
-->

## Diagrams in Disc(X)

If $X$ is a `discrete type`{.Agda ident=Discrete}, then it is in
particular in `Set`{.Agda}, and we can make diagrams of shape
$\mathrm{Disc}(X)$ in some category $\ca{C}$, using the decidable
equality on $X$. We note that the decidable equality is _redundant_
information: The construction `Disc′`{.Agda} above extends into a [left
adjoint] to the `Ob`{.Agda} functor.

[left adjoint]: Cat.Instances.StrictCat.Cohesive.html#disc-γ

```agda
Disc-diagram
  : ∀ {iss : isSet X} (disc : Discrete X) 
  → (X → Ob C) 
  → Functor (Disc′ (X , iss)) C
Disc-diagram {X = X} {C = C} disc f = F where
  module C = Precategory C
  set : isSet X
  set = Discrete→isSet disc

  P : X → X → Type _
  P x y = C.Hom (f x) (f y)
```

The object part of the functor is the provided $f : X \to
\mathrm{Ob}(\ca{C})$, and the decidable equality is used to prove that
$f$ respects equality. This is why it's redundant: $f$ automatically
respects equality, because it's a function! However, by using the
decision procedure, we get better computational behaviour: Very often,
$\mathrm{disc}(x,x)$ will be $\mathrm{yes}(\mathrm{refl})$, and
substitution along $\mathrm{refl}$ is easy to deal with.

```agda
  F : Functor _ _
  F .F₀ = f
  F .F₁ {x} {y} p with disc x y
  ... | yes q = subst (P x) q C.id
  ... | no ¬p = absurd (¬p p)
```

Proving that our our $F_1$ is functorial involves a bunch of tedious
computations with equalities and a whole waterfall of absurd cases:

```agda
  F .F-id {x} with disc x x
  ... | yes p = 
    subst (P x) p C.id    ≡⟨ ap (λ e → subst (P x) e C.id) (set _ _ p refl) ⟩
    subst (P x) refl C.id ≡⟨ transport-refl _ ⟩
    C.id                  ∎
  ... | no ¬x≡x = absurd (¬x≡x refl)

  F .F-∘ {x} {y} {z} f g with disc x y | disc x z | disc y z
  ... | yes x=y | yes x=z | yes y=z =
    subst (P x) x=z C.id                          ≡⟨ ap (λ e → subst (P x) e C.id) (set _ _ _ _) ⟩
    subst (P x) (x=y ∙ y=z) C.id                  ≡⟨ subst-∙ (P x) _ _ _ ⟩
    subst (P x) y=z (subst (P _) x=y C.id)        ≡⟨ fromPathP (toHomPathP C (ap₂ C._∘_ refl (ap₂ C._∘_ refl (transport-refl _) ∙ C.idr _))) ⟩ 
    subst (P y) y=z C.id C.∘ subst (P x) x=y C.id ∎

  ... | yes x=y | yes x=z | no  y≠z = absurd (y≠z f)
  ... | yes x=y | no  x≠z | yes y=z = absurd (x≠z (g ∙ f))
  ... | yes x=y | no  x≠z | no  y≠z = absurd (x≠z (g ∙ f))
  ... | no x≠y  | yes x=z | yes y=z = absurd (x≠y g)
  ... | no x≠y  | yes x=z | no  y≠z = absurd (y≠z f)
  ... | no x≠y  | no  x≠z | yes y=z = absurd (x≠z (g ∙ f))
  ... | no x≠y  | no  x≠z | no  y≠z = absurd (x≠z (g ∙ f))
```
