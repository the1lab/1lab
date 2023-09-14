<!--
```agda
open import Cat.Univalent
open import Cat.Prelude

open import Data.Dec

import Cat.Reasoning
```
-->

```agda
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
open _=>_
```
-->

# Discrete categories {defines="discrete-category"}

Given a groupoid $A$, we can build the category $\rm{Disc}(A)$ with
space of objects $A$ and a single morphism $x \to y$ whenever $x \equiv
y$.

```agda
Disc : (A : Type ℓ) → is-groupoid A → Precategory ℓ ℓ
Disc A A-grpd .Ob = A
Disc A A-grpd .Hom = _≡_
Disc A A-grpd .Hom-set = A-grpd
Disc A A-grpd .id = refl
Disc A A-grpd ._∘_ p q = q ∙ p
Disc A A-grpd .idr _ = ∙-id-l _
Disc A A-grpd .idl _ = ∙-id-r _
Disc A A-grpd .assoc _ _ _ = sym (∙-assoc _ _ _)

Disc′ : Set ℓ → Precategory ℓ ℓ
Disc′ A = Disc ∣ A ∣ h where abstract
  h : is-groupoid ∣ A ∣
  h = is-hlevel-suc 2 (A .is-tr)
```

We can lift any function between the underlying types to a functor
between discrete categories. This is because every function
automatically respects equality in a functorial way.

```agda
lift-disc
  : ∀ {A : Set ℓ} {B : Set ℓ'}
  → (∣ A ∣ → ∣ B ∣)
  → Functor (Disc′ A) (Disc′ B)
lift-disc f .F₀ = f
lift-disc f .F₁ = ap f
lift-disc f .F-id = refl
lift-disc f .F-∘ p q = ap-∙ f q p
```

<!--
```agda
Codisc′ : ∀ {ℓ'} → Type ℓ → Precategory ℓ ℓ'
Codisc′ x .Ob = x
Codisc′ x .Hom _ _ = Lift _ ⊤
Codisc′ x .Hom-set _ _ = is-prop→is-set (λ _ _ i → lift tt)
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
$\rm{Disc}(X)$ in some category $\cC$, using the decidable
equality on $X$. We note that the decidable equality is _redundant_
information: The construction `Disc′`{.Agda} above extends into a [[left
adjoint]] to the `Ob`{.Agda} functor.

```agda
Disc-diagram
  : ∀ {X : Set ℓ} (disc : Discrete ∣ X ∣)
  → (∣ X ∣ → Ob C)
  → Functor (Disc′ X) C
Disc-diagram {C = C} {X = X} disc f = F where
  module C = Precategory C

  P : ∣ X ∣ → ∣ X ∣ → Type _
  P x y = C.Hom (f x) (f y)

  map : ∀ {x y : ∣ X ∣} → x ≡ y → Dec (x ≡ y) → P x y
  map {x} {y} p =
    Dec-elim (λ _ → P x y)
      (λ q → subst (P x) q C.id)
      (λ ¬p → absurd (¬p p))
```

The object part of the functor is the provided $f : X \to
\rm{Ob}(\cC)$, and the decidable equality is used to prove that
$f$ respects equality. This is why it's redundant: $f$ automatically
respects equality, because it's a function! However, by using the
decision procedure, we get better computational behaviour: Very often,
$\rm{disc}(x,x)$ will be $\rm{yes}(\refl)$, and
substitution along $\refl$ is easy to deal with.

```agda
  F : Functor _ _
  F .F₀ = f
  F .F₁ {x} {y} p = map p (disc x y)
```

Proving that our our $F_1$ is functorial involves a bunch of tedious
computations with equalities and a whole waterfall of absurd cases:

```agda
  F .F-id {x} with inspect (disc x x)
  ... | yes p , q =
    map refl (disc x x)   ≡⟨ ap (map refl) q ⟩
    map refl (yes p)      ≡⟨ ap (map refl ⊙ yes) (X .is-tr _ _ p refl) ⟩
    map refl (yes refl)   ≡⟨⟩
    subst (P x) refl C.id ≡⟨ transport-refl _ ⟩
    C.id                  ∎
  ... | no ¬x≡x , _ = absurd (¬x≡x refl)

  F .F-∘ {x} {y} {z} f g with inspect (disc x y) | inspect (disc x z) | inspect (disc y z)
  ... | yes x=y , p1 | yes x=z , p2 | yes y=z , p3 =
    map (g ∙ f) (disc x z)                 ≡⟨ ap (map (g ∙ f)) p2 ⟩
    map (g ∙ f) (yes ⌜ x=z ⌝)              ≡⟨ ap! (X .is-tr _ _ _ _) ⟩
    map (g ∙ f) (yes (x=y ∙ y=z))          ≡⟨⟩
    subst (P x) (x=y ∙ y=z) C.id           ≡⟨ subst-∙ (P x) _ _ _ ⟩
    subst (P x) y=z (subst (P _) x=y C.id) ≡⟨ from-pathp (Hom-pathp-reflr C refl) ⟩
    map f (yes y=z) C.∘ map g (yes x=y)    ≡˘⟨ ap₂ C._∘_ (ap (map f) p3) (ap (map g) p1) ⟩
    map f (disc y z) C.∘ map g (disc x y)  ∎

  ... | yes x=y , _ | yes x=z , _ | no  y≠z , _ = absurd (y≠z f)
  ... | yes x=y , _ | no  x≠z , _ | yes y=z , _ = absurd (x≠z (g ∙ f))
  ... | yes x=y , _ | no  x≠z , _ | no  y≠z , _ = absurd (x≠z (g ∙ f))
  ... | no x≠y , _  | yes x=z , _ | yes y=z , _ = absurd (x≠y g)
  ... | no x≠y , _  | yes x=z , _ | no  y≠z , _ = absurd (y≠z f)
  ... | no x≠y , _  | no  x≠z , _ | yes y=z , _ = absurd (x≠z (g ∙ f))
  ... | no x≠y , _  | no  x≠z , _ | no  y≠z , _ = absurd (x≠z (g ∙ f))
```

<!--
```
Disc-adjunct
  : ∀ {iss : is-groupoid X}
  → (X → Ob C)
  → Functor (Disc X iss) C
Disc-adjunct {C = C} F .F₀ = F
Disc-adjunct {C = C} F .F₁ p = subst (C .Hom (F _) ⊙ F) p (C .id)
Disc-adjunct {C = C} F .F-id = transport-refl _
Disc-adjunct {C = C} {iss = iss} F .F-∘ {x} {y} {z} f g = path where
  import Cat.Reasoning C as C
  go = Disc-adjunct {C = C} {iss} F .F₁
  abstract
    path : go (g ∙ f) ≡ C ._∘_ (go f) (go g)
    path =
      J′ (λ y z f → ∀ {x} (g : x ≡ y) → go (g ∙ f) ≡ go f C.∘ go g)
        (λ x g → subst-∙ (C .Hom (F _) ⊙ F) _ _ _
              ·· transport-refl _
              ·· C.introl (transport-refl _))
        f {x} g
```
-->

<!--
```agda
Disc-natural
  : ∀ {X : Set ℓ}
  → {F G : Functor (Disc′ X) C}
  → (∀ x → C .Hom (F .F₀ x) (G .F₀ x))
  → F => G
Disc-natural fam .η = fam
Disc-natural {C = C} {F = F} {G = G} fam .is-natural x y f =
  J (λ y p → fam y C.∘ F .F₁ p ≡ (G .F₁ p C.∘ fam x))
    (C.elimr (F .F-id) ∙ C.introl (G .F-id))
    f
  where module C = Cat.Reasoning C
```
-->
