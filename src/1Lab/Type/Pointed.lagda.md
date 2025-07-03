<!--
```agda
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.Type.Pointed where
```

## Pointed types {defines="pointed pointed-type pointed-map pointed-homotopy"}

A **pointed type** is a type $A$ equipped with a choice of base point $\point{A}$.

```agda
Type∙ : ∀ ℓ → Type (lsuc ℓ)
Type∙ ℓ = Σ (Type ℓ) (λ A → A)
```

<!--
```agda
private variable
  ℓ ℓ' : Level
  A B C : Type∙ ℓ
```
-->

If we have pointed types $(A, a)$ and $(B, b)$, the most natural notion
of function between them is not simply the type of functions $A \to B$,
but rather those functions $A \to B$ which _preserve the basepoint_,
i.e. the functions $f : A \to B$ equipped with paths $f(a) \equiv b$.
Those are called **pointed maps**.

```agda
_→∙_ : Type∙ ℓ → Type∙ ℓ' → Type _
(A , a) →∙ (B , b) = Σ[ f ∈ (A → B) ] (f a ≡ b)

infixr 0 _→∙_
```

Pointed maps compose in a straightforward way.

```agda
id∙ : A →∙ A
id∙ = id , refl

_∘∙_ : (B →∙ C) → (A →∙ B) → A →∙ C
(f , ptf) ∘∙ (g , ptg) = f ∘ g , ap f ptg ∙ ptf

infixr 40 _∘∙_
```

Paths between pointed maps are characterised as **pointed homotopies**:

```agda
funext∙ : {f g : A →∙ B}
        → (h : ∀ x → f .fst x ≡ g .fst x)
        → Square (h (A .snd)) (f .snd) (g .snd) refl
        → f ≡ g
funext∙ h pth i = funext h i , pth i
```

The product of two pointed types is again a pointed type.

```agda
_×∙_ : Type∙ ℓ → Type∙ ℓ' → Type∙ (ℓ ⊔ ℓ')
(A , a) ×∙ (B , b) = A × B , a , b

infixr 5 _×∙_

fst∙ : A ×∙ B →∙ A
fst∙ = fst , refl

snd∙ : A ×∙ B →∙ B
snd∙ = snd , refl
```

```agda
zero∙ : A →∙ B
zero∙ {B = B} .fst _ = B .snd
zero∙ .snd = refl

Maps∙ : Type∙ ℓ → Type∙ ℓ' → Type∙ (ℓ ⊔ ℓ')
Maps∙ A B .fst = A →∙ B
Maps∙ A B .snd = zero∙

Homogeneous : Type ℓ → Type _
Homogeneous A = ∀ {x y} → Path (Type∙ _) (A , x) (A , y)

homogeneous-funext∙
  : ∀ {ℓ ℓ'} {A : Type∙ ℓ} {B : Type∙ ℓ'}
  → ⦃ _ : Homogeneous (B .fst) ⦄
  → ∀ {f g : A →∙ B} (h : ∀ x → f .fst x ≡ g .fst x)
  → f ≡ g
homogeneous-funext∙ {A = A} {B = B , b₀} {f = f∙@(f , f*)} {g∙@(g , g*)} h =
  subst (λ b → PathP (λ i → A →∙ b i) f∙ g∙) fix bad where
    hom : ∀ x → Path (Type∙ _) (B , b₀) (B , x)
    hom x = auto

    fg* = sym f* ∙∙ h (A .snd) ∙∙ g*

    bad : PathP (λ i → A →∙ B , fg* i) f∙ g∙
    bad i .fst x = h x i
    bad i .snd j = ∙∙-filler (sym f*) (h (A .snd)) g* j i

    fix : Square {A = Type∙ _} refl (λ i → B , fg* i) refl refl
    fix i j = hcomp (∂ i ∨ ∂ j) λ where
      k (k = i0) → B , b₀
      k (i = i0) → hom (fg* j) k
      k (i = i1) → hom b₀ k
      k (j = i0) → hom b₀ k
      k (j = i1) → hom b₀ k
```
