<!--
```agda
open import Cat.CartesianClosed.Locally
open import Cat.Diagram.Limit.Finite
open import Cat.Functor.Pullback
open import Cat.Functor.Adjoint
open import Cat.Instances.Slice
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.DependentProduct
  {o ℓ} (C : Precategory o ℓ) (fc : Finitely-complete C) where
```

# Dependent products {defines="dependent-product"}

Analogously to [[Exponential Objects]], we can define **dependent
products** in a category. We mimic the design of the module
[`Cat.Diagram.Exponential`](Cat.Diagram.Exponential.html).

<!--
```agda
open Cat.Reasoning C
open Finitely-complete fc
```
-->

```agda
module _ {A B : Ob} {f : Hom A B} where
  private
    module C/A = Cat.Reasoning (Slice C A)
    module C/B = Cat.Reasoning (Slice C B)
    module pb = Functor (Base-change pullbacks f)
  record is-dependent-product {X : C/A.Ob}
    (Π : C/B.Ob) (ev : C/A.Hom (pb.₀ Π) X) : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      ƛ        : ∀ {Γ} (m : C/A.Hom (pb.₀ Γ) X) → C/B.Hom Γ Π
      commutes : ∀ {Γ} (m : C/A.Hom (pb.₀ Γ) X) → ev C/A.∘ pb.₁ (ƛ m) ≡ m
      unique
        : ∀ {Γ} {m : C/A.Hom (pb.₀ Γ) X} m'
        → ev C/A.∘ pb.₁ m' ≡ m
        → m' ≡ ƛ m
```

Just as exponentiation induces an equivalence between
$\hom_\cC(\Gamma, B^A)$ and $\hom_\cC(A × \Gamma, B)$,
dependent products induce an equivalence between
$\hom_{\cC/B}(\Gamma, \prod_f X)$ and
$\hom_{\cC/A}(A \times_B \Gamma, X)$.

```agda
    unlambda : ∀ {C} (m : C/B.Hom C Π) → C/A.Hom (pb.₀ C) X
    unlambda m = ev C/A.∘ pb.₁ m

    lambda-is-equiv : ∀ {C} → is-equiv (ƛ {C})
    lambda-is-equiv .is-eqv x .centre = unlambda x , sym (unique x refl)
    lambda-is-equiv .is-eqv x .paths (y , p) =
      Σ-prop-path! (ap unlambda (sym p) ∙ commutes y)
```

<!--
```agda
    unique₂
      : ∀ {C} {m : C/A.Hom (pb.₀ C) _} m₁ m₂
      → ev C/A.∘ pb.₁ m₁ ≡ m
      → ev C/A.∘ pb.₁ m₂ ≡ m
      → m₁ ≡ m₂
    unique₂ _ _ p q = unique _ p ∙ sym (unique _ q)

    lambda-ev : ƛ ev ≡ C/B.id
    lambda-ev = sym (unique C/B.id (C/A.elimr pb.F-id))

  module _ where
    is-dependent-product-is-prop
      : ∀ {X Π ev} → is-prop (is-dependent-product {X} Π ev)
    is-dependent-product-is-prop {X} {Π} {ev} x y = q where
      open is-dependent-product

      p : Path (∀ {C} m → C/B.Hom C Π) (x .ƛ) (y .ƛ)
      p i m = y .unique (x .ƛ m) (x .commutes m) i

      q : x ≡ y
      q i .is-dependent-product.ƛ = p i
      q i .is-dependent-product.commutes m =
        is-prop→pathp (λ i → C/A.Hom-set _ _ (ev C/A.∘ pb.₁ (p i m)) m)
          (x .commutes m) (y .commutes m) i
      q i .is-dependent-product.unique {m = m} m' q =
        is-prop→pathp (λ i → C/B.Hom-set _ _ m' (p i m))
          (x .unique m' q) (y .unique m' q) i
```
-->

We bundle this data together.

```agda
record DependentProduct {A B : Ob} (f : Hom A B) (X : /-Obj {C = C} A) :
  Type (o ⊔ ℓ) where
  field
    Π : /-Obj {C = C} B
    ev : /-Hom (Base-change pullbacks f .Functor.F₀ Π) X
    has-is-Π : is-dependent-product Π ev
  open is-dependent-product has-is-Π public
```

## Exponentiable Maps {defines=exponentiable-map}

A map $f : A \xto{\cC} B$ is **exponentiable** if $\prod_f X$ exists for
every $X : \cC/A$. Such a map induces a dependent product *functor*,
$\prod_f : \cC/A \to \cC/B$, right adjoint to the [[pullback functor]]
$A \times_B - : \cC/B \to \cC/A$.

<!--
```agda
module _ {A B : Ob} (f : Hom A B) (dp : ∀ X → DependentProduct f X) where
  private
    module C/A = Cat.Reasoning (Slice C A)
    module C/B = Cat.Reasoning (Slice C B)
    module pb = Functor (Base-change pullbacks f)
    module _ {X} where open DependentProduct (dp X) public
```
-->

```agda
  Πf : Functor (Slice C A) (Slice C B)
  Πf .Functor.F₀ X = Π {X}
  Πf .Functor.F₁ h = ƛ (h C/A.∘ ev)
  Πf .Functor.F-id = ap ƛ (C/A.idl ev) ∙ lambda-ev
  Πf .Functor.F-∘ f g = sym $ unique _ $
    ev C/A.∘ pb.₁ (ƛ (f C/A.∘ ev) C/B.∘ ƛ (g C/A.∘ ev))         ≡⟨ C/A.refl⟩∘⟨ pb.F-∘ _ _ ⟩
    ev C/A.∘ pb.₁ (ƛ (f C/A.∘ ev)) C/A.∘ pb.₁ (ƛ (g C/A.∘ ev))  ≡⟨ C/A.extendl (commutes _) ⟩
    f C/A.∘ ev C/A.∘ pb.₁ (ƛ (g C/A.∘ ev))                      ≡⟨ C/A.refl⟩∘⟨ commutes _ ⟩
    f C/A.∘ g C/A.∘ ev                                          ≡⟨ C/A.assoc _ _ _ ⟩
    (f C/A.∘ g) C/A.∘ ev
    ∎

  f*⊣Πf : Base-change pullbacks f ⊣ Πf
  f*⊣Πf ._⊣_.unit ._=>_.η _ = ƛ C/A.id
  f*⊣Πf ._⊣_.unit ._=>_.is-natural x y f = unique₂ _ _
    ( ev C/A.∘ pb.₁ (ƛ C/A.id C/B.∘ f)                          ≡⟨ C/A.refl⟩∘⟨ pb.F-∘ _ _ ⟩
      ev C/A.∘ pb.₁ (ƛ C/A.id) C/A.∘ pb.₁ f                     ≡⟨ C/A.cancell (commutes _) ⟩
      pb.₁ f                                                    ∎)
    ( ev C/A.∘ pb.₁ (ƛ (pb.₁ f C/A.∘ ev) C/B.∘ ƛ C/A.id)        ≡⟨ C/A.refl⟩∘⟨ pb.F-∘ _ _ ⟩
      ev C/A.∘ pb.₁ (ƛ (pb.₁ f C/A.∘ ev)) C/A.∘ pb.₁ (ƛ C/A.id) ≡⟨ C/A.extendl (commutes _) ⟩
      pb.₁ f C/A.∘ ev C/A.∘ pb.₁ (ƛ C/A.id)                     ≡⟨ C/A.elimr (commutes _) ⟩
      pb.₁ f                                                    ∎)
  f*⊣Πf ._⊣_.counit ._=>_.η _ = ev
  f*⊣Πf ._⊣_.counit ._=>_.is-natural x y f = commutes _
  f*⊣Πf ._⊣_.zig = commutes _
  f*⊣Πf ._⊣_.zag = unique₂ _ _
    ( ev C/A.∘ pb.₁ (ƛ (ev C/A.∘ ev) C/B.∘ ƛ C/A.id)            ≡⟨ C/A.refl⟩∘⟨ pb.F-∘ _ _ ⟩
      ev C/A.∘ pb.₁ (ƛ (ev C/A.∘ ev)) C/A.∘ pb.₁ (ƛ C/A.id)     ≡⟨ C/A.extendl (commutes _) ⟩
      ev C/A.∘ ev C/A.∘ pb.₁ (ƛ C/A.id)                         ≡⟨ C/A.elimr (commutes _) ⟩
      ev                                                        ∎)
    (C/A.elimr pb.F-id)
```

In particular, if all morphisms are exponentiable, then the category is
[[locally cartesian closed]].

```agda
lccc : (∀ {A B} (f : Hom A B) X → DependentProduct f X) → Locally-cartesian-closed C
lccc dp = dependent-product→lcc C fc (λ f → Πf f (dp f)) (λ f → f*⊣Πf f (dp f))
```
