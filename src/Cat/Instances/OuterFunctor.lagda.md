<!--
```agda
open import Cat.Diagram.Product.Solver
open import Cat.Internal.Functor.Outer
open import Cat.Functor.Equivalence
open import Cat.Functor.Properties
open import Cat.Instances.Slice
open import Cat.Functor.Adjoint
open import Cat.Diagram.Product
open import Cat.Prelude

open import Cat.Internal.Instances.Discrete

import Cat.Internal.Reasoning
import Cat.Internal.Base
import Cat.Reasoning
```
-->

```agda
module Cat.Instances.OuterFunctor
  {o ℓ} {C : Precategory o ℓ}
  where
```

<!--
```agda
open Cat.Reasoning C
open Cat.Internal.Base C
open Functor
open Outer-functor
open _=>o_

```
-->

# The category of outer functors

Like most constructions in category theory, [outer functors], and outer
natural transformations between them, can also be regarded as a
category. By a rote calculation, we can define the identity and
composite outer natural transformations.

[outer functors]: Cat.Internal.Functor.Outer.html

<!--
```agda
module _ {ℂ : Internal-cat} where
  open Internal-cat ℂ
```
-->

```agda
  idnto : ∀ {F : Outer-functor ℂ} → F =>o F
  idnto {F = F} .ηo px = px
  idnto {F = F} .ηo-fib _ = refl
  idnto {F = F} .is-naturalo px y f =
    ap (F .P₁ px) (Internal-hom-path refl)
  idnto {F = F} .ηo-nat _ _ = refl

  _∘nto_ : ∀ {F G H : Outer-functor ℂ} → G =>o H → F =>o G → F =>o H
  _∘nto_ α β .ηo x = α .ηo (β .ηo x)
  _∘nto_ α β .ηo-fib px = α .ηo-fib (β .ηo px) ∙ β .ηo-fib px
  _∘nto_ {H = H} α β .is-naturalo px y f =
    ap (α .ηo) (β .is-naturalo px y f)
    ∙ α .is-naturalo (β .ηo px) y (adjusti (sym (β .ηo-fib px)) refl f)
    ∙ ap (H .P₁ _) (Internal-hom-path refl)
  (α ∘nto β) .ηo-nat px σ =
    α .ηo-nat (β .ηo px) σ ∙ ap (α .ηo) (β .ηo-nat px σ)
```

These are almost definitionally a precategory, requiring only an appeal
to extensionality to establish the laws.

<!--
```agda
module _ (ℂ : Internal-cat) where
  open Internal-cat ℂ
```
-->

```agda
  Outer-functors : Precategory (o ⊔ ℓ) (o ⊔ ℓ)
  Outer-functors .Precategory.Ob = Outer-functor ℂ
  Outer-functors .Precategory.Hom = _=>o_
  Outer-functors .Precategory.Hom-set _ _ = hlevel 2
  Outer-functors .Precategory.id = idnto
  Outer-functors .Precategory._∘_ = _∘nto_
  Outer-functors .Precategory.idr α = Outer-nat-path (λ _ → refl)
  Outer-functors .Precategory.idl α = Outer-nat-path (λ _ → refl)
  Outer-functors .Precategory.assoc α β γ = Outer-nat-path (λ _ → refl)
```

<!--
```agda
module _ (prods : has-products C) (ℂ : Internal-cat) where
  open Internal-cat ℂ
  open Binary-products C prods
```
-->

## The constant-functor functor

If $\cC$ is a category with products, and $\bC$ is a category internal
to $\cC$, then we can construct a _constant outer-functor functor_ $\cC
\to \rm{Out}(\bC)$.

```agda
  Δo : Functor C (Outer-functors ℂ)
  Δo .F₀ = ConstO prods
  Δo .F₁ = const-nato prods
  Δo .F-id = Outer-nat-path λ px →
    ap₂ ⟨_,_⟩ (idl _) refl
    ∙ sym (⟨⟩∘ px)
    ∙ eliml ⟨⟩-η
  Δo .F-∘ f g = Outer-nat-path λ px →
    ⟨ (f ∘ g) ∘ π₁ ∘ px , π₂ ∘ px ⟩                                        ≡⟨ products! C prods ⟩
    ⟨ f ∘ π₁ ∘ ⟨ g ∘ π₁ ∘ px , π₂ ∘ px ⟩ , π₂ ∘ ⟨ g ∘ π₁ ∘ px , π₂ ∘ px ⟩ ⟩ ∎
```

## Outer functors on discrete internal categories

We shall now give a short characterisation of outer functors on
[[discrete internal categories]]. For some motivation, let us examine
the 1-categorical analog: presheaves on [[discrete categories]].
With a bit of thought, we can notice that such a presheaf would be
equivalent to a family of sets: functoriality gives us no extra structure,
as the category we are taking presheaves over has no interesting morphisms!

Outer-functors→Slice internalize this fact to a category $\cC$, we need an internal notion
of a family of objects in $\cC$: as we have already seen, slices in $\cC$
fit this role perfectly. This suggests that the category of outer functors
on a discrete internal category $X$ is equivalent to the [[slice category]]
over $X$.

We shall by constructing a functor from the category of outer functors
on a (not necessarily discrete) internal category $\bC$ into the slice
category $\cC / \bC_0$.

<!--
```agda
open Internal-hom
open /-Obj
open /-Hom
```
-->

```agda
module _ (ℂ : Internal-cat) where
  open Internal-cat ℂ

  Outer-functors→Slice : Functor (Outer-functors ℂ) (Slice C C₀)
```

Each outer functor $P$ gets sent to its total space $\int P \to \bC_0$.

```agda
  Outer-functors→Slice .F₀ P .domain = P .∫P
  Outer-functors→Slice .F₀ P .map = P .P₀ id
```

Moreover, each outer natural transformation induces a morphism between
the corresponding total spaces.

```agda
  Outer-functors→Slice .F₁ α .map = α .ηo id
  Outer-functors→Slice .F₁ {P} {Q} α .commutes =
    Q .P₀ id ∘ α .ηo id   ≡⟨ Q .P₀-nat id (α .ηo id) ⟩
    Q .P₀ (id ∘ α .ηo id) ≡⟨ ap (Q .P₀) (idl _) ⟩
    Q .P₀ (α .ηo id)      ≡⟨ α .ηo-fib id ⟩
    P .P₀ id              ∎
```

Functoriality follows from some easy algebra.

```agda
  Outer-functors→Slice .F-id = trivial!
  Outer-functors→Slice .F-∘ α β =
    ext (ap (α .ηo) (sym (idl _)) ∙ sym (α .ηo-nat id (β .ηo id)))
```
Additionally, this functor is [[faithful]].

```agda
  Outer-functors→Slice-faithful : is-faithful (Outer-functors→Slice)
  Outer-functors→Slice-faithful {P} {Q} {α} {β} p = ext λ px →
    α .ηo px      ≡⟨ ap (α .ηo) (sym (idl px)) ∙ sym (α .ηo-nat id px) ⟩
    α .ηo id ∘ px ≡⟨ ap₂ _∘_ (ap map p) refl ⟩
    β .ηo id ∘ px ≡˘⟨ ap (β .ηo) (sym (idl px)) ∙ sym (β .ηo-nat id px) ⟩
    β .ηo px      ∎
```

When $\bC$ is a discrete internal category, this functor is full.

```agda
Outer-functors→Slice-full : ∀ {X} → is-full (Outer-functors→Slice (Disci C X))
```

Let $\alpha$ be a morphism of slices between $\int P \to X$ and $\int Q \to X$,
where $P, Q$ are two outer functors. The key observation we need to make
is that for every generalized element $p : \int P$, the underlying objects
of $P(p)$ and $P(\alpha \circ p)$ are identical, which follows from some
tedious symbol shuffling.

```agda
Outer-functors→Slice-full {X} {P} {Q} α = pure (α-nat , ext (idr _)) where
  abstract
    ob₀ : ∀ {Γ} (px : Hom Γ (P .∫P)) → Q .P₀ (α .map ∘ px) ≡ P .P₀ px
    ob₀ px =
      Q .P₀ (α .map ∘ px)    ≡˘⟨ Q .P₀-nat (α .map) px ⟩
      Q .P₀ (α .map) ∘ px    ≡⟨ pushl (ap (Q .P₀) (sym (idl _)) ∙ sym (Q .P₀-nat id (α .map))) ⟩
      Q .P₀ id ∘ α .map ∘ px ≡⟨ pulll (α .commutes) ⟩
      P .P₀ id ∘ px          ≡⟨ P .P₀-nat id px ∙ ap (P .P₀) (idl px) ⟩
      P .P₀ px ∎
```

With that lemma out of the way, we can construct our outer natural
transformation. The components of the natural transformation are the
easiest bit, as we need it to line up with $\alpha$, and our earlier
observation ensures that this choice is suitably fibred.

```agda
  α-nat : P =>o Q
  α-nat .ηo x = α .map ∘ x
  α-nat .ηo-fib = ob₀
```

Unfortunately, naturality is more difficult. On one hand, the intuition
is straightforward: discrete categories only have identity morphisms, so
naturality is trivial. However, convincing Agda of this fact is anything
but!

```
  α-nat .is-naturalo px h σ =
    J-dep
      (λ h σ p q → α .map ∘ P .P₁ px σ ≡ Q .P₁ (α .map ∘ px) (adjusti (sym (ob₀ px)) refl σ))
      (ap₂ _∘_ refl (P .P-id px)
       ∙ sym (Q .P-id (map α ∘ px))
       ∙ apd (λ i f → Q .P₁ (map α ∘ px) {y = ob₀ px i} f) (Internal-hom-pathp refl _ (ob₀ px)))
      (Disci-hom→ob-path C σ)
      (is-prop→pathp (λ _ → Disci-hom-is-prop C) (Disci.idi C X (P .P₀ px)) σ)
  α-nat .ηo-nat px σ = sym (assoc _ _ _)
```

Finally, we shall show that this functor is an isomorphism of categories
when $\bC$ is discrete. We've already shown that it's fully faithful,
so all that remains is showing that the action on objects is an equivalence.

```agda
Outer-functors→Slice-iso : ∀ {X} → is-precat-iso (Outer-functors→Slice (Disci C X))
Outer-functors→Slice-iso {X} .is-precat-iso.has-is-ff =
  full+faithful→ff (Outer-functors→Slice (Disci C X))
    Outer-functors→Slice-full
    (Outer-functors→Slice-faithful (Disci C X))
```

If $\bC$ is discrete, then it is relatively easy to show that every
slice can be upgraded to an outer functor: the functorial action does
nothing, so almost all the conditions are `refl`{.Agda}.

```agda
Outer-functors→Slice-iso {X} .is-precat-iso.has-is-iso = eqv
  where
    slice→outer-functor : /-Obj {C = C} X → Outer-functor (Disci C X)
    slice→outer-functor f .∫P = f .domain
    slice→outer-functor f .P₀ x = f .map ∘ x
    slice→outer-functor f .P₁ px h = px
    slice→outer-functor f .P₁-tgt px h =
      sym (h .has-tgt) ∙ h .has-src
    slice→outer-functor f .P-id _ = refl
    slice→outer-functor f .P-∘ px h1 h2 = refl
    slice→outer-functor f .P₀-nat px σ = sym (assoc _ _ _)
    slice→outer-functor f .P₁-nat px h σ = refl
```

Showing that this forms an equivalence is a bit more clunky.
Intuitively, we get the same functor out the other end: the action on
morphisms does not matter, as $\bC$ is discrete. Unfortunately, proof
assistants, so this involves a bit of ugly path-munging.

```agda
    eqv : is-equiv _
    eqv =
      is-iso→is-equiv $
      iso slice→outer-functor
        (λ f →
          /-Obj-path refl (idr _))
        (λ P →
          Outer-functor-path
            refl
            (ext λ px → P .P₀-nat id px ∙ ap (P .P₀) (idl px))
            (funextP λ px → funext-dep λ {y} {y'} p →
              sym (P .P-id px)
              ∙ apd (λ i f → P .P₁ px {y = Disci-hom→ob-path C y' i} f)
                  (is-prop→pathp (λ i → Disci-hom-is-prop C) (Disci.idi C X (P .P₀ px)) y')))

```
