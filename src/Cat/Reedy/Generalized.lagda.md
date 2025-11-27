---
description: |
  Generalized Reedy categories.
---

<!--
```agda
open import Cat.Morphism.Factorisation.Orthogonal
open import Cat.Functor.Adjoint.Reflective
open import Cat.Functor.WideSubcategory
open import Cat.Functor.Conservative
open import Cat.Direct.Generalized
open import Cat.Functor.Properties
open import Cat.Functor.Adjoint
open import Cat.Morphism.Class
open import Cat.Prelude

open import Data.Wellfounded.Properties
open import Data.Nat.Order
open import Data.Nat.Base

import Cat.Functor.Reasoning.FullyFaithful
import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Reedy.Generalized where
```

<!--
```agda
module _ {o ℓ} (A : Precategory o ℓ) where
  private module A = Cat.Reasoning A
```
-->

# Generalized Reedy categories

:::{.definition #generalized-reedy-structure}
A *generalized Reedy structure* on a [[precategory]] $\cA$ consists of:

- two classes of morphisms $\cA^{-}, \cA^{+} \subseteq \cA$, and
- a function $\mathrm{dim} : \cA_{0} \to \NN$

```agda
  record is-generalized-reedy
    {ℓ⁻ ℓ⁺} (Neg : Arrows A ℓ⁻) (Pos : Arrows A ℓ⁺)
    (dim : A.Ob → Nat)
    : Type (o ⊔ ℓ ⊔ ℓ⁺ ⊔ ℓ⁻) where
```

subject to the following conditions:

- The pair $(\cA^{-}, \cA^{+})$ forms an [[orthogonal factorisation system]].
  In particular, this means that both $\cA^{-}$ and $\cA^{+}$ contain all
  isomorphism of $\cA$ and are closed under composition.
:::


```agda
    field
      neg-pos-ofs : is-ofs A Neg Pos

    open is-ofs neg-pos-ofs renaming
      ( is-iso→in-L to is-iso→neg
      ; is-iso→in-R to is-iso→pos
      ; L-is-stable to neg-∘
      ; R-is-stable to pos-∘
      ; L-subcat to Neg-subcat
      ; R-subcat to Pos-subcat
      )
      public
```

- If $f : \cA(x, y)$ is invertible, then $\mathrm{dim}(x) = \mathrm{dim}(y)$.
- If $f : \cA^{-}(x, y)$ is non-invertible then $\mathrm{dim}(x) > \mathrm{dim}(y)$.
- If $f : \cA^{+}(x, y)$ is non-invertible then $\mathrm{dim}(x) < \mathrm{dim}(y)$.

```agda
    field
      dim-iso : ∀ {x y} {f : A.Hom x y} → A.is-invertible f → dim x ≡ dim y
      dim-neg : ∀ {x y} {f : A.Hom x y} → f ∈ Neg → ¬ (A.is-invertible f) → dim x > dim y
      dim-pos : ∀ {x y} {f : A.Hom x y} → f ∈ Pos → ¬ (A.is-invertible f) → dim x < dim y
```

- If $f : \cA(x, y)$ is in $\cA^{-} \cap \cA^{+}$, then $f$ must be
  invertible[^1].

[^1]: In the presence of [[excluded middle]], the previous three axioms
  imply that every map $f : \cA(x, y)$ with $f \in \cA^{-} \cap \cA^{+}$
  must be invertible, as otherwise we'd have $\mathrm{dim}(x) < \mathrm{dim}(y) < \mathrm{dim}(x)$.

  However, in constructive foundations the best we can do is show that $f$ is
  not non-invertible, which is why we explicitly require this as an axiom.

```agda
    field
      neg+pos→invertible
        : ∀ {x y} {f : A.Hom x y}
        → f ∈ Neg
        → f ∈ Pos
        → A.is-invertible f
```

- Finally, we require that for every $f : y \iso y$ and $p : \cA^{-}(x, y)$,
  if $f \circ p = p$ then $p = \id$. In other words, the stabilizer subgroup
  of $\mathrm{Aut}(y)$ relative to $p : \cA^{-}(x, y)$ is trivial.

```agda
    field
      neg-trivial-stabilizer
        : ∀ {x y} {f : A.Hom y y} {p : A.Hom x y}
        → A.is-invertible f
        → p ∈ Neg
        → f A.∘ p ≡ p
        → f ≡ A.id
```

The purpose of this final axiom is to ensure that isomorphisms in $\cA$ view
morphisms in $\cA^{-1}$ as [[epimorphisms]].

```agda
    iso-neg-epic
      : ∀ {x y z} {f₁ f₂ : A.Hom y z} {p : A.Hom x y}
      → A.is-invertible f₁
      → A.is-invertible f₂
      → p ∈ Neg
      → f₁ A.∘ p ≡ f₂ A.∘ p
      → f₁ ≡ f₂
```

This follows from some isomorphism shuffling. All isomorphisms are
[[monomorphisms]], so it suffices to prove that $f_{2}^{-1} \circ f_{1} = f_{2}^{-1} \circ f_2 = \id$.
However, $f_{2}^{-1} \circ f_{1}$ is also an iso, so we can apply our axiom
to reduce the goal to showing that $f_{2}^{-1} \circ f_{1} \circ p = p$, which
follows from our assumption that $f_{1} \circ p = f_{2} \circ p$.

```agda
    iso-neg-epic {f₁ = f₁} {f₂ = f₂} {p = p} f₁-inv f₂-inv p∈A⁻ f₁∘p=f₂∘p =
      A.invertible→monic f₂⁻¹-inv f₁ f₂ $
        f₂.inv A.∘ f₁ ≡⟨ f₂⁻¹∘f₁∘p=id ⟩
        A.id          ≡˘⟨ f₂.invr ⟩
        f₂.inv A.∘ f₂ ∎
      where
        module f₁ = A.is-invertible f₁-inv
        module f₂ = A.is-invertible f₂-inv

        f₂⁻¹-inv : A.is-invertible f₂.inv
        f₂⁻¹-inv = A.is-invertible-inverse f₂-inv

        f₂⁻¹∘f₁∘p=id : f₂.inv A.∘ f₁ ≡ A.id
        f₂⁻¹∘f₁∘p=id =
          neg-trivial-stabilizer (A.invertible-∘ f₂⁻¹-inv f₁-inv) p∈A⁻
          $ A.reassocl.from
          $ A.pre-invl.from f₂-inv f₁∘p=f₂∘p
```

We can also upgrade the stabilizer condition to an equivalence.

```agda
    neg-trivial-stabilizer-equiv
      : ∀ {x y} {f : A.Hom y y} {p : A.Hom x y}
      → p ∈ Neg
      → (A.is-invertible f × f A.∘ p ≡ p) ≃ (f ≡ A.id)
    neg-trivial-stabilizer-equiv p∈A⁻ = prop-ext!
      (λ (f-inv , fp=p) → neg-trivial-stabilizer f-inv p∈A⁻ fp=p)
      (λ f=id → (A.subst-is-invertible (sym f=id) A.id-invertible) , A.eliml f=id)
```

<!--
```agda
  record Generalized-reedy (ℓ⁻ ℓ⁺ : Level) : Type (o ⊔ ℓ ⊔ lsuc ℓ⁻ ⊔ lsuc ℓ⁺) where
    field
      Neg : Arrows A ℓ⁻
      Pos : Arrows A ℓ⁺
      dim : A.Ob → Nat
      has-generalized-reedy : is-generalized-reedy Neg Pos dim
    open is-generalized-reedy has-generalized-reedy public
```
-->

## Reedy structures and direct categories

```agda
module _
  {oc ℓc oa ℓa ℓ⁻ ℓ⁺}
  {C : Precategory oc ℓc} {A : Precategory oa ℓa}
  {Neg : Arrows A ℓ⁻} {Pos : Arrows A ℓ⁺} {dim : Precategory.Ob A → Nat}
  (A-reedy : is-generalized-reedy A Neg Pos dim)
  where
  private
    module A where
      open Cat.Reasoning A public
      open is-generalized-reedy A-reedy public
    open is-generalized-direct
```

If $(\cA, \cA^{-}, \cA^{+}, \mathrm{dim})$ is a generalized Reedy structure,
then the wide subcategory spanned by $\cA^{+}$ is a [[generalized direct category]].

```agda
  generalized-reedy→pos-direct
    : is-generalized-direct (Wide A.Pos-subcat)
```

First, note that the inclusion functor $\iota : \cA^{+} \to \cA$ is
[[pseudomonic]] and thus [[conservative]], as $\cA^{+}$ contains
all isos. This means that if some $f : \cA^{+}(x, y)$ is non-invertible
in $\cA^{+}$, then it must also be non-invertible in $\cA$.

In particular, this means that $\mathrm{dim} : \cA_{0} \to \NN$ is
strictly monotone with respect to the relation

$$
x \prec y := \exists(f : \cA^{+}(x, y)).\ \text{\(f\) is not invertible}
$$

as non-invertible maps in $\cA^{+}$ increase dimension. This lets us
pull back well-foundedness of $\mathrm{dim}(x) < \mathrm{dim}(y)$ to
$x \prec y$, which completes the proof.

```agda
  generalized-reedy→pos-direct .≺-wf =
    reflect-wf <-wf dim $ rec! λ f ¬f-inv → A.dim-pos
      (f .witness)
      (¬f-inv ⊙ Forget-conservative)
     where
       Forget-conservative : is-conservative Forget-wide-subcat
       Forget-conservative = pseudomonic→conservative
         (is-pseudomonic-Forget-wide-subcat (A.is-iso→pos _))
         _
```



## Reflecting generalized Reedy structures

Let $(\cA, \cA^{-}, \cA^{+}, \mathrm{dim})$ be a generalized Reedy
category, and $\iota : \cC \to \cA$ be a [[reflective subcategory]]
with reflector $r \dashv \iota$.If $\cA^{-} \subseteq (\iota \circ r)^{*}(\cA^{-})$
and $\cA^{+} \subseteq (\iota \circ r)^{*}(\cA^{+})$, then
$(\iota^{*}(\cA^{-}), \iota^{*}(\cA^{+}), \mathrm{dim} \circ \iota)$ is a
generalized Reedy structure on $\cC$.

<!--
```agda
module _
  {oc ℓc oa ℓa ℓ⁻ ℓ⁺}
  {C : Precategory oc ℓc} {A : Precategory oa ℓa}
  {Neg : Arrows A ℓ⁻} {Pos : Arrows A ℓ⁺} {dim : Precategory.Ob A → Nat}
  {ι : Functor C A} {r : Functor A C}
  where
  open Functor
```
-->

```agda
  reflect-generalized-reedy
    : (r⊣ι : r ⊣ ι)
    → is-reflective r⊣ι
    → Neg ⊆ F-restrict-arrows (ι F∘ r) Neg
    → Pos ⊆ F-restrict-arrows (ι F∘ r) Pos
    → is-generalized-reedy A Neg Pos dim
    → is-generalized-reedy C
        (F-restrict-arrows ι Neg)
        (F-restrict-arrows ι Pos)
        (dim ⊙ ι .F₀)
  reflect-generalized-reedy r⊣ι ι-ff ι∘r-pos ι∘r-neg A-reedy = C-reedy where
```

<!--
```agda
    module A where
      open Cat.Reasoning A public
      open is-generalized-reedy A-reedy public

    module C = Cat.Reasoning C
    open is-generalized-reedy

    module ι = Cat.Functor.Reasoning.FullyFaithful ι ι-ff
```
-->

Our first goal is to show that $(\iota^{*}(\cA^{-}), \iota^{*}(\cA^{+})$
forms an orthogonal factorisations system on $\cC$. This follows from
some general results about reflecting OFSs onto reflective subcategories.

```agda
    C-reedy : is-generalized-reedy C _ _ _
    C-reedy .neg-pos-ofs =
      reflect-ofs r⊣ι ι-ff ι∘r-pos ι∘r-neg A.neg-pos-ofs
```

Next, let's show that the restriction of $\mathrm{dim}$ along $\iota$
is well-behaved. By definition $\iota$ is [[fully faithful]], and thus
[[conservative]]. This means that we can reflect the (non)-existence
of isomorphisms in $\cA$ into $\cA$, which in turn lets us reflect
all of the properties of dimensions.

```agda
    C-reedy .dim-iso f-inv =
      A.dim-iso (ι.F-map-invertible f-inv)
    C-reedy .dim-neg ι[f]∈A⁻ ¬f-inv =
      A.dim-neg ι[f]∈A⁻ (¬f-inv ⊙ ι.invertible.from)
    C-reedy .dim-pos ι[f]∈A⁺ ¬f-inv =
      A.dim-pos ι[f]∈A⁺ (¬f-inv ⊙ ι.invertible.from)
    C-reedy .neg+pos→invertible ι[f]∈A⁻ ι[f]∈A⁺ =
      ι.invertible.from (A.neg+pos→invertible ι[f]∈A⁻ ι[f]∈A⁺)
```

Finally, we need to show that the stabilizer subgroups of a $p : \cC(x,y)$
with $\iota(p) \in \cA^{-}$ are trivial. First, note that a map $f : \cC(y, y)$
is equal to $\id_{y}$ if and only if $\iota(f) = \id_{\iota(y)}$. However,
$\iota(p) \in \cA^{-}$ has trivial stabilizers in $\mathrm{Aut}(\iota(y))$,
so this is only true if $\iota(f)$ is invertible and $\iota(f)$ fixes $\iota(p)$.
Finally, $\iota$ is fully faithful, so this is true if and only if $f$
is invertible and $f \circ p = p$.

```agda
    C-reedy .neg-trivial-stabilizer {f = f} {p = p} f-inv ι[p]∈A⁻ f∘p=p =
      flip Equiv.from (f-inv , f∘p=p) $
        f ≡ C.id
          ≃⟨ ι.to-id ⟩
        ι.₁ f ≡ A.id
          ≃˘⟨ A.neg-trivial-stabilizer-equiv ι[p]∈A⁻ ⟩
        A.is-invertible (ι.₁ f) × ι.₁ f A.∘ ι.F₁ p ≡ ι.F₁ p
          ≃⟨ Σ-ap (ι.invertible-equiv e⁻¹) (λ _ → ι.triangle-equivl) ⟩
        C.is-invertible f × f C.∘ p ≡ p
          ≃∎
```
