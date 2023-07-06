<!--
```agda
open import Cat.Prelude

open import Cat.Functor.Bifunctor
open import Cat.Functor.Base
open import Cat.Functor.Equivalence
open import Cat.Instances.Functor
open import Cat.Monoidal.Base

import Cat.Reasoning
```
-->

```agda
module Cat.Monoidal.Reasoning
   {ov ℓv} {V : Precategory ov ℓv}
   (V-monoidal : Monoidal-category V)
  where
```

<!--
```agda
open Cat.Reasoning V
open Monoidal-category V-monoidal public
open _=>_

private variable
  A B C D X Y Z : Ob
```
-->

# Reasoning in a Monoidal Category

Monoidal Categories are complicated beasts, so we will need quite a few
tools to tame them.

## Some Preliminary Lemmas

Whiskering along unit gives an equivalence, as the unitors yield
natural isomorphisms to the identity functor.

```agda
▶-is-equivalence : is-equivalence (Unit ▶F)
▶-is-equivalence =
  is-equivalence-natural-iso unitor-l Id-is-equivalence

◀-is-equivalence : is-equivalence (◀F Unit)
◀-is-equivalence =
  is-equivalence-natural-iso unitor-r Id-is-equivalence
```


## Variants of the Triangle Identity

When writing out the definition of a monoidal category, we made a
somewhat arbitrary choice to privledge `triangle`{.Agda}. In fact, there
are a total of 4 versions of this coherence!

We first note that we could have used the other direction of the
natural isomorphisms.

```agda
triangle-iso : (ρ≅ ◀Iso B) ∘Iso α≅ A Unit B ≡ A ▶Iso λ≅
triangle-iso = ≅-path-from triangle

triangle-inv : α→ A Unit B ∘ (ρ→ ◀ B) ≡ (A ▶ λ→)
triangle-inv = ap to triangle-iso
```

Furthermore, we could have swapped the roles of left and right
unitors.

```agda
triangle-sym : (A ▶ λ←) ∘ α→ A Unit B ≡ (ρ← ◀ B)
triangle-sym {A = A} {B = B} = 
  (A ▶ λ←) ∘ α→ A Unit B               ≡⟨ pushl (sym triangle) ⟩
  (ρ← ◀ B) ∘ α← A Unit B ∘ α→ A Unit B ≡⟨ elimr (associator.invr ηₚ _) ⟩
  ρ← ◀ B ∎

triangle-sym-iso : (A ▶Iso λ≅) ∘Iso (α≅ A Unit B Iso⁻¹) ≡ (ρ≅ ◀Iso B)
triangle-sym-iso = ≅-path-from triangle-sym

triangle-sym-inv : α← A Unit B ∘ (A ▶ λ→) ≡ (ρ→ ◀ B)
triangle-sym-inv = ap to triangle-sym-iso
```

## Variants of the Pentagon Identity

Like the triangle identity, we can swap the pentagon identity around.

```agda
pentagon-iso
  : (α≅ A B C ◀Iso D) ∘Iso α≅ A (B ⊗ C) D ∘Iso (A ▶Iso α≅ B C D)
  ≡ α≅ (A ⊗ B) C D ∘Iso α≅ A B (C ⊗ D)
pentagon-iso = ≅-path-from pentagon

pentagon-inv
  : ∀ {A B C D}
  → (A ▶ α→ B C D) ∘ α→ A (B ⊗ C) D ∘ (α→ A B C ◀ D)
  ≡ α→ A B (C ⊗ D) ∘ α→ (A ⊗ B) C D
pentagon-inv = assoc _ _ _ ∙ ap to pentagon-iso
```

We also will need to use the pentagon identity with two of the sides
flipped; we call this the "long" pentagon identities for reasons that should
become evident.

```agda
pentagon-long-iso-▶
  : (A ▶Iso α≅ B C D)
  ≡ (α≅ A (B ⊗ C) D Iso⁻¹) ∘Iso ((α≅ A B C Iso⁻¹) ◀Iso D)
    ∘Iso α≅ (A ⊗ B) C D ∘Iso α≅ A B (C ⊗ D)
pentagon-long-iso-▶ =
  Iso-swapl (Iso-swapl pentagon-iso)
  ∙ ap₂ _∘Iso_ refl (ap₂ _∘Iso_ (≅-path refl) refl)

pentagon-long-▶
  : (A ▶ α→ B C D) ≡ α→ A B (C ⊗ D) ∘ α→ (A ⊗ B) C D ∘ (α← A B C ◀ D) ∘ α← A (B ⊗ C) D 
pentagon-long-▶ =
  ap to pentagon-long-iso-▶
  ∙ sym (assoc _ _ _)
  ∙ sym (assoc _ _ _)

pentagon-long-▶-inv
  : A ▶ α← B C D ≡ α→ A (B ⊗ C) D ∘ (α→ A B C ◀ D) ∘ α← (A ⊗ B) C D ∘ α← A B (C ⊗ D)
pentagon-long-▶-inv =
  ap from pentagon-long-iso-▶

pentagon-long-iso-◀
  : (α≅ A B C ◀Iso D)
  ≡ α≅ (A ⊗ B) C D ∘Iso α≅ A B (C ⊗ D)
    ∘Iso (A ▶Iso ((α≅ B C D) Iso⁻¹)) ∘Iso (α≅ A (B ⊗ C) D Iso⁻¹)
pentagon-long-iso-◀ =
  Iso-swapr {b = α≅ _ _ _}
    (Iso-swapr {b = _ ▶Iso α≅ _ _ _} {c = α≅ _ _ _ ∘Iso α≅ _ _ _}
      (≅-path pentagon-inv))
  ∙ ≅-path (assoc _ _ _ ∙ assoc _ _ _)

pentagon-long-◀
  : α→ A B C ◀ D ≡ α← A (B ⊗ C) D ∘ (A ▶ α← B C D) ∘ α→ A B (C ⊗ D) ∘ α→ (A ⊗ B) C D
pentagon-long-◀ =
  ap to pentagon-long-iso-◀
  ∙ sym (assoc _ _ _)
  ∙ sym (assoc _ _ _)

pentagon-long-◀-inv
  : α← A B C ◀ D ≡ α← (A ⊗ B) C D ∘ α← A B (C ⊗ D) ∘ (A ▶ α→ B C D) ∘ α→ A (B ⊗ C) D
pentagon-long-◀-inv =
  ap from pentagon-long-iso-◀
```

## Alternative Coherences

Applying the left unitor is the same as reassociating then whiskering the
left unitor, as in the diagram below.

~~~{.quiver}
\begin{tikzcd}
  {A \otimes B} && {(I \otimes A) \otimes B} \\
  \\
  && {I \otimes (A \otimes B)}
  \arrow["\lambda"', from=1-1, to=3-3]
  \arrow["{\lambda \blacktriangleleft B}", from=1-1, to=1-3]
  \arrow["\alpha"{description}, from=1-3, to=3-3]
\end{tikzcd}~~~

To show this, note that $I \otimes -$ is an equivalence. In particular,
this means that $ \otimes -$ is faithful. From here, it's a matter
of applying the long pentagon identity, and then cleaning up
with the triangle identity and naturality.

```
assoc-unitor-l : α→ Unit A B ∘ (λ→ ◀ B) ≡ λ→
assoc-unitor-l =
  is-equivalence→is-faithful (Unit ▶F) ▶-is-equivalence $
  (_ ▶ (α→ _ _ _ ∘ (λ→ ◀ _)))                                        ≡⟨ ▶F.F-∘ _ _ ⟩
  (_ ▶ α→ _ _ _) ∘ (_ ▶ (λ→ ◀ _))                                    ≡⟨ ap₂ _∘_ pentagon-long-▶ refl ⟩
  (α→ _ _ _ ∘ α→ _ _ _ ∘ (α← _ _ _ ◀ _) ∘ α← _ _ _) ∘ (_ ▶ (λ→ ◀ _)) ≡⟨ extendr (extendr (pullr (associator.from .is-natural _ _ _))) ⟩
  (α→ _ _ _ ∘ α→ _ _ _ ∘ (α← _ _ _ ◀ _)) ∘ ((_ ▶ λ→) ◀ _) ∘ α← _ _ _ ≡⟨ extendl (extendr (pullr (◀F.collapse triangle-sym-inv))) ⟩
  (α→ _ _ _ ∘ α→ _ _ _) ∘ ((ρ→ ◀ _) ◀ _) ∘ α← _ _ _                  ≡⟨ extendl (extendr (associator.to .is-natural _ _ _)) ⟩
  (α→ _ _ _ ∘ (ρ→ ⊗₁ (id ⊗₁ id))) ∘ α→ _ _ _ ∘ α← _ _ _              ≡⟨ elimr (associator.invl ηₚ _) ⟩
  α→ _ _ _ ∘ (ρ→ ⊗₁ ⌜ id ⊗₁ id ⌝)                                    ≡⟨ ap! -⊗-.F-id ⟩
  α→ _ _ _ ∘ (ρ→ ◀ _)                                                ≡⟨ triangle-inv ⟩
  (_ ▶ λ→) ∎

assoc-unitor-l-iso : (λ≅ ◀Iso B) ∘Iso α≅ Unit A B ≡ λ≅
assoc-unitor-l-iso = ≅-path assoc-unitor-l

assoc-unitor-l-inv : (λ← ◀ B) ∘ α← Unit A B ≡ λ←
assoc-unitor-l-inv = ap from assoc-unitor-l-iso
```

We can show a similar result for the right unitor.

```agda
assoc-unitor-r : α← A B Unit ∘ (A ▶ ρ→) ≡ ρ→
assoc-unitor-r =
  is-equivalence→is-faithful (◀F Unit) ◀-is-equivalence $
  (α← _ _ _ ∘ (_ ▶ ρ→)) ◀ _                                          ≡⟨ ◀F.F-∘ _ _ ⟩
  (α← _ _ _ ◀ _) ∘ ((_ ▶ ρ→) ◀ _)                                    ≡⟨ ap₂ _∘_ pentagon-long-◀-inv refl ⟩
  (α← _ _ _ ∘ α← _ _ _ ∘ (_ ▶ α→ _ _ _) ∘ α→ _ _ _) ∘ ((_ ▶ ρ→) ◀ _) ≡⟨ extendr (extendr (pullr (associator.to .is-natural _ _ _))) ⟩
  (α← _ _ _ ∘ α← _ _ _ ∘ (_ ▶ α→ _ _ _)) ∘ (_ ▶ (ρ→ ◀ _)) ∘ α→ _ _ _ ≡⟨ extendl (extendr (pullr (▶F.collapse triangle-inv))) ⟩
  (α← _ _ _ ∘ α← _ _ _) ∘ (_ ▶ (_ ▶ λ→)) ∘ α→ _ _ _                  ≡⟨ extendl (extendr (associator.from .is-natural _ _ _)) ⟩
  (α← _ _ _ ∘ (⌜ (id ⊗₁ id) ⌝ ⊗₁ λ→)) ∘ α← _ _ _ ∘ α→ _ _ _          ≡⟨ elimr (associator.invr ηₚ _) ⟩
  (α← _ _ _ ∘ (⌜ (id ⊗₁ id) ⌝ ⊗₁ λ→))                                ≡⟨ ap! -⊗-.F-id ⟩
  α← _ _ _ ∘ (_ ▶ λ→)                                                ≡⟨ triangle-sym-inv ⟩
  ρ→ ◀ _ ∎

assoc-unitor-r-iso : (A ▶Iso ρ≅) ∘Iso (α≅ A B Unit Iso⁻¹) ≡ ρ≅
assoc-unitor-r-iso = ≅-path assoc-unitor-r

assoc-unitor-r-inv : (A ▶ ρ←) ∘ α→ A B Unit ≡ ρ←
assoc-unitor-r-inv = ap from assoc-unitor-r-iso
```

