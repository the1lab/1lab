<!--
```agda
open import Cat.Allegory.Base
open import Cat.Prelude

open import Order.Frame
open import Order.Base

import Order.Frame.Reasoning
```
-->

```agda
module Cat.Allegory.Instances.Mat where
```

# Frame-valued matrices

Let $L$ be a [frame]: it could be the frame of opens of a locale, for
example. It turns out that $L$ has enough structure that we can define
an [allegory], where the objects are sets, and the morphisms $A \rel B$
are given by $A \times B$-matrices valued in $L$.

[frame]: Order.Frame.html
[allegory]: Cat.Allegory.Base.html

<!--
```agda
module _ {o ℓ : Level} (L : Frame o ℓ) where
  open Order.Frame.Reasoning (L .snd)
  open Precategory
  private module A = Allegory
```
-->

The identity matrix has an entry $\top$ at position $(i, j)$ iff $i =
j$, which we can express independently of whether $i = j$ is decidable
by saying that the identity matrix has $(i,j)$th entry $\bigvee_{i = j}
\top$. The composition of $M : B \rel C$ and $N : A \rel B$ has $(a,c)$th
entry given by

$$
\bigvee_{b : B} N(a,b) \wedge M(b,c) \text{,}
$$

which is easily seen to be an analogue of the $\sum_{b = 0}^{B}
N(a,b)M(b,c)$ which implements composition when matrices take values in
a ring. The infinite distributive law is applied frequently to establish
that this is, indeed, a category:

```agda
  Mat : Precategory (lsuc o) o
  Mat .Ob          = Set o
  Mat .Hom A B     = ∣ A ∣ → ∣ B ∣ → ⌞ L ⌟
  Mat .Hom-set x y = hlevel!

  Mat .id x y              = ⋃ λ (_ : x ≡ y) → top
  Mat ._∘_ {y = y} M N i j = ⋃ λ k → N i k ∩ M k j

  Mat .idr M = ext λ i j →
    ⋃ (λ k → ⋃ (λ _ → top) ∩ M k j) ≡⟨ ⋃-apᶠ (λ k → ∩-comm ∙ ⋃-distribl _ _) ⟩
    ⋃ (λ k → ⋃ (λ _ → M k j ∩ top)) ≡⟨ ⋃-apᶠ (λ k → ⋃-apᶠ λ i → ∩-idr) ⟩
    ⋃ (λ k → ⋃ (λ _ → M k j))       ≡⟨ ⋃-twice _ ⟩
    ⋃ (λ (k , _) → M k j)           ≡⟨ ⋃-singleton (contr _ Singleton-is-contr) ⟩
    M i j                           ∎
  Mat .idl M = ext λ i j →
    ⋃ (λ k → M i k ∩ ⋃ (λ _ → top)) ≡⟨ ⋃-apᶠ (λ k → ⋃-distribl _ _) ⟩
    ⋃ (λ k → ⋃ (λ _ → M i k ∩ top)) ≡⟨ ⋃-apᶠ (λ k → ⋃-apᶠ λ j → ∩-idr) ⟩
    ⋃ (λ x → ⋃ (λ _ → M i x))       ≡⟨ ⋃-twice _ ⟩
    ⋃ (λ (k , _) → M i k)           ≡⟨ ⋃-singleton (contr _ (λ p i → p .snd (~ i) , λ j → p .snd (~ i ∨ j))) ⟩
    M i j                           ∎

  Mat .assoc M N O = ext λ i j →
    ⋃ (λ k → ⋃ (λ l → O i l ∩ N l k) ∩ M k j)   ≡⟨ ⋃-apᶠ (λ k → ⋃-distribr _ _) ⟩
    ⋃ (λ k → ⋃ (λ l → (O i l ∩ N l k) ∩ M k j)) ≡⟨ ⋃-twice _ ⟩
    ⋃ (λ (k , l) → (O i l ∩ N l k) ∩ M k j)     ≡⟨ ⋃-apᶠ (λ _ → sym ∩-assoc) ⟩
    ⋃ (λ (k , l) → O i l ∩ (N l k ∩ M k j))     ≡⟨ ⋃-apⁱ ×-swap ⟩
    ⋃ (λ (l , k) → O i l ∩ (N l k ∩ M k j))     ≡˘⟨ ⋃-twice _ ⟩
    ⋃ (λ l → ⋃ (λ k → O i l ∩ (N l k ∩ M k j))) ≡⟨ ⋃-apᶠ (λ k → sym (⋃-distribl _ _)) ⟩
    ⋃ (λ l → O i l ∩ ⋃ (λ k → N l k ∩ M k j))   ∎
```

Most of the structure of an allegory now follows directly from the fact
that frames are also [[meet semilattices]]: the ordering, duals, and
intersections are all computed pointwise. The only thing which requires
a bit more algebra is the verification of the modular law:

```agda
  Matrices : Allegory (lsuc o) o (o ⊔ ℓ)
  Matrices .A.cat = Mat
  Matrices .A._≤_ M N = ∀ i j → M i j ≤ N i j

  Matrices .A.≤-thin          = hlevel!
  Matrices .A.≤-refl i j      = ≤-refl
  Matrices .A.≤-trans p q i j = ≤-trans (p i j) (q i j)
  Matrices .A.≤-antisym p q   = ext λ i j → ≤-antisym (p i j) (q i j)
  Matrices .A._◆_ p q i j     = ⋃≤⋃ (λ k → ∩≤∩ (q i k) (p k j))

  Matrices .A._† M i j     = M j i
  Matrices .A.dual-≤ x i j = x j i
  Matrices .A.dual M       = refl
  Matrices .A.dual-∘       = ext λ i j → ⋃-apᶠ λ k → ∩-comm

  Matrices .A._∩_ M N i j    = M i j ∩ N i j
  Matrices .A.∩-le-l i j     = ∩≤l
  Matrices .A.∩-le-r i j     = ∩≤r
  Matrices .A.∩-univ p q i j = ∩-universal _ (p i j) (q i j)

  Matrices .A.modular f g h i j =
    ⋃ (λ k → f i k ∩ g k j) ∩ h i j                     =⟨ ⋃-distribr _ _ ∙ ⋃-apᶠ (λ _ → sym ∩-assoc) ⟩
    ⋃ (λ k → f i k ∩ (g k j ∩ h i j))                   =⟨ ⋃-apᶠ (λ k → ap₂ _∩_ refl ∩-comm) ⟩
    ⋃ (λ k → f i k ∩ h i j ∩ g k j)                     ≤⟨ ⋃≤⋃ (λ i → ∩-universal _ (∩≤∩r (⋃-inj j)) (≤-trans ∩≤r ∩≤r)) ⟩
    ⋃ (λ k → (f i k ∩ ⋃ (λ l → h i l ∩ g k l)) ∩ g k j) ≤∎
```
