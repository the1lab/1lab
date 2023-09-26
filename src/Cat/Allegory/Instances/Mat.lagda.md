<!--
```agda
open import Cat.Allegory.Base
open import Cat.Prelude

open import Order.Frame
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
module _ {o} (L : Frame o o) where
  open Frame L hiding (Ob)
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

  Mat .idr M = funext² λ i j →
    ⋃ (λ k → ⋃ (λ _ → top) ∩ M k j) ≡⟨ ⋃-apᶠ (λ k → ∩-commutative _ _ ∙ ⋃-distrib-l _ _) ⟩
    ⋃ (λ k → ⋃ (λ _ → M k j ∩ top)) ≡⟨ ⋃-apᶠ (λ k → ap ⋃ (funext λ i → ∩-idr _)) ⟩
    ⋃ (λ k → ⋃ (λ _ → M k j))       ≡⟨ ⋃-twice _ ⟩
    ⋃ (λ (k , _) → M k j)           ≡⟨ ⋃-singleton _ (contr _ Singleton-is-contr) ⟩
    M i j                           ∎
  Mat .idl M = funext² λ i j →
    ⋃ (λ k → M i k ∩ ⋃ (λ _ → top)) ≡⟨ ⋃-apᶠ (λ k → ⋃-distrib-l _ _) ⟩
    ⋃ (λ k → ⋃ (λ _ → M i k ∩ top)) ≡⟨ ⋃-apᶠ (λ k → ⋃-apᶠ λ j → ∩-idr _) ⟩
    ⋃ (λ x → ⋃ (λ _ → M i x))       ≡⟨ ⋃-twice _ ⟩
    ⋃ (λ (k , _) → M i k)           ≡⟨ ⋃-singleton _ (contr _ (λ p i → p .snd (~ i) , λ j → p .snd (~ i ∨ j))) ⟩
    M i j                           ∎

  Mat .assoc M N O = funext² λ i j →
    ⋃ (λ k → ⋃ (λ l → O i l ∩ N l k) ∩ M k j)   ≡⟨ ⋃-apᶠ (λ k → ⋃-distrib-r) ⟩
    ⋃ (λ k → ⋃ (λ l → (O i l ∩ N l k) ∩ M k j)) ≡⟨ ⋃-twice _ ⟩
    ⋃ (λ (k , l) → (O i l ∩ N l k) ∩ M k j)     ≡⟨ ⋃-apᶠ (λ _ → sym (∩-assoc _ _ _)) ⟩
    ⋃ (λ (k , l) → O i l ∩ (N l k ∩ M k j))     ≡⟨ ⋃-apⁱ ×-swap ⟩
    ⋃ (λ (l , k) → O i l ∩ (N l k ∩ M k j))     ≡˘⟨ ⋃-twice _ ⟩
    ⋃ (λ l → ⋃ (λ k → O i l ∩ (N l k ∩ M k j))) ≡⟨ ap ⋃ (funext λ k → sym (⋃-distrib-l _ _)) ⟩
    ⋃ (λ l → O i l ∩ ⋃ (λ k → N l k ∩ M k j))   ∎
```

Most of the structure of an allegory now follows directly from the fact
that frames are also [semilattices]: the ordering, duals, and
intersections are all computed pointwise. The only thing which requires
a bit more algebra is the verification of the modular law:

[semilattices]: Order.Semilattice.html

```agda
  Matrices : Allegory (lsuc o) o o
  Matrices .A.cat = Mat
  Matrices .A._≤_ M N = ∀ i j → M i j ≤ N i j

  Matrices .A.≤-thin          = hlevel!
  Matrices .A.≤-refl i j      = ≤-refl
  Matrices .A.≤-trans p q i j = ≤-trans (p i j) (q i j)
  Matrices .A.≤-antisym p q   = funext² λ i j → ≤-antisym (p i j) (q i j)
  Matrices .A._◆_ p q i j     = ⋃-monotone (λ k → ∩-monotone (q i k) (p k j))

  Matrices .A._† M i j     = M j i
  Matrices .A.dual-≤ x i j = x j i
  Matrices .A.dual M       = refl
  Matrices .A.dual-∘       = funext² λ i j → ⋃-apᶠ λ k → ∩-commutative _ _

  Matrices .A._∩_ M N i j    = M i j ∩ N i j
  Matrices .A.∩-le-l i j     = ∩≤l _ _
  Matrices .A.∩-le-r i j     = ∩≤r _ _
  Matrices .A.∩-univ p q i j = ∩-universal _ _ _ (p i j) (q i j)

  Matrices .A.modular f g h i j =
    ⋃ (λ k → f i k ∩ g k j) ∩ h i j                     =⟨ ⋃-distrib-r ∙ ⋃-apᶠ (λ _ → sym (∩-assoc _ _ _)) ⟩
    ⋃ (λ k → f i k ∩ (g k j ∩ h i j))                   =⟨ ⋃-apᶠ (λ k → ap₂ _∩_ refl ((∩-commutative _ _))) ⟩
    ⋃ (λ k → f i k ∩ (h i j ∩ g k j))                   ≤⟨ (⋃-monotone λ l → ∩-monotone ≤-refl (∩-universal _ _ _ (fam≤⋃ _ j) (∩≤r _ _))) ⟩
    ⋃ (λ k → f i k ∩ (⋃ (λ l → h i l ∩ g k l) ∩ g k j)) =⟨ ⋃-apᶠ (λ k → ∩-assoc _ _ _) ⟩
    ⋃ (λ k → (f i k ∩ ⋃ (λ l → h i l ∩ g k l)) ∩ g k j) ≤∎
```
