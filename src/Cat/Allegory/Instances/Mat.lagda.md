```agda
open import Cat.Allegory.Base
open import Cat.Prelude

open import Order.Frame

import Order.Frame.Reasoning as Frame

module Cat.Allegory.Instances.Mat where
```

# Frame-valued matrices

A generalisation of the construction of $\bf{Rel}$ constructs an
allegory $\bf{Mat}(L)$ whose objects are sets, and where the morphisms
are "relations" with values in an arbitrary [frame] $L$. Plugging in $L
= \Omega$ recovers the usual category of relations, whereas other
choices for $L$ give rise to more interesting allegories.

[frame]: Order.Frame.html

The hardest part is constructing the actual underlying category, and
surprisingly, the hardest part of _that_ is constructing identity
morphisms. We'd like to define the identity matrix $1_{A}$ satisfying
$1_{A}(i,j) = 1$ if $i = j$, and $0$ otherwise. But unless $A$ has
decidable equality, we can't take this definition by cases as a
definition directly.

Since frames are (co)complete lattices, what we _can_ do is define
$1_{A}(i,j)$ to be the join of the constant family with value $1$
indexed by the type $i = j$. When $i$ is indeed $j$, this is the join of
a singleton-indexed family, which computes to the family's unique value.
When $i$ is not $j$, then this is an empty join, i.e., the bottom
element. This construction of diagonal $L$-matrices will be exactly what
we need to define the identity:

```agda
module _ {o} (L : Frame o) where
  private module L = Frame L
  open Precategory
  open Allegory

  private
    δ : (A : Set o) → ∣ A ∣ → ∣ A ∣ → ⌞ L ⌟
    δ A x y = L.⋃ {I = x ≡ y} (λ i → L.top)

    δ-diag : (A : Set o) (x : ∣ A ∣) → δ A x x ≡ L.top
    δ-diag A x = L.≤-antisym
      (L.⋃-universal _ (λ _ → L.introl refl))
      (L.⋃-colimiting refl _)

    δ-commutes : (A : Set o) (x y : ∣ A ∣) → δ A x y ≡ δ A y x
    δ-commutes A x y = L.≤-antisym
      (L.⋃-universal _ (λ i → L.⋃-colimiting (sym i) _))
      (L.⋃-universal _ (λ i → L.⋃-colimiting (sym i) λ v → L.top))
```

The second part of the construction is this lemma about joins whose
family has a factor of $\delta_{x}$: If we're computing the join
$\bigcup_y \delta_{x}(y)f(y)$, then, intuitively, “the only non-zero
value is f(x)”; While we can't _decide_ which value is $f(x)$'s, this is
still true even if the index set lacks decidable equality.

```agda
    δ-trace : (A : Set o) (x : ∣ A ∣) (f : ∣ A ∣ → ⌞ L ⌟)
            → L.⋃ (λ y → δ A x y L.∩ f y) ≡ f x
    δ-trace A x f = L.≤-antisym
      (L.⋃-universal (λ y → δ A x y L.∩ f y)
        (λ i →
          δ A x i L.∩ f i            L.=⟨ L.⋃-distrib′ _ ⟩
          L.⋃ (λ i′ → L.top L.∩ f i) L.≤⟨ L.⋃-universal _ (λ x=i → subst (λ e → (L.top L.∩ f e) L.≤ f x) x=i L.∩≤r) ⟩
          f x                        L.≤∎ ))
      (f x                         L.=⟨ sym L.∩-idl ⟩
       L.top L.∩ f x               L.=⟨ ap (L._∩ f x) (sym (δ-diag A x)) ⟩
       δ A x x L.∩ f x             L.≤⟨ L.⋃-colimiting x (λ y → δ A x y L.∩ f y) ⟩
       L.⋃ (λ y → δ A x y L.∩ f y) L.≤∎)
```

We define the composition to be “matrix multiplication”, i.e., the
matrix whose value at the $(c,a)$th coordinate is given by the “sum”
$\bigcup_b g(c,b)\cap f(b,a)$. In the $L = \Omega$ case, this
corresponds directly to the existential quantifier in the relational
composite.

```agda
  Mat-precat : Precategory (lsuc o) o
  Mat-precat .Ob  = Set o
  Mat-precat .Hom A B = ∣ A ∣ → ∣ B ∣ → ⌞ L ⌟
  Mat-precat .Hom-set _ _ = hlevel!
  Mat-precat .id {A} x y = δ A x y
  Mat-precat ._∘_ f g c a = L.⋃ (λ b → g c b L.∩ f b a)
```

Both identity laws follow from the `δ-trace`{.Agda} lemma we proved
above, though one of them needs commutativity in $L$:

```agda
  Mat-precat .idr {x = x} f = funext λ c → funext λ a → δ-trace x c λ z → f z a
  Mat-precat .idl {y = y} f = funext λ c → funext λ a →
    L.⋃ (λ b → f c b L.∩ δ y b a) ≡⟨ ap L.⋃ (funext λ b → L.∩-commutative ∙ ap (L._∩ f c b) (δ-commutes y b a)) ⟩
    L.⋃ (λ b → δ y a b L.∩ f c b) ≡⟨ δ-trace y a (f c) ⟩
    f c a                         ∎
```

The infinite distributive law is exactly what we need to establish that
composition in $\bf{Mat}(L)$ is associative.

```agda
  Mat-precat .assoc f g h = funext λ a → funext λ d →
    L.⋃ (λ c → L.⋃ (λ b → h a b L.∩ g b c) L.∩ f c d)   ≡⟨ ap L.⋃ (funext λ c → L.⋃-distrib′ _ ∙ ap L.⋃ (funext λ b → sym L.∩-assoc)) ⟩
    L.⋃ (λ c → L.⋃ (λ b → h a b L.∩ (g b c L.∩ f c d))) ≡⟨ L.⋃-commute _ ⟩
    L.⋃ (λ b → L.⋃ (λ c → h a b L.∩ (g b c L.∩ f c d))) ≡⟨ ap L.⋃ (funext λ c → sym (L.⋃-distrib _ _)) ⟩
    L.⋃ (λ b → h a b L.∩ L.⋃ λ c → g b c L.∩ f c d)     ∎
```

Most of the allegory structure is incredibly straightforward: The
ordering and intersections are computed pointwise, and so everything
related to those follows from $L$ being a semilattice. The relational
converse is given by transposing matrices, which is well-behaved because
meet in $L$ is a commutative operation.

```agda
  Mat : Allegory _ _ _
  Mat .cat = Mat-precat
  Mat ._≤_ f g         = ∀ a b → f a b L.≤ g a b
  Mat .≤-thin          = hlevel!
  Mat .≤-refl a b      = L.≤-refl
  Mat .≤-trans f g a b = L.≤-trans (f a b) (g a b)
  Mat .≤-antisym f g   = funext λ a → funext λ b → L.≤-antisym (f a b) (g a b)

  Mat ._† f x y     = f y x
  Mat .dual f       = refl
  Mat .dual-∘       = funext λ x → funext λ y →
    ap L.⋃ (funext λ _ → L.∩-commutative)
  Mat .dual-≤ α a b = α b a
  Mat ._∩_ f g x y = f x y L.∩ g x y
  Mat .∩-le-l a b = L.∩≤l
  Mat .∩-le-r a b = L.∩≤r
  Mat .∩-univ α β a b = L.∩-univ _ (α _ _) (β _ _)
```

Monotonicity of composition follows from monotonicity of $\bigcup$ in
the family and of $\cap$ in each variable. The only thing that needs a
bit of work is the modular law, which again requires infinite
distributivity in $L$.

```agda
  Mat ._◆_ {f = f} {f′} {g} {g′} α β x y =
    L.⋃ (λ b → g x b L.∩ f b y)   L.≤⟨ L.⋃-monotone _ _ (λ i → L.∩-monotone (β _ _) (α _ _)) ⟩
    L.⋃ (λ b → g′ x b L.∩ f′ b y) L.≤∎

  Mat .modular f g h a d =
    L.⋃ (λ b → f a b L.∩ g b d) L.∩ h a d                            L.=⟨ L.⋃-distrib′ _ ⟩
    L.⋃ (λ b → (f a b L.∩ g b d) L.∩ h a d)                          L.≤⟨ L.⋃-monotone _ _ (λ i → lemma _ _ _) ⟩
    L.⋃ (λ b → (f a b L.∩ L.⋃ (λ d′ → h a d′ L.∩ g b d′)) L.∩ g b d) L.≤∎
    where
      lemma
        : ∀ f (g h : _ → ⌞ L ⌟)
        → (f L.∩ g d) L.∩ h d L.≤ (f L.∩ L.⋃ (λ d′ → h d′ L.∩ g d′)) L.∩ g d
      lemma f g h =
        (f L.∩ g d) L.∩ h d                        L.=⟨ L.extendr (L.∩-commutative ∙ L.pushr (sym L.∩-idempotent)) ⟩
        (f L.∩ h d L.∩ g d) L.∩ g d                L.≤⟨ L.∩-monotoneₗ (L.∩-monotoneᵣ (L.⋃-colimiting d _)) ⟩
        (f L.∩ L.⋃ (λ d′ → h d′ L.∩ g d′)) L.∩ g d L.≤∎
```
