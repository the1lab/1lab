<!--
```agda
open import Cat.Morphism.Orthogonal
open import Cat.Prelude

open import Cat.Displayed.Base
open import Cat.Displayed.Comprehension
open import Cat.Displayed.Comprehension.Coproduct
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Indexing
open import Cat.Displayed.Cocartesian
open import Cat.Displayed.Fibre

import Cat.Reasoning
import Cat.Displayed.Reasoning
```
-->

```agda
module Cat.Displayed.Comprehension.Coproduct.Strong where
```

<!--
```agda
```
-->

# Strong Comprehension Coproducts

Let $\cD$ and $\cE$ be a pair of [comprehension categories] over the same
base category $\cB$, such that $\cD$ has [coproducts] over $\cE$.
Type theoretically, this (roughly) corresponds to a type theory with
a pair of syntactic constructs (for instance, types and kinds), along
with mixed-mode sigma types.

We can model this using coproducts over a comprehension category, though
the elimination principle we get from this setup is pretty weak; we
really only have a recursion principle, not an elimination principle.
To model this, we need to add an extra condition. We say that a
comprehension category has **strong comprehension coproducts** if
the canonical substitution $\pi_{\cE}, \langle x , a \rangle$ forms an
[orthogonal factorisation system] with weakenings $\pi_{\cD}$. In
more elementary terms, this means that any diagram of the following form
has a **unique** filler.

~~~{.quiver}
\begin{tikzcd}
  {\Gamma,_{\cE}X,_{\cD}A} && {\Delta,_{\cD}B} \\
  \\
  {\Gamma,_{\cD}\coprod X A} && \Delta
  \arrow["{\pi_{\cE},\langle X, A\rangle}"', from=1-1, to=3-1]
  \arrow["{\pi_{\cD}}", from=1-3, to=3-3]
  \arrow["\sigma"', from=3-1, to=3-3]
  \arrow["\nu", from=1-1, to=1-3]
  \arrow["{\exists!}", dashed, from=3-1, to=1-3]
\end{tikzcd}
~~~

[comprehension categories]: Cat.Displayed.Comprehension.html
[coproducts]: Cat.Displayed.Comprehension.Coproduct.html
[orthogonal factorisation system]: Cat.Morphism.Orthogonal.html

<!--
```agda
module _
  {ob ℓb od ℓd oe ℓe} {B : Precategory ob ℓb}
  {D : Displayed B od ℓd} {E : Displayed B oe ℓe}
  {D-fib : Cartesian-fibration D} {E-fib : Cartesian-fibration E}
  (P : Comprehension D) {Q : Comprehension E}
  (coprods : has-comprehension-coproducts D-fib E-fib Q)
  where
  private
    open Cat.Reasoning B
    module E = Displayed E
    module D = Displayed D
    module P = Comprehension D D-fib P
    module Q = Comprehension E E-fib Q
    open has-comprehension-coproducts coprods
```
-->

```agda
  strong-comprehension-coproducts : Type _
  strong-comprehension-coproducts =
    ∀ {Γ Δ} (x : E.Ob[ Γ ]) (a : D.Ob[ Γ Q.⨾ x ]) (b : D.Ob[ Δ ])
    → m⊥m B (Q.πᶜ P.⨾ˢ ⟨ x , a ⟩) (P.πᶜ {x = b})
```

<!--
```agda
  record make-strong-comprehension-coproducts : Type (ob ⊔ ℓb ⊔ od ⊔ oe) where
    no-eta-equality
    field
      ∐-strong-elim
        : ∀ {Γ Δ} {x : E.Ob[ Γ ]} {a : D.Ob[ Γ Q.⨾ x ]} {b : D.Ob[ Δ ]}
        → (σ : Hom (Γ P.⨾ ∐ x a) Δ) (ν : Hom (Γ Q.⨾ x P.⨾ a) (Δ P.⨾ b))
        → σ ∘ (Q.πᶜ P.⨾ˢ ⟨ x , a ⟩) ≡ P.πᶜ ∘ ν
        → Hom (Γ P.⨾ ∐ x a) (Δ P.⨾ b)
      ∐-strong-β
        : ∀ {Γ Δ} {x : E.Ob[ Γ ]} {a : D.Ob[ Γ Q.⨾ x ]} {b : D.Ob[ Δ ]}
        → {σ : Hom (Γ P.⨾ ∐ x a) Δ} {ν : Hom (Γ Q.⨾ x P.⨾ a) (Δ P.⨾ b)}
        → (p : σ ∘ (Q.πᶜ P.⨾ˢ ⟨ x , a ⟩) ≡ P.πᶜ ∘ ν)
        → ∐-strong-elim σ ν p ∘ (Q.πᶜ P.⨾ˢ ⟨ x , a ⟩) ≡ ν
      ∐-strong-sub
        : ∀ {Γ Δ} {x : E.Ob[ Γ ]} {a : D.Ob[ Γ Q.⨾ x ]} {b : D.Ob[ Δ ]}
        → {σ : Hom (Γ P.⨾ ∐ x a) Δ} {ν : Hom (Γ Q.⨾ x P.⨾ a) (Δ P.⨾ b)}
        → (p : σ ∘ (Q.πᶜ P.⨾ˢ ⟨ x , a ⟩) ≡ P.πᶜ ∘ ν)
        → P.πᶜ ∘ ∐-strong-elim σ ν p ≡ σ
      ∐-strong-η
        : ∀ {Γ Δ} {x : E.Ob[ Γ ]} {a : D.Ob[ Γ Q.⨾ x ]} {b : D.Ob[ Δ ]}
        → {σ : Hom (Γ P.⨾ ∐ x a) Δ} {ν : Hom (Γ Q.⨾ x P.⨾ a) (Δ P.⨾ b)}
        → (p : σ ∘ (Q.πᶜ P.⨾ˢ ⟨ x , a ⟩) ≡ P.πᶜ ∘ ν)
        → (other : Hom (Γ P.⨾ ∐ x a) (Δ P.⨾ b))
        → other ∘ (Q.πᶜ P.⨾ˢ ⟨ x , a ⟩) ≡ ν
        → P.πᶜ ∘ other ≡ σ
        → other ≡ ∐-strong-elim σ ν p

  to-strong-comprehension-coproducts
    : make-strong-comprehension-coproducts
    → strong-comprehension-coproducts
  to-strong-comprehension-coproducts mk x a b {u = u} {v = v} p =
    contr (∐-strong-elim _ _ p , ∐-strong-β p , ∐-strong-sub p) λ w →
       Σ-prop-path (λ _ → ×-is-hlevel 1 (Hom-set _ _ _ _) (Hom-set _ _ _ _)) $
       sym (∐-strong-η p (w .fst) (w .snd .fst) (w .snd .snd))
    where open make-strong-comprehension-coproducts mk
```
-->

This definition is a bit dense, so let's unpack things a bit.

<!--
```agda
module strong-comprehension-coproducts
  {ob ℓb od ℓd oe ℓe} {B : Precategory ob ℓb}
  {D : Displayed B od ℓd} {E : Displayed B oe ℓe}
  {D-fib : Cartesian-fibration D} {E-fib : Cartesian-fibration E}
  (P : Comprehension D) {Q : Comprehension E}
  (coprods : has-comprehension-coproducts D-fib E-fib Q)
  (strong : strong-comprehension-coproducts P coprods)
  where
  private
    open Cat.Reasoning B
    module E = Displayed E
    module D = Displayed D
    module P = Comprehension D D-fib P
    module Q = Comprehension E E-fib Q
    open has-comprehension-coproducts coprods
```
-->

The filler for the diagram gives us our elimination principle; note
that we have access to the coproduct when forming the $B$! However,
this elimination principle does **not** allow us to eliminate into
anything from $\cE$; in type theoretic terms, we have an elimination
principle, but no $\cE$-large elimination. This corresponds to
[very strong coproducts], which are extremely rare.

[very strong coproducts]: Cat.Displayed.Comprehension.Coproduct.VeryStrong.html

```agda
  opaque
    ∐-strong-elim
      : ∀ {Γ Δ} {x : E.Ob[ Γ ]} {a : D.Ob[ Γ Q.⨾ x ]} {b : D.Ob[ Δ ]}
      → (σ : Hom (Γ P.⨾ ∐ x a) Δ) (ν : Hom (Γ Q.⨾ x P.⨾ a) (Δ P.⨾ b))
      → σ ∘ (Q.πᶜ P.⨾ˢ ⟨ x , a ⟩) ≡ P.πᶜ ∘ ν
      → Hom (Γ P.⨾ ∐ x a) (Δ P.⨾ b)
    ∐-strong-elim {x = x} {a = a} {b = b} σ ν p =
      strong x a b p .centre .fst
```

The upper-left triangle of the diagram gives us our $\beta$ law;
eliminating out of a substitution extended with an introduction form
gives us the original substitution.

```agda
  opaque
    unfolding ∐-strong-elim
    ∐-strong-β
      : ∀ {Γ Δ} {x : E.Ob[ Γ ]} {a : D.Ob[ Γ Q.⨾ x ]} {b : D.Ob[ Δ ]}
      → {σ : Hom (Γ P.⨾ ∐ x a) Δ} {ν : Hom (Γ Q.⨾ x P.⨾ a) (Δ P.⨾ b)}
      → (p : σ ∘ (Q.πᶜ P.⨾ˢ ⟨ x , a ⟩) ≡ P.πᶜ ∘ ν)
      → ∐-strong-elim σ ν p ∘ (Q.πᶜ P.⨾ˢ ⟨ x , a ⟩) ≡ ν
    ∐-strong-β p = strong _ _ _ p .centre .snd .fst
```

The lower-right triangle describes how substitution interacts with
eliminators; if we forget the thing we just eliminated into, then
we recover the substitution from $\Gamma, \coprod X A \to \Delta$.

```agda
    ∐-strong-sub
      : ∀ {Γ Δ} {x : E.Ob[ Γ ]} {a : D.Ob[ Γ Q.⨾ x ]} {b : D.Ob[ Δ ]}
      → {σ : Hom (Γ P.⨾ ∐ x a) Δ} {ν : Hom (Γ Q.⨾ x P.⨾ a) (Δ P.⨾ b)}
      → (p : σ ∘ (Q.πᶜ P.⨾ˢ ⟨ x , a ⟩) ≡ P.πᶜ ∘ ν)
      → P.πᶜ ∘ ∐-strong-elim σ ν p ≡ σ
    ∐-strong-sub p = strong _ _ _ p .centre .snd .snd
```

Finally, uniqueness gives us an $\eta$; any other substitution that
walks like the eliminator and quacks like the eliminator is the
eliminator.

```agda
    ∐-strong-η
      : ∀ {Γ Δ} {x : E.Ob[ Γ ]} {a : D.Ob[ Γ Q.⨾ x ]} {b : D.Ob[ Δ ]}
      → {σ : Hom (Γ P.⨾ ∐ x a) Δ} {ν : Hom (Γ Q.⨾ x P.⨾ a) (Δ P.⨾ b)}
      → (p : σ ∘ (Q.πᶜ P.⨾ˢ ⟨ x , a ⟩) ≡ P.πᶜ ∘ ν)
      → (other : Hom (Γ P.⨾ ∐ x a) (Δ P.⨾ b))
      → other ∘ (Q.πᶜ P.⨾ˢ ⟨ x , a ⟩) ≡ ν
      → P.πᶜ ∘ other ≡ σ
      → other ≡ ∐-strong-elim σ ν p
    ∐-strong-η p other β sub =
      ap fst (sym $ strong _ _ _ p .paths (other , β , sub)) 
```

Now, for some useful lemmas. If we eliminate by simply packaging up
the data into a pair, then we've done nothing. Categorically, this
means the unique filler of the following diagram is the identity
morphism.

~~~{.quiver}
\begin{tikzcd}
  {\Gamma,_{\cE}X,_{\cD}A} && {\Gamma,_{\cD}\coprod X A} \\
  \\
  {\Gamma,_{\cD}\coprod X A} && \Gamma
  \arrow["{\pi_{\cE},\langle X, A\rangle}"', from=1-1, to=3-1]
  \arrow["{\pi_{\cD}}", from=1-3, to=3-3]
  \arrow["{\pi_{\cD}}"', from=3-1, to=3-3]
  \arrow["{\pi_{\cE},\langle X, A\rangle}", from=1-1, to=1-3]
  \arrow["id", from=3-1, to=1-3]
\end{tikzcd}
~~~

```agda
    ∐-strong-id
      : ∀ {Γ} {x : E.Ob[ Γ ]} {a : D.Ob[ Γ Q.⨾ x ]}
      → ∐-strong-elim P.πᶜ (Q.πᶜ P.⨾ˢ ⟨ x , a ⟩) refl ≡ id
    ∐-strong-id = sym (∐-strong-η refl id (idl _) (idr _))
```
