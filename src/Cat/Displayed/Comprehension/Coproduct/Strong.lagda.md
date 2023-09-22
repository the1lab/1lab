<!--
```agda
open import Cat.Displayed.Comprehension.Coproduct
open import Cat.Displayed.Comprehension
open import Cat.Displayed.Cartesian
open import Cat.Morphism.Orthogonal
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Comprehension.Coproduct.Strong where
```

# Strong comprehension coproducts {defines="strong-comprehension-coproduct"}

Let $\cD$ and $\cE$ be a pair of [[comprehension categories]] over the
same base category $\cB$, such that $\cD$ has [[coproducts|comprehension
coproducts]] over $\cE$. Type theoretically, this (roughly) corresponds
to a type theory with a pair of syntactic categories (for instance,
types and kinds), along with mixed-mode $\Sigma$ types.

We can model this using coproducts over a comprehension category, but
the elimination principle we get from this setup is pretty weak: we
really only have a _recursion_ principle, not an _elimination_
principle. That has to be be captured through an extra condition.

We say that a comprehension category has **strong comprehension
coproducts** if (it has comprehension coproducts, and) the canonical
substitution $\pi_{\cE}, \langle x , a \rangle$ forms an [[orthogonal
factorisation system]] with the weakening maps $\pi_{\cD}$. In more
elementary terms, this means that any square diagram, as below, has a
*unique* diagonal filler.

~~~{.quiver}
\begin{tikzcd}
  {\Gamma,_{\cE}X,_{\cD}A} && {\Delta,_{\cD}B} \\
  \\
  {\Gamma,_{\cD}\coprod_X A} && \Delta
  \arrow["{\pi_{\cE},\langle X, A\rangle}"', from=1-1, to=3-1]
  \arrow["{\pi_{\cD}}", from=1-3, to=3-3]
  \arrow["\sigma"', from=3-1, to=3-3]
  \arrow["\nu", from=1-1, to=1-3]
  \arrow["{\exists!}", dashed, from=3-1, to=1-3]
\end{tikzcd}
~~~

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

That's a very concise definition: too concise. Let's dig a bit deeper.

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

In the diagram, $B$ is a type in some context $\Delta$, and we have a
substitution $\sigma : \Gamma , \coprod_X A \to \Delta$ --- but, for
intuition, we might as well zap $\sigma$ to the identity: $B$ is a type
in context $\Gamma, \coprod_X A$.
In this simplified setting, the top morphism $\nu : \Gamma, X, A \to
\Gamma, B$ must be entirely determined by a "term" $\Gamma, x : X, a : A
\vdash \nu : B\langle x, a \rangle$, for the outer square to commute.
Then, we see that the diagonal filler is exactly an elimination
principle: since it too commutes with weakening, it must be determined
by a "term" $\Gamma, v : \coprod_X A \vdash B(v)$!

However, note that this elimination principle does **not** allow us to
eliminate an arbitrary object from $\cE$, which corresponds
type-theoretically having _no_ $\cE$-large elimination. This large
elimination is captured by [[very strong comprehension coproducts]],
which are extremely rare.

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
