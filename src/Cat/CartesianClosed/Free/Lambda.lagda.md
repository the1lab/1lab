<!--
```agda
open import Cat.CartesianClosed.Free.Signature
open import Cat.Prelude
```
-->

```agda
module Cat.CartesianClosed.Free.Lambda {ℓ} (S : Λ-Signature ℓ) where
```

<!--
```agda
open import Cat.CartesianClosed.Free S
open Λ-Signature S renaming (Ob to Node ; Hom to Edge)
private variable
  Γ Δ Θ : Cx
  τ σ ρ : Ty
```
-->

# Simply-typed lambda calculus {defines="simply-typed-lambda-calculus STLC"}

The **simply typed $\lambda$-calculus** (STLC) is a very small typed
programming language very strongly associated with [[Cartesian closed
categories]]. In this module, we define the syntax for STLC over a
[[$\Lambda$-signature]] $\Sigma$, and show how it relates to the
syntax of the [[free Cartesian closed category]] over $\Sigma$.

We have already defined most of the pieces we need in the construction
of normalisation by evaluation for [[free Cartesian closed categories]].
What remains is to define $\lambda$-*expressions*:

```agda
data Expr (Γ : Cx) : Ty → Type ℓ where
  `var    : Var Γ τ             → Expr Γ τ
  `π₁     : Expr Γ (τ `× σ)     → Expr Γ τ
  `π₂     : Expr Γ (τ `× σ)     → Expr Γ σ
  `⟨_,_⟩  : Expr Γ τ → Expr Γ σ → Expr Γ (τ `× σ)
  `λ      : Expr (Γ , τ) σ      → Expr Γ (τ `⇒ σ)
  `$      : Expr Γ (τ `⇒ σ)     → Expr Γ τ → Expr Γ σ
  `unit   : Expr Γ `⊤
  `hom    : ∀ {x y} → Edge x y → Expr Γ x → Expr Γ (` y)
```

These expressions have a straightforward interpretation as morphisms in
$\Syn_\Sigma$, after interpreting contexts as objects:

```agda
⟦_⟧ᵉ : Expr Γ τ → Mor ⟦ Γ ⟧ᶜ τ
⟦ `var x ⟧ᵉ = ⟦ x ⟧ⁿ
⟦ `π₁ e ⟧ᵉ = `π₁ `∘ ⟦ e ⟧ᵉ
⟦ `π₂ e ⟧ᵉ = `π₂ `∘ ⟦ e ⟧ᵉ
⟦ `⟨ e , f ⟩ ⟧ᵉ = ⟦ e ⟧ᵉ `, ⟦ f ⟧ᵉ
⟦ `λ e ⟧ᵉ = `ƛ ⟦ e ⟧ᵉ
⟦ `$ e f ⟧ᵉ = `ev `∘ (⟦ e ⟧ᵉ `, ⟦ f ⟧ᵉ)
⟦ `unit ⟧ᵉ = `!
⟦ `hom x e ⟧ᵉ = (` x) `∘ ⟦ e ⟧ᵉ
```

Furthermore, neutrals and normals embed into expressions in a way that
preserves their semantics, in the sense of the following commuting
triangle:

~~~{.quiver}
\[\begin{tikzcd}
  {\mathrm{Nf}\,\Gamma\,\tau} && {\mathrm{Expr}\,\Gamma\,\tau} \\
  \\
  & {\mathrm{Mor}\,\sem{\Gamma}\,\tau}
  \arrow[from=1-1, to=1-3]
  \arrow[from=1-1, to=3-2]
  \arrow[from=1-3, to=3-2]
\end{tikzcd}\]
~~~

```agda
nf→expr : Nf Γ τ → Expr Γ τ
ne→expr : Ne Γ τ → Expr Γ τ

nf→expr (lam n) = `λ (nf→expr n)
nf→expr (pair n n₁) = `⟨ nf→expr n , nf→expr n₁ ⟩
nf→expr unit = `unit
nf→expr (ne x) = ne→expr x

ne→expr (var x) = `var x
ne→expr (app n x) = `$ (ne→expr n) (nf→expr x)
ne→expr (hom x x₁) = `hom x (nf→expr x₁)
ne→expr (fstₙ n) = `π₁ (ne→expr n)
ne→expr (sndₙ n) = `π₂ (ne→expr n)

nf-⟦⟧ᵉ : (n : Nf Γ τ) → ⟦ n ⟧ₙ ≡ ⟦ nf→expr n ⟧ᵉ
ne-⟦⟧ᵉ : (n : Ne Γ τ) → ⟦ n ⟧ₛ ≡ ⟦ ne→expr n ⟧ᵉ

nf-⟦⟧ᵉ (lam n) = ap `ƛ (nf-⟦⟧ᵉ n)
nf-⟦⟧ᵉ (pair n m) = ap₂ _`,_ (nf-⟦⟧ᵉ n) (nf-⟦⟧ᵉ m)
nf-⟦⟧ᵉ unit = refl
nf-⟦⟧ᵉ (ne x) = ne-⟦⟧ᵉ x

ne-⟦⟧ᵉ (var x) = refl
ne-⟦⟧ᵉ (app n x) = ap₂ (λ x y → `ev `∘ (x `, y)) (ne-⟦⟧ᵉ n) (nf-⟦⟧ᵉ x)
ne-⟦⟧ᵉ (hom x n) = ap ((` x) `∘_) (nf-⟦⟧ᵉ n)
ne-⟦⟧ᵉ (fstₙ n) = ap (`π₁ `∘_) (ne-⟦⟧ᵉ n)
ne-⟦⟧ᵉ (sndₙ n) = ap (`π₂ `∘_) (ne-⟦⟧ᵉ n)
```

The map $\rm{Nf}\,\Gamma\,\tau \to \rm{Mor}\,\sem{\Gamma}\,\tau$ is an
isomorphism by normalisation; this exhibits `Mor`{.Agda} (hence
`Nf`{.Agda}) as a [[split quotient]] (in other words, a [[retract]]) of
`Expr`{.Agda}.

```agda
nfᵉ : Expr Γ τ → Nf Γ τ
nfᵉ e = nfᶜ _ ⟦ e ⟧ᵉ .fst

Nf-is-retract : is-left-inverse (nfᵉ {Γ} {τ}) nf→expr
Nf-is-retract n = Equiv.adjunctr nf≃ (sym (nf-⟦⟧ᵉ n))
```

## Substitutions

We define substitutions; the action of renamings on expressions and
substitutions; the action of substitutions on expressions; and
composition of substitutions.

```agda
data Subᵉ (Γ : Cx) : Cx → Type ℓ where
  ∅   : Subᵉ Γ ∅
  _,_ : Subᵉ Γ Δ → Expr Γ τ → Subᵉ Γ (Δ , τ)

ren-expr : ∀ {Γ Δ τ} → Ren Γ Δ → Expr Δ τ → Expr Γ τ
ren-subᵉ : ∀ {Γ Δ Θ} → Ren Δ Γ → Subᵉ Γ Θ → Subᵉ Δ Θ

ren-expr ρ (`var x) = `var (ren-var ρ x)
ren-expr ρ (`π₁ e) = `π₁ (ren-expr ρ e)
ren-expr ρ (`π₂ e) = `π₂ (ren-expr ρ e)
ren-expr ρ `⟨ e , e₁ ⟩ = `⟨ ren-expr ρ e , ren-expr ρ e₁ ⟩
ren-expr ρ (`λ e) = `λ (ren-expr (keep ρ) e)
ren-expr ρ (`$ e e₁) = `$ (ren-expr ρ e) (ren-expr ρ e₁)
ren-expr ρ `unit = `unit
ren-expr ρ (`hom x s) = `hom x (ren-expr ρ s)

ren-subᵉ ρ ∅       = ∅
ren-subᵉ ρ (s , x) = ren-subᵉ ρ s , ren-expr ρ x

sub-var : Subᵉ Δ Γ → Var Γ τ → Expr Δ τ
sub-var (s , x) stop = x
sub-var (s , x) (pop v) = sub-var s v

sub-drop : Subᵉ Δ Γ → Subᵉ (Δ , τ) Γ
sub-drop ∅       = ∅
sub-drop (s , x) = sub-drop s , ren-expr (drop stop) x

sub-keep : Subᵉ Δ Γ → Subᵉ (Δ , τ) (Γ , τ)
sub-keep s = sub-drop s , `var stop

sub-stop : Subᵉ Γ Γ
sub-stop {∅}     = ∅
sub-stop {Γ , x} = sub-keep sub-stop

sub-expr : Subᵉ Δ Γ → Expr Γ τ → Expr Δ τ
∘-sub    : Subᵉ Γ Θ → Subᵉ Δ Γ → Subᵉ Δ Θ

∘-sub ∅ r = ∅
∘-sub (s , x) r = ∘-sub s r , sub-expr r x

sub-expr s (`var x) = sub-var s x
sub-expr s (`π₁ e) = `π₁ (sub-expr s e)
sub-expr s (`π₂ e) = `π₂ (sub-expr s e)
sub-expr s `⟨ e , e₁ ⟩ = `⟨ sub-expr s e , sub-expr s e₁ ⟩
sub-expr s (`λ e) = `λ (sub-expr (sub-keep s) e)
sub-expr s (`$ e e₁) = `$ (sub-expr s e) (sub-expr s e₁)
sub-expr s `unit = `unit
sub-expr s (`hom x s') = `hom x (sub-expr s s')
```
