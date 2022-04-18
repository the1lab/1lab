```agda
open import 1Lab.Prelude

open import Algebra.Group

open import Data.Set.Truncation

module Algebra.Group.Homotopy.BAut where
```

# Deloopings of automorphism groups

Recall that any set $X$ generates a group [$\id{Sym}(X)$][symg], given
by the automorphisms $X \simeq X$. We also have a generic construction
of [deloopings]: special spaces $K(G,1)$ (for a group $G$), where the
[fundamental group] $\pi_1(K(G,1))$ recovers $G$. For the specific case
of deloping automorphism groups, we can give an alternative
construction: The type of small types [merely] equivalent to $X$ has a
fundamental group of $\id{Sym}(X)$.

[symg]: Algebra.Group.html#symmetric-groups
[deloopings]: Algebra.Group.Homotopy.html#deloopings
[fundamental group]: Algebra.Group.Homotopy.html#homotopy-groups.
[merely]: 1Lab.HIT.Truncation.html

```agda
module _ {ℓ} (T : Type ℓ) where
  BAut : Type (lsuc ℓ)
  BAut = Σ[ B ∈ Type ℓ ] ∥ T ≃ B ∥

  base : BAut
  base = T , inc (id , id-equiv)
```

The first thing we note is that `BAut`{.Agda} is a _connected_ type,
meaning that it only has "a single point", or, more precisely, that all
of its interesting information is in its (higher) path spaces:

```agda
  connected : ∀ b → ∥ b ≡ base ∥
  connected (b , x) =
    ∥-∥-elim {P = λ x → ∥ (b , x) ≡ base ∥} (λ _ → squash) (λ e → inc (p _ _)) x
    where
      p : ∀ b e → (b , inc e) ≡ base
      p _ = EquivJ (λ B e → (B , inc e) ≡ base) refl
```

We now turn to proving that $\pi_1(\baut(X)) \simeq (X \simeq X)$. We
will define a type family $\id{Code}(b)$, where a value $p : \id{Code}(x)$
codes for an identification $p \equiv \id{base}$. Correspondingly, there
are functions to and from these types: The core of the proof is showing
that these functions, `encode`{.Agda} and `decode`{.Agda}, are inverses.

```agda
  Code : BAut → Type ℓ
  Code b = T ≃ b .fst

  encode : ∀ b → base ≡ b → Code b
  encode x p = path→equiv (ap fst p)

  decode : ∀ b → Code b → base ≡ b
  decode (b , eqv) rot = Σ-pathp (ua rot) (is-prop→pathp (λ _ → squash) _ _)
```

Recall that $\id{base}$ is the type $T$ itself, equipped with the
identity equivalence. Hence, to code for an identification $\id{base}
\equiv (X, e)$, it suffices to record $e$ --- which by univalence
corresponds to a path $\id{ua}(e) : T \equiv X$.  We can not directly
extract the equivalence from a given point $(X, e) : \baut(X)$: it is
"hidden away" under a truncation. But, given an identification $p : b
\equiv \id{base}$, we can recover the equivalence by seeing _how_ $p$
identifies $X \equiv T$.

```agda
  decode∘encode : ∀ b (p : base ≡ b) → decode b (encode b p) ≡ p
  decode∘encode b =
    J (λ b p → decode b (encode b p) ≡ p)
      (Σ-prop-square (λ _ → squash) sq)
    where
      sq : ua (encode base refl) ≡ refl
      sq = ap ua path→equiv-refl ∙ ua-id-equiv
```

`Encode`{.Agda ident=encode} and `decode`{.Agda} are inverses by a
direct application of `univalence`{.Agda}.

```agda
  encode∘decode : ∀ b (p : Code b) → encode b (decode b p) ≡ p
  encode∘decode b p = equiv→section univalence _
```

We now have the core result: Specialising `encode`{.Agda} and
`decode`{.Agda} to the `basepoint`{.Agda}, we conclude that loop space
$\id{base} \equiv \id{base}$ is equivalent to $\id{Sym}(X)$.

```agda
  Ω¹BAut : (base ≡ base) ≃ (T ≃ T)
  Ω¹BAut = Iso→Equiv
    (encode base , iso (decode base) (encode∘decode base) (decode∘encode base))
```
