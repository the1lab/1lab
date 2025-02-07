<!--
```agda
open import 1Lab.Classical
open import 1Lab.Prelude

open import Data.Fin.Indexed
open import Data.Power
open import Data.Bool
open import Data.Dec
open import Data.Fin
open import Data.Nat
open import Data.Sum

open import Logic.Propositional.Classical

open import Meta.Brackets
```
-->

```agda
module Logic.Propositional.Classical.Compactness where
```

# Compactness of classical propositional logic is a constructive taboo

The **compactness** property, for a logical system, says that we can
determine the [[satisfiability|satisfiable]] of a set $\Phi$ of formulae
--- no matter how big $\Phi$ is! --- by checking the truth of every one
of its [[*finite*]] subsets, $\Psi \sube \Phi$.

<!--
```agda
private variable
  ℓ : Level
  Γ Δ Θ : Nat
  ψ θ ζ : Ctx Γ
  P Q R : Proposition Γ
```
-->

```agda
subset-is-sat : ∀ {Γ} → (Proposition Γ → Ω) → Type _
subset-is-sat {Γ} ϕs =
  ∃[ ρ ∈ (Fin Γ → Bool) ]
  ((ϕ : Proposition Γ) → ϕ ∈ ϕs → ⟦ ϕ ⟧ ρ ≡ true)

has-compactness : Type
has-compactness =
  ∀ {Γ}
  → (ϕs : Proposition Γ → Ω)
  → (∀ (ϕs' : Proposition Γ → Ω) → ϕs' ⊆ ϕs → Finite (∫ₚ ϕs') → subset-is-sat ϕs')
  → subset-is-sat ϕs
```

Keep in mind that compactness is *not* immediate, even classically,
since the set $\Phi$ of formulae we are testing might be arbitrarily
sized --- it could be countably infinite, equinumerous with $\bR$, or
worse --- and so it does not necessarily satisfy any boundedness
principles that would allow us to "patch together" pieces of truth ---
or even carve out those pieces in the first place.

In fact, while compactness may sound like a natural statement, we will
show that this property is *too strong* to ask of classical
propositional logic, in our neutral meta-theory: if compactness holds,
then so does [[weak excluded middle]]. Here, we formalise an argument
due to [@Saving:2023].

```agda
compactness→wlem : has-compactness → WLEM
compactness→wlem compact P = ¬P∨¬¬P where
```

We fix an arbitrary proposition $P : \Omega$ _of Agda_, our meta-logic,
and an atom $x$ of our object logic. We will apply compactness to the
set

$$\{ x \mid P \} \cup \{ \lnot x \mid \lnot P \}\text{.}$$

of formulae.

```agda
  x : Proposition 1
  x = atom 0

  [x∣P] : Proposition 1 → Ω
  [x∣P] ϕ = elΩ ((x ≡ ϕ) × ∣ P ∣)

  [¬x∣¬P] : Proposition 1 → Ω
  [¬x∣¬P] ϕ = elΩ ((“¬” x ≡ ϕ) × (¬ ∣ P ∣))
```

Despite the previous examples of bad subset being extremely large, this
is actually quite tame! It only has three possible _finite_ subsets,
namely the empty set, $\{ x \}$, and $\{ \lnot x \}$, all of which are
easily seen to be satisfiable. However, showing this to a proof
assistant requires quite a bit of work in combinatorics, so the actual
formalisation is a slightly nightmarish case bash.

```agda
  finitely-consistent
    : (ϕs' : Proposition 1 → Ω)
    → ϕs' ⊆ ([x∣P] ∪ [¬x∣¬P])
    → Finite (∫ₚ ϕs')
    → subset-is-sat ϕs'
```

<details>
<summary>
We will set the `<details>`{.html} aside for the curious reader.
</summary>

```agda
  finitely-consistent ϕs' sub (fin {zero} ∥enum∥) =
    pure $ (λ _ → true) , λ ϕ ϕ∈ϕs' → absurd (card-zero→empty ∥enum∥ (ϕ , ϕ∈ϕs'))
  finitely-consistent ϕs' sub (fin {suc zero} ∥enum∥) = do
    enum ← ∥enum∥
    let module enum = Equiv enum
    let (ϕ , ϕ∈ϕs') = enum.from 0
    sub ϕ ϕ∈ϕs' <&> λ where
      (inl xp) →
        (λ _ → true) , λ ϕ' ϕ'∈ϕs' → ∥-∥-out! do
          sub ϕ' ϕ'∈ϕs' >>= λ where
            (inl xp') → □-tr do
              (x=ϕ' , _) ← xp'
              pure (subst (λ e → ⟦ e ⟧ (λ _ → true) ≡ true) x=ϕ' refl)
            (inr ¬xp') → □-tr do
              (_ , p) ← xp
              (_ , ¬p) ← ¬xp'
              absurd (¬p p)
      (inr ¬xp) →
        (λ _ → false) , λ ϕ' ϕ'∈ϕs' → ∥-∥-out! do
          sub ϕ' ϕ'∈ϕs' >>= λ where
            (inl xp') → □-tr do
              (_ , ¬p) ← ¬xp
              (_ , p) ← xp'
              absurd (¬p p)
            (inr ¬xp') → □-tr do
              (¬x=ϕ' , _) ← ¬xp'
              pure (subst (λ e → ⟦ e ⟧ (λ _ → false) ≡ true) ¬x=ϕ' refl)
  finitely-consistent ϕs' sub (fin {suc (suc n)} ∥enum∥) = do
    enum ← ∥enum∥
    let module enum = Equiv enum
    let (ϕ , ϕ∈ϕs') = enum.from 0
    let (ϕ' , ϕ'∈ϕs') = enum.from 1
    sub ϕ ϕ∈ϕs' >>= λ where
      (inl xp) → sub ϕ' ϕ'∈ϕs' >>= λ where
        (inl xp') → □-tr do
          (x=ϕ , _) ← xp
          (x=ϕ' , _) ← xp'
          absurd
            (fzero≠fsuc $
              sym (enum.ε 0)
              ∙ ap enum.to (Σ-prop-path! (sym x=ϕ ∙ x=ϕ'))
              ∙ enum.ε 1)
        (inr ¬xp') → □-tr do
          (_ , p) ← xp
          (_ , ¬p) ← ¬xp'
          absurd (¬p p)
      (inr ¬xp) → sub ϕ' ϕ'∈ϕs' >>= λ where
        (inl xp') → □-tr do
          (_ , ¬p) ← ¬xp
          (_ , p) ← xp'
          absurd (¬p p)
        (inr ¬xp') → □-tr do
          (x=ϕ , _) ← ¬xp
          (x=ϕ' , _) ← ¬xp'
          absurd
            (fzero≠fsuc $
              sym (enum.ε 0)
              ∙ ap enum.to (Σ-prop-path! (sym x=ϕ ∙ x=ϕ'))
              ∙ enum.ε 1)
```

</details>

By compactness, we must have a satisfying assignment for the set of
formulae

$$\{ x \mid P \} \cup \{ \lnot x \mid \lnot P \}\text{,}$$

which actually consists only of the boolean value assigned to the atom
$x$: something we can do case analysis on. If our compactness oracle
thinks that $x$ must be true, then it *can not have been the case that
$\lnot P$ holds*, since then we would have $x = \operatorname{false}$.
In other words, we have decided $\lnot \lnot P$.

```agda
  x-true→¬¬P
    : (ρ : Fin 1 → Bool)
    → (∀ ϕ → ϕ ∈ [x∣P] ∪ [¬x∣¬P] → sem-prop ϕ ρ ≡ true)
    → ⟦ x ⟧ ρ ≡ true
    → ¬ ¬ ∣ P ∣
  x-true→¬¬P ρ sat x-true ¬p =
    not-no-fixed $
    ⟦ x ⟧ ρ       ≡⟨ x-true ⟩
    true          ≡˘⟨ sat (“¬” x) (inc (inr (inc (refl , ¬p)))) ⟩
    not (⟦ x ⟧ ρ) ∎
```

Conversely, if $x$ was assigned false, then $\lnot P$ must not have
failed: but the triple negative $\lnot \lnot \lnot P$ can be reduced to
a single negative, even constructively.

```agda
  x-false→¬P
    : (ρ : Fin 1 → Bool)
    → (∀ ϕ → ϕ ∈ [x∣P] ∪ [¬x∣¬P] → sem-prop ϕ ρ ≡ true)
    → ⟦ x ⟧ ρ ≡ false
    → ¬ ∣ P ∣
  x-false→¬P ρ sat x-false p =
    not-no-fixed $
    ⟦ x ⟧ ρ       ≡⟨ sat x (inc (inl (inc (refl , p)))) ⟩
    true          ≡˘⟨ ap not x-false ⟩
    not (⟦ x ⟧ ρ) ∎
```

If we put this all together, then we can decide $\neg P$!

```agda
  ¬P∨¬¬P : Dec (¬ ∣ P ∣)
  ¬P∨¬¬P = ∥-∥-out! do
    (ρ , ρ-sat) ← compact ([x∣P] ∪ [¬x∣¬P]) finitely-consistent
    pure $
      Bool-elim (λ b → ρ 0 ≡ b → Dec (¬ ∣ P ∣))
        (λ x-true → no (x-true→¬¬P ρ ρ-sat x-true))
        (λ x-false → yes (x-false→¬P ρ ρ-sat x-false))
        (ρ 0) refl
```
