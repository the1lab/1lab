<!--
```agda
open import 1Lab.Classical
open import 1Lab.Prelude

open import Data.Fin.Indexed
open import Data.Power
open import Data.Bool
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

A logic has the **compactness** property when every set of formulas $\phi$
is [[satisfiable]] precisely when every [[finite]] subset is satisfiable.

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
subset-is-sat {Γ} ϕs = ∃[ ρ ∈ (Fin Γ → Bool) ] (∀ ϕ → ϕ ∈ ϕs → ⟦ ϕ ⟧ ρ ≡ true)

has-compactness : Type
has-compactness =
  ∀ {Γ}
  → (ϕs : Proposition Γ → Ω)
  → (∀ (ϕs' : Proposition Γ → Ω) → ϕs' ⊆ ϕs → Finite (∫ₚ ϕs') → subset-is-sat ϕs')
  → subset-is-sat ϕs
```

This property is quite powerful: in fact, it is *too* powerful, and implies
[[weak excluded middle]]! The following argument is due to [@Saving:2023].

```agda
compactness→wlem : has-compactness → WLEM
compactness→wlem compact P =
  ∥-∥-proj (disjoint-⊎-is-prop hlevel! hlevel! λ { (¬¬p , ¬p) → ¬¬p ¬p }) ∥¬¬P∨¬P∥ where
```

Let $P$ be an arbitrary proposition (in Agda), and let $x$ be an atom
of propositional logic. Consider the set of formulae
$\{ x \mid P \} \cup \{ \lnot x \mid \lnot P \}$.

```agda
  x : Proposition 1
  x = atom 0

  [x∣P] : Proposition 1 → Ω
  [x∣P] ϕ = elΩ ((x ≡ ϕ) × ∣ P ∣)

  [¬x∣¬P] : Proposition 1 → Ω
  [¬x∣¬P] ϕ = elΩ ((“¬” x ≡ ϕ) × (¬ ∣ P ∣))
```

There are 3 possible finite subsets of
$\{ x \mid P \} \cup \{ \lnot x \mid \lnot P \}$.

* $\emptyset$
* $\{ x \}$
* $\{ \lnot x \}$

All three of these are clearly satisfiable, but
"Unfortunately, proof assistants": convincing Agda that those are the only
3 possible subsets involves quite a work.

```agda
  finitely-consistent
    : (ϕs' : Proposition 1 → Ω)
    → ϕs' ⊆ ([x∣P] ∪ [¬x∣¬P])
    → Finite (∫ₚ ϕs')
    → subset-is-sat ϕs'
```

<details>
<summary>We shall spare the innocent reader the details.
</summary>

```agda
  finitely-consistent ϕs' sub (fin {zero} ∥enum∥) =
    pure $ (λ _ → true) , λ ϕ ϕ∈ϕs' → absurd (card-zero→empty ∥enum∥ (ϕ , ϕ∈ϕs'))
  finitely-consistent ϕs' sub (fin {suc zero} ∥enum∥) = □-tr do
    enum ← tr-□ ∥enum∥
    let module enum = Equiv enum
    let (ϕ , ϕ∈ϕs') = enum.from 0
    sub ϕ ϕ∈ϕs' <&> λ where
      (inl xp) →
        (λ _ → true) , λ ϕ' ϕ'∈ϕs' → out! do
          sub ϕ' ϕ'∈ϕs' >>= λ where
            (inl xp') → do
              (x=ϕ' , _) ← xp'
              pure (subst (λ e → ⟦ e ⟧ (λ _ → true) ≡ true) x=ϕ' refl)
            (inr ¬xp') → do
              (_ , p) ← xp
              (_ , ¬p) ← ¬xp'
              absurd (¬p p)
      (inr ¬xp) →
        (λ _ → false) , λ ϕ' ϕ'∈ϕs' → out! do
          sub ϕ' ϕ'∈ϕs' >>= λ where
            (inl xp') → do
              (_ , ¬p) ← ¬xp
              (_ , p) ← xp'
              absurd (¬p p)
            (inr ¬xp') → do
              (¬x=ϕ' , _) ← ¬xp'
              pure (subst (λ e → ⟦ e ⟧ (λ _ → false) ≡ true) ¬x=ϕ' refl)
  finitely-consistent ϕs' sub (fin {suc (suc n)} ∥enum∥) = 
    absurd (out! do
      enum ← tr-□ ∥enum∥
      let module enum = Equiv enum
      let (ϕ , ϕ∈ϕs') = enum.from 0
      let (ϕ' , ϕ'∈ϕs') = enum.from 1
      sub ϕ ϕ∈ϕs' >>= λ where
        (inl xp) → sub ϕ' ϕ'∈ϕs' >>= λ where
          (inl xp') → do
            (x=ϕ , _) ← xp
            (x=ϕ' , _) ← xp'
            absurd
              (fzero≠fsuc $
                sym (enum.ε 0)
                ∙ ap enum.to (Σ-prop-path! (sym x=ϕ ∙ x=ϕ'))
                ∙ enum.ε 1)
          (inr ¬xp') → do
            (_ , p) ← xp
            (_ , ¬p) ← ¬xp'
            absurd (¬p p)
        (inr ¬xp) → sub ϕ' ϕ'∈ϕs' >>= λ where
          (inl xp') → do
            (_ , ¬p) ← ¬xp
            (_ , p) ← xp'
            absurd (¬p p)
          (inr ¬xp') → do
            (x=ϕ , _) ← ¬xp
            (x=ϕ' , _) ← ¬xp'
            absurd
              (fzero≠fsuc $
                sym (enum.ε 0)
                ∙ ap enum.to (Σ-prop-path! (sym x=ϕ ∙ x=ϕ'))
                ∙ enum.ε 1))
```
</details>

Every finite subset of $\{ x \mid P \} \cup \{ \lnot x \mid \lnot P \}$
is satisfiable, so $\{ x \mid P \} \cup \{ \lnot x \mid \lnot P \}$ must
be satisfiable by compactness. If $x$ gets assigned to true, then
$\neg \neg P$ must hold.

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

Conversely, if $x$ gets assigned to false, then $\neg P$ must hold.

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

If we put this all together, then we get weak excluded middle!

```agda
  ∥¬¬P∨¬P∥ : ∥ ¬ (¬ ∣ P ∣) ⊎ ¬ ∣ P ∣ ∥
  ∥¬¬P∨¬P∥ = do
    (ρ , ρ-sat) ← compact ([x∣P] ∪ [¬x∣¬P]) finitely-consistent
    pure $
      Bool-elim (λ b → ρ 0 ≡ b → ¬ (¬ ∣ P ∣) ⊎ ¬ ∣ P ∣)
        (λ x-true → inl (x-true→¬¬P ρ ρ-sat x-true))
        (λ x-false → inr (x-false→¬P ρ ρ-sat x-false))
        (ρ 0) refl
```
