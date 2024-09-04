<!--
```agda
open import Algebra.Group.Semidirect
open import Algebra.Group.Cat.Base
open import Algebra.Group.Concrete
open import Algebra.Group.Action
open import Algebra.Prelude
open import Algebra.Group

open import Homotopy.Connectedness

open ConcreteGroup
open is-group-hom
open Groups
```
-->

```agda
module Algebra.Group.Concrete.Semidirect {ℓ} where
```

# Semidirect products of concrete groups {defines="semidirect-product-of-concrete-groups"}

The construction of the [[semidirect product]] for [[concrete groups]]
is quite natural: given a concrete group $G$ and an action $\varphi :
\B G \to \rm{ConcreteGroups}$ of $G$ on $H = \varphi(\point{G})$, we
simply define $\B(G \ltimes H)$ as the $\Sigma$-type

$$
\sum_{g : \B G} \B \varphi(g)
$$

pointed at $(\point{G}, \point{H})$.

<!--
```agda
module _ (G : ConcreteGroup ℓ) (φ : ⌞ B G ⌟ → ConcreteGroup ℓ) where
```
-->

```agda
  H : ConcreteGroup ℓ
  H = φ (pt G)

  Semidirect-concrete : ConcreteGroup ℓ
  Semidirect-concrete .B .fst = Σ ⌞ B G ⌟ λ g → ⌞ B (φ g) ⌟
  Semidirect-concrete .B .snd = pt G , pt H
```

That this is a connected groupoid follows from standard results.

```agda
  Semidirect-concrete .has-is-connected = is-connected→is-connected∙ $
    Σ-is-n-connected 2
      (is-connected∙→is-connected (G .has-is-connected))
      (λ a → is-connected∙→is-connected (φ a .has-is-connected))
  Semidirect-concrete .has-is-groupoid = Σ-is-hlevel 3
    (G .has-is-groupoid)
    (λ a → φ a .has-is-groupoid)
```

In order to relate this with the definition of [[semidirect products]]
for abstract groups, we show that the [[fundamental group]]
$\pi_1\B(G \ltimes H)$ is the semidirect product $\pi_1\B G \ltimes
\pi_1\B H$.

To that end, we start by defining the action of $\pi_1\B G$ on
$\pi_1\B H$ induced by $\varphi$.
Given a loop $p : \point{G} \equiv \point{G}$, we can apply the function
$x \mapsto \pi_1 \B \varphi(x)$ to it to get a loop $\pi_1 \B H \equiv
\pi_1 \B H$, which we then turn into an automorphism.

<!--
NOTE(annoying): these are *right* actions, because both π₁ and Aut use
the diagrammatic order; if they both used the classical order, we'd
get left actions and we'd have to use left semidirect products; if
they used different orders, the definition of `π₁-φ` would have to
involve a `sym` to align them up.
-->

```agda
  π₁-φ : Action (Groups ℓ) (π₁B G) (π₁B H)
  π₁-φ .hom p = path→iso (ap (π₁B ⊙ φ) p)
  π₁-φ .preserves .pres-⋆ p q =
    path→iso (ap (π₁B ⊙ φ) (p ∙ q))                          ≡⟨ ap path→iso (ap-∙ (π₁B ⊙ φ) p q) ⟩
    path→iso (ap (π₁B ⊙ φ) p ∙ ap (π₁B ⊙ φ) q)               ≡⟨ path→iso-∙ (Groups ℓ) _ _ ⟩
    path→iso (ap (π₁B ⊙ φ) p) ∙Iso path→iso (ap (π₁B ⊙ φ) q) ∎

  π₁BG⋉π₁BH : Group ℓ
  π₁BG⋉π₁BH = Semidirect-product (π₁B G) (π₁B H) π₁-φ

  private module ⋉ = Group-on (π₁BG⋉π₁BH .snd)
```

::: source
The following proof is adapted from Symmetry [-@Symmetry, §4.14].
:::

The first step is to construct an equivalence between the underlying
sets of $\pi_1\B(G \ltimes H)$ and $\pi_1\B G \ltimes \pi_1\B H$.
Since $\B(G \ltimes H)$ is a $\Sigma$-type, its loops consist of pairs
$(p : \point{G} \is \point{G}, q : \point{H} \is_p \point{H})$, where
the second component is a [[dependent path]] over $p$ in the total space
of $\varphi$. What we actually want is a pair of non-dependent loops,
so we need to "realign" the second component by transporting one of
its endpoints along $p$; we do this by generalising on the endpoints
and using [[path induction]].

Note that we have a type $A = \B G$, a type family $B(a) = \B\varphi(a)$,
and a function $f : (a : A) \to B(a)$ given by $a \mapsto \point{\varphi(a)}$.
The following constructions work in this general setting.

<!--
```agda
  module _ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} (f : (a : A) → B a) where
```
-->

```agda
    align
      : ∀ {a a' : A} (p : a ≡ a')
      → PathP (λ i → B (p i)) (f a) (f a') ≃ (f a' ≡ f a')
    align {a} =
      J (λ a' p → PathP (λ i → B (p i)) (f a) (f a') ≃ (f a' ≡ f a')) id≃

    align-refl
      : ∀ {a : A} (q : f a ≡ f a)
      → align (λ _ → a) # q ≡ q
    align-refl {a} = unext $
      J-refl (λ a' p → PathP (λ i → B (p i)) (f a) (f a') ≃ (f a' ≡ f a')) id≃

    Σ-align
      : ∀ {a a' : A}
      → ((a , f a) ≡ (a' , f a')) ≃ ((a ≡ a') × (f a' ≡ f a'))
    Σ-align = Iso→Equiv Σ-pathp-iso e⁻¹ ∙e Σ-ap-snd align
```

It remains to show that this equivalence is a [[group homomorphism]]
--- or rather a group*oid* homomorphism, since we've generalised the
endpoints.
First, note that we can describe the action of $\varphi$ on paths using
a kind of dependent [[conjugation]] operation.

```agda
    conjP : ∀ {a a' : A} → (p : a ≡ a') → f a ≡ f a → f a' ≡ f a'
    conjP {a} p = transport (λ i → f a ≡ f a → f (p i) ≡ f (p i)) λ q → q

    conjP-refl : ∀ {a : A} → (q : f a ≡ f a) → conjP refl q ≡ q
    conjP-refl {a} = unext $ transport-refl {A = f a ≡ f a → _} λ q → q
```

Thus we have a composition operation on pairs of paths that generalises
the multiplication in $\pi_1\B G \ltimes \pi_1\B H$.

```agda
    _∙⋉_
      : ∀ {a₀ a₁ a₂ : A}
      → (a₀ ≡ a₁) × (f a₁ ≡ f a₁)
      → (a₁ ≡ a₂) × (f a₂ ≡ f a₂)
      → (a₀ ≡ a₂) × (f a₂ ≡ f a₂)
    (p , q) ∙⋉ (p' , q') = p ∙ p' , conjP p' q ∙ q'
```

<details>
<summary>
We can then show that `Σ-align`{.Agda} preserves the group(oid)
operations by double path induction.

```agda
    Σ-align-∙
      : ∀ {a₀ a₁ a₂ : A}
      → (p  : (a₀ , f a₀) ≡ (a₁ , f a₁))
      → (p' : (a₁ , f a₁) ≡ (a₂ , f a₂))
      → Σ-align # (p ∙ p')
      ≡ Σ-align # p ∙⋉ Σ-align # p'
```
</summary>

```agda
    Σ-align-∙ {a₀} {a₁} {a₂} p p' = J₂
      (λ a₀ a₂ p⁻¹ p' →
        ∀ (q : PathP (λ i → B (p⁻¹ (~ i))) (f a₀) (f a₁))
        → (q' : PathP (λ i → B (p' i)) (f a₁) (f a₂))
        → Σ-align # ((sym p⁻¹ ,ₚ q) ∙ (p' ,ₚ q'))
        ≡ Σ-align # (sym p⁻¹ ,ₚ q) ∙⋉ Σ-align # (p' ,ₚ q'))
      (λ q q' →
        Σ-align # ((refl ,ₚ q) ∙ (refl ,ₚ q'))                      ≡˘⟨ ap# Σ-align (ap-∙ (a₁ ,_) q q') ⟩
        Σ-align # (refl ,ₚ q ∙ q')                                  ≡⟨⟩
        refl        , align refl # (q ∙ q')                         ≡⟨ refl ,ₚ align-refl (q ∙ q') ⟩
        refl        , q ∙ q'                                        ≡˘⟨ refl ,ₚ ap₂ _∙_ (align-refl q) (align-refl q') ⟩
        refl        , align refl # q ∙ align refl # q'              ≡˘⟨ ∙-idl _ ,ₚ ap (_∙ align refl # q') (conjP-refl (align refl # q)) ⟩
        refl ∙ refl , conjP refl (align refl # q) ∙ align refl # q' ∎)
      (ap fst (sym p)) (ap fst p') (ap snd p) (ap snd p')
```
</details>

This concludes the proof that the constructions of the semidirect
product of abstract and concrete groups agree over the equivalence
between abstract and concrete groups.

```agda
  Semidirect-concrete-abstract : π₁B Semidirect-concrete ≡ π₁BG⋉π₁BH
  Semidirect-concrete-abstract = ∫-Path
    (total-hom (Σ-align (pt ⊙ φ) .fst)
      (record { pres-⋆ = Σ-align-∙ (pt ⊙ φ) }))
    (Σ-align (pt ⊙ φ) .snd)
```
