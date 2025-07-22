<!--
```agda
open import Cat.Instances.Graphs
open import Cat.Prelude

open import Data.Sum
```
-->

```agda
module Cat.Instances.Graphs.Box where
```

# The box product of graphs {defines="box-product"}

The **box product** of two [[graphs]] $G$ and $H$ is the graph with node
[[set]] $G \times H$, and, provided that there are edges $x_0 \to x_1$
(resp. $y_0 \to y_1$), edges of the form $(x, y_0) \to (x, y_1)$ and
$(x_0, y) \to (x_1, y)$.

<!--
```agda
open Graph

private variable
  o ℓ o' ℓ' : Level

module _ {o ℓ o' ℓ'} (G : Graph o ℓ) (H : Graph o' ℓ') where
  private variable
    g₀ g₁ : ⌞ G ⌟
    h₀ h₁ : ⌞ H ⌟
```
-->

We define the edges as an indexed inductive type. Note that the indices
corresponding to the graph we're including an edge from vary, but the
indices corresponding to the other graph remain fixed.

```agda
  data Box-edge : (g₀ g₁ : ⌞ G ⌟) (h₀ h₁ : ⌞ H ⌟) → Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
    inl : G .Edge g₀ g₁ → Box-edge g₀ g₁ h₀ h₀
    inr : H .Edge h₀ h₁ → Box-edge g₀ g₀ h₀ h₁
```

<details>
<summary>We can prove that this type is a set by showing that it is
equivalent to a sum, with a summand for each constructor, replacing the
usage of indexing by an [[inductive identity]].
</summary>

```agda
instance
  H-Level-Box-edge
    : ∀ {G : Graph o ℓ} {H : Graph o' ℓ'} {g₀ g₁ h₀ h₁ n}
    → H-Level (Box-edge G H g₀ g₁ h₀ h₁) (2 + n)
  H-Level-Box-edge {G = G} {H} {g₀ = g₀} {g₁} {h₀} {h₁} =
    basic-instance 2 $ retract→is-hlevel 2 from to coh (hlevel 2)
    where
    T : Type _
    T = (h₀ ≡ᵢ h₁ × G .Edge g₀ g₁) ⊎ (g₀ ≡ᵢ g₁ × H .Edge h₀ h₁)

    from : T → Box-edge G H g₀ g₁ h₀ h₁
    from (inl (reflᵢ , x)) = inl x
    from (inr (reflᵢ , x)) = inr x

    to : Box-edge G H g₀ g₁ h₀ h₁ → T
    to (inl x) = inl (reflᵢ , x)
    to (inr x) = inr (reflᵢ , x)

    coh : is-left-inverse from to
    coh (inl x) = refl
    coh (inr x) = refl
```

</details>

We note that because the `Box-edge`{.Agda} type has to "store" the
endpoint nodes of the paths being included, the edges of a box product
live in the least universe that contains both the edges *and* nodes of
the operand graphs.

```agda
Box-product
  : Graph o ℓ → Graph o' ℓ' → Graph (o ⊔ o') (o ⊔ ℓ ⊔ o' ⊔ ℓ')
Box-product G H .Node = ⌞ G ⌟ × ⌞ H ⌟
Box-product G H .Edge (g₀ , h₀) (g₁ , h₁) = Box-edge G H g₀ g₁ h₀ h₁
Box-product G H .Node-set = hlevel 2
Box-product G H .Edge-set = hlevel 2
```
