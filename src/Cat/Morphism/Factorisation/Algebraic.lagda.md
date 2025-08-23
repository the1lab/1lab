<!--
```agda
open import Cat.Displayed.Instances.Factorisations
open import Cat.Diagram.Comonad
open import Cat.Diagram.Monad
open import Cat.Prelude
```
-->

```agda
module Cat.Morphism.Factorisation.Algebraic where
```

# Algebraic weak factorisation systems

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} (F : Factorisation C) where
  open Factorisation F
```
-->

:::{.definition #left-weak-factorisation-structure}
A **left weak factorisation structure** on a [[functorial
factorisation]] $F$ is an extension of the [[left factor functor]] $(L,
\eps)$ into a [[comonad]] on $\Arr{\cC}$.
:::

```agda
  record Lwfs-on : Type (o ⊔ ℓ) where
    field
      L-δ       : L => L F∘ L
      L-comonad : is-comonad L-ε L-δ

    open is-comonad L-comonad public

    𝕃 : Comonad-on L
    𝕃 = record { has-is-comonad = L-comonad }
```

:::{.definition #right-weak-factorisation-structure}
A **right weak factorisation structure** on a [[functorial
factorisation]] $F$ is an extension of the [[right factor functor]] $(R,
\eta)$ into a [[monad]] on $\Arr{\cC}$.
:::

```agda
  record Rwfs-on : Type (o ⊔ ℓ) where
    field
      R-μ     : R F∘ R => R
      R-monad : is-monad R-η R-μ

    open is-monad R-monad public

    ℝ : Monad-on R
    ℝ = record { has-is-monad = R-monad }
```

:::{.definition #algebraic-weak-factorisation-system alias="awfs"}
An **algebraic weak factorisation system** on $\cC$ is a [[functorial
factorisation]] $F$ which is simultaneously equipped with [[left|left
weak factorisation structure]] and [[right weak factorisation
structures]].
:::

```agda
  record Awfs-on : Type (o ⊔ ℓ) where
    field
      awfsᴸ : Lwfs-on
      awfsᴿ : Rwfs-on

    open Lwfs-on awfsᴸ using (𝕃 ; ε ; δ ; δ-unitl ; δ-unitr ; δ-assoc ; module counit ; module comult) public
    open Rwfs-on awfsᴿ using (ℝ ; η ; μ ; μ-unitl ; μ-unitr ; μ-assoc ; module unit   ; module mult)   public
```
