<!--
```agda
open import Cat.Instances.Product
open import Cat.Functor.Compose
open import Cat.Diagram.Monad
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Monads where
```

<!--
```agda
private variable
  o h : Level
open Precategory
open Functor
```
-->

# Categories of monads {defines="category-of-monads"}

The **category of monads** of a category $\cC$ consists of [[monads]]
on $\cC$ and natural transformations preserving the monadic structure.
In terms of the bicategory of [[monads in $\Cat$|monad in]], a morphism
in the 1-categorical version always has the identity functor as the
underlying 1-cell. That is, this 1-category of monads on is the
"2-fibre" of the displayed bicategory of monads in $\Cat$ over $\cC$.

<!--
```agda
module _ {C : Precategory o h} where
  private
    module C = Cat.Reasoning C

    Endo : Precategory (o ⊔ h) (o ⊔ h)
    Endo = Cat[ C , C ]
    module Endo = Cat.Reasoning Endo

    Endo-∘-functor : Functor (Endo ×ᶜ Endo) Endo
    Endo-∘-functor = F∘-functor
    module Endo-∘ = Functor Endo-∘-functor
```
-->

A monad homomorphism is a natural transformation $\nu$ preserving
the unit $\eta$ and the multiplication $\mu$. In other words, the
following two diagrams commute, where $\blacklozenge$ is the
[[horizontal composition|horizontal composition in cat]]:

~~~{.quiver}
\[\begin{tikzcd}
  {\id} && {\id} && {MM} && {NN} \\
  \\
  {M} && {N} && {M} && {N}
  \arrow["{\id}", from=1-1, to=1-3]
  \arrow["{\nu}"', from=3-1, to=3-3]
  \arrow["{\eta_M}"', from=1-1, to=3-1]
  \arrow["{\eta_N}", from=1-3, to=3-3]
  \arrow["{\nu\mathbin{\blacklozenge}\nu}", from=1-5, to=1-7]
  \arrow["{\nu}"', from=3-5, to=3-7]
  \arrow["{\mu_M}"', from=1-5, to=3-5]
  \arrow["{\mu_N}", from=1-7, to=3-7]
\end{tikzcd}\]
~~~

```agda
  record Monad-hom (M N : Monad C) : Type (o ⊔ h) where
    no-eta-equality
    module M = Monad M
    module N = Monad N
    field
      nat : M.M => N.M
    open _=>_ nat public
    field
      pres-unit : nat ∘nt M.unit ≡ N.unit
      pres-mult : nat ∘nt M.mult ≡ N.mult ∘nt (nat ◆ nat)
```

<!--
```agda
  module _ {M N : Monad C} where
    private
      module M = Monad M
      module N = Monad N

    Monad-hom-path
      : (ν ξ : Monad-hom M N)
      → ν .Monad-hom.nat ≡ ξ .Monad-hom.nat
      → ν ≡ ξ
    Monad-hom-path ν ξ p i .Monad-hom.nat = p i
    Monad-hom-path ν ξ p i .Monad-hom.pres-unit =
      is-prop→pathp
        (λ i → Nat-is-set (p i ∘nt M.unit) N.unit)
        (ν .Monad-hom.pres-unit)
        (ξ .Monad-hom.pres-unit)
        i
    Monad-hom-path ν ξ p i .Monad-hom.pres-mult =
      is-prop→pathp
        (λ i → Nat-is-set (p i ∘nt M.mult) (N.mult ∘nt (p i ◆ p i)))
        (ν .Monad-hom.pres-mult)
        (ξ .Monad-hom.pres-mult)
        i

    abstract instance
      H-Level-Monad-hom : ∀ {n} → H-Level (Monad-hom M N) (2 + n)
      H-Level-Monad-hom = basic-instance 2 $ Iso→is-hlevel 2 eqv (hlevel 2)
        where unquoteDecl eqv = declare-record-iso eqv (quote Monad-hom)

    instance
      Extensional-Monad-hom
        : ∀ {ℓ} ⦃ sa : Extensional (M.M => N.M) ℓ ⦄
        → Extensional (Monad-hom M N) ℓ
      Extensional-Monad-hom ⦃ sa ⦄ =
        injection→extensional!
          {f = Monad-hom.nat}
          (Monad-hom-path _ _) sa

      Funlike-Monad-hom
        : Funlike (Monad-hom M N) ⌞ C ⌟ (λ x → C .Hom (M.M # x) (N.M # x))
      Funlike-Monad-hom ._#_ = Monad-hom.η
```
-->

We have the identity and composition as expected.

```agda
  monad-hom-id : ∀ {M : Monad C} → Monad-hom M M
  monad-hom-id {M = _} .Monad-hom.nat       = idnt
  monad-hom-id {M = _} .Monad-hom.pres-unit = Endo.idl _
  monad-hom-id {M = M} .Monad-hom.pres-mult =
    let module M = Monad M in
    idnt ∘nt M.mult          ≡⟨ Endo.id-comm-sym ⟩
    M.mult ∘nt idnt          ≡˘⟨ ap (M.mult ∘nt_) Endo-∘.F-id ⟩
    M.mult ∘nt (idnt ◆ idnt) ∎

  monad-hom-∘
    : ∀ {M N O : Monad C}
    → Monad-hom N O
    → Monad-hom M N
    → Monad-hom M O
  monad-hom-∘ {M = M} {N} {O} ν ξ = mh where
    module M = Monad M
    module N = Monad N
    module O = Monad O
    module ν = Monad-hom ν
    module ξ = Monad-hom ξ

    mh : Monad-hom M O
    mh .Monad-hom.nat = ν.nat ∘nt ξ.nat
    mh .Monad-hom.pres-unit =
      (ν.nat ∘nt ξ.nat) ∘nt M.unit ≡˘⟨ Endo.assoc ν.nat ξ.nat M.unit ⟩
      ν.nat ∘nt (ξ.nat ∘nt M.unit) ≡⟨ ap (ν.nat ∘nt_) ξ.pres-unit ⟩
      ν.nat ∘nt N.unit             ≡⟨ ν.pres-unit ⟩
      O.unit                       ∎
    mh .Monad-hom.pres-mult =
      (ν.nat ∘nt ξ.nat) ∘nt M.mult                       ≡˘⟨ Endo.assoc ν.nat ξ.nat M.mult ⟩
      ν.nat ∘nt (ξ.nat ∘nt M.mult)                       ≡⟨ ap (ν.nat ∘nt_) ξ.pres-mult ⟩
      ν.nat ∘nt (N.mult ∘nt (ξ.nat ◆ ξ.nat))             ≡⟨ Endo.assoc ν.nat N.mult (ξ.nat ◆ ξ.nat) ⟩
      (ν.nat ∘nt N.mult) ∘nt (ξ.nat ◆ ξ.nat)             ≡⟨ ap (_∘nt (ξ.nat ◆ ξ.nat)) ν.pres-mult ⟩
      (O.mult ∘nt (ν.nat ◆ ν.nat)) ∘nt (ξ.nat ◆ ξ.nat)   ≡˘⟨ Endo.assoc O.mult (ν.nat ◆ ν.nat) (ξ.nat ◆ ξ.nat) ⟩
      O.mult ∘nt ((ν.nat ◆ ν.nat) ∘nt (ξ.nat ◆ ξ.nat))   ≡˘⟨ ap (O.mult ∘nt_) $ Endo-∘.F-∘ (ν.nat , ν.nat) (ξ.nat , ξ.nat) ⟩
      O.mult ∘nt ((ν.nat ∘nt ξ.nat) ◆ (ν.nat ∘nt ξ.nat)) ∎
```

Putting these together, we have the 1-category of monads.

```agda
Monads : ∀ (C : Precategory o h) → Precategory (o ⊔ h) (o ⊔ h)
Monads C .Ob          = Monad C
Monads C .Hom         = Monad-hom
Monads C .Hom-set _ _ = hlevel 2
Monads C .id          = monad-hom-id
Monads C ._∘_         = monad-hom-∘
Monads C .idr _       = ext λ _ → C .idr _
Monads C .idl _       = ext λ _ → C .idl _
Monads C .assoc _ _ _ = ext λ _ → C. assoc _ _ _
```
