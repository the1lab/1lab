<!--
```agda
open import 1Lab.Reflection.HLevel

open import Cat.Functor.Adjoint
open import Cat.Prelude

open import Data.Partial.Total
open import Data.Partial.Base

open import Realisability.PCA.Trivial
open import Realisability.PCA

import 1Lab.Reflection as R

import Cat.Reasoning as Cat

import Realisability.Data.Bool
import Realisability.PCA.Sugar
import Realisability.Base

open R hiding (def ; absurd)
open Functor
open _=>_
open _⊣_
```
-->

```agda
module Cat.Instances.Assemblies where
```

<!--
```agda
private variable
  ℓ ℓ' ℓA : Level
  𝔸 : PCA ℓA
```
-->

# Assemblies over a PCA

When working over a [[partial combinatory algebra]] $\bA$, it's often
the case that we're interested in programs $\tt{p} : \bA$ as concrete
*implementations* of some mathematical datum $x : X$. For example, we
can implement the successor function on natural numbers to be
$$
\tt{suc} = \langle n \rangle \langle f \rangle \langle x \rangle\ f(nfx)
$$,
representing a numeral $n : \bN$ as a *Church numeral*, taking the
defining property of $\operatorname{suc} n$ to be that if we have some
iterable process $f : A \to A$ starting at $x : A$, then the
$(\operatorname{suc} n)$-th iteration is $f$ applied to the $n$th
iteration; But we could just as well implement
$$
\tt{suc} = \langle n \rangle\ \tt{pair}(\tt{false}, n)
$$
representing a numeral $n : \bN$ as a *Curry numeral*, a pair containing
the information of whether the number is zero and its predecessor (if
any). These implementations are extensionally identical, in that they
both denote the same actual natural number, but for a concrete pca $\bA$,
they might genuinely be different --- we could imagine measuring the
time complexity of the predecessor function, which is $O(1)$ for Curry
numbers and $O(n)$ for Church numbers. Therefore, if we are to
investigate the computational content of constructive mathematics, we
need a way to track the connection between the mathematical elements $x
: X$ and the programs $\tt{p} : \bA$ which denote them.

:::{.definition #assembly}
An **assembly** over a pca $\bA$ is a [[set]] $X$ equipped with a
[[propositional|proposition]] relation $\tt{p} \Vdash x$ between
[[values|values in a pca]] $\tt{p} : \bA$ and elements $x : X$; when
this holds, we say $\tt{p}$ **realises** $x$. Moreover, for every $x :
X$, we require that there be at least one $\tt{p}$ which realises it.
:::

::: warning
The construction of assemblies over $\bA$, and the category
$\thecat{Asm}(\bA)$, works regardless of *which* pca $\bA$ we choose ---
but we only get something *interesting* if $\bA$ is [[nontrivial|trivial
pca]]: the category $\thecat{Asm}(*)$ over the trivial pca is the
category $\Sets$.

Therefore, when making natural-language statements about
$\thecat{Asm}(\bA)$, we generally assume that $\bA$ is nontrivial. A
statement like "the category $\thecat{Asm}(\bA)$ is not
[[univalent|univalent category]]" should be read as saying "univalence
of $\thecat{Asm}(\bA)$ implies $\bA$ is trivial."
:::

A prototypical example is the assembly of booleans, `𝟚`{.Agda}, defined
[below](#the-assembly-of-booleans). Its set of elements is
`Bool`{.Agda}, and we fix realisers
$$
\begin{align*}
\left(\langle x \rangle \langle y \rangle\ x\right) \Vdash&\ \rm{true}\\
\left(\langle x \rangle \langle y \rangle\ y\right) \Vdash&\ \rm{false;}
\end{align*}
$$
see [[booleans in a pca]] for the details of the construction. This is not
the only possible choice: we could, for example, invert the realisers,
and say that the value `true`{.Agda} is implemented by the *program*
$\tt{false}$ (and vice-versa). This results in a genuinely different
assembly over `Bool`{.Agda}, though with the same denotational data.

```agda
record Assembly (𝔸 : PCA ℓA) ℓ : Type (lsuc ℓ ⊔ ℓA) where
  no-eta-equality
  field
    Ob         : Type ℓ
    has-is-set : is-set Ob
    realisers  : Ob → ℙ⁺ 𝔸
    realised   : ∀ x → ∃[ a ∈ ↯ ⌞ 𝔸 ⌟ ] (a ∈ realisers x)
```

<!--
```agda
  module _ {x : Ob} where open ℙ⁺ (realisers x) using (defined) public

open Assembly public

private variable
  X Y Z : Assembly 𝔸 ℓ

instance
  Underlying-Assembly : Underlying (Assembly 𝔸 ℓ)
  Underlying-Assembly = record { ⌞_⌟ = Assembly.Ob }

  hlevel-proj-asm : hlevel-projection (quote Assembly.Ob)
  hlevel-proj-asm .hlevel-projection.has-level = quote Assembly.has-is-set
  hlevel-proj-asm .hlevel-projection.get-level _ = pure (quoteTerm (suc (suc zero)))
  hlevel-proj-asm .hlevel-projection.get-argument (_ ∷ _ ∷ _ ∷ c v∷ []) = pure c
  hlevel-proj-asm .hlevel-projection.get-argument (_ ∷ c v∷ []) = pure c
  {-# CATCHALL #-}
  hlevel-proj-asm .hlevel-projection.get-argument _ = typeError []

module _ (X : Assembly 𝔸 ℓ) (a : ↯ ⌞ 𝔸 ⌟) (x : ⌞ X ⌟) where
  open Ω (X .realisers x .mem a) renaming (∣_∣ to [_]_⊩_) public

-- This module can't be parametrised so this display form can fire
-- (otherwise it gets closed over pattern variables that aren't solvable
-- from looking at the expression, like the level and the PCA):
{-# DISPLAY realisers X x .ℙ⁺.mem a = [ X ] a ⊩ x #-}

subst⊩
  : {𝔸 : PCA ℓA} (X : Assembly 𝔸 ℓ) {x : ⌞ X ⌟} {p q : ↯ ⌞ 𝔸 ⌟}
  → [ X ] p ⊩ x → q ≡ p → [ X ] q ⊩ x
subst⊩ X {x} hx p = subst (_∈ X .realisers x) (sym p) hx
```
-->

To understand the difference--- and similarity--- between the ordinary
assembly of booleans and the swapped booleans, we define a morphism of
assemblies $(X, \Vdash_X) \to (Y, \Vdash_Y)$ to be a function $f : X \to
Y$ satisfying the [[*property*|propositional truncation]] that there
exists a program $\tt{f} : \bA$ which sends realisers of $x : X$ to
realisers of $f(x) : Y$.

```agda
record Assembly-hom {𝔸 : PCA ℓA} (X : Assembly 𝔸 ℓ) (Y : Assembly 𝔸 ℓ') : Type (ℓA ⊔ ℓ ⊔ ℓ') where
  open Realisability.Base 𝔸 using ([_]_⊢_)

  field
    map     : ⌞ X ⌟ → ⌞ Y ⌟
    tracked : ∥ [ map ] X .realisers ⊢ Y .realisers ∥
```

Note the force of the propositional truncation in this definition: maps
of assemblies are identical *when they have the same underlying
function*, regardless of which programs potentially implement them.
Since we can not, for a general $\bA$, show that the programs
$\mathtt{f}$ and
$$
\langle a \rangle\ f\ a
$$
are identical, $\thecat{Asm}(\bA)$ would not be a category if the choice
of realiser mattered for identity of computable maps.

<!--
```agda
private unquoteDecl eqv = declare-record-iso eqv (quote Assembly-hom)

instance
  H-Level-Assembly-hom : ∀ {n} → H-Level (Assembly-hom X Y) (2 + n)
  H-Level-Assembly-hom = basic-instance 2 $ Iso→is-hlevel 2 eqv (hlevel 2)

  Extensional-Assembly-hom
    : ∀ {ℓr} ⦃ _ : Extensional (⌞ X ⌟ → ⌞ Y ⌟) ℓr ⦄
    → Extensional (Assembly-hom X Y) ℓr
  Extensional-Assembly-hom ⦃ e ⦄ = injection→extensional! (λ p → Iso.injective eqv (Σ-prop-path! p)) e

  Funlike-Assembly-hom : Funlike (Assembly-hom X Y) ⌞ X ⌟ λ _ → ⌞ Y ⌟
  Funlike-Assembly-hom = record { _·_ = Assembly-hom.map }

{-# DISPLAY Assembly-hom.map f x = f · x #-}

-- Helper record for constructing an assembly map when the realiser is
-- known/does not depend on other truncated data.

record make-assembly-hom {𝔸 : PCA ℓA} (X : Assembly 𝔸 ℓ) (Y : Assembly 𝔸 ℓ') : Type (ℓA ⊔ ℓ ⊔ ℓ') where
  open Realisability.PCA.Sugar 𝔸 using (_⋆_)
  field
    map      : ⌞ X ⌟ → ⌞ Y ⌟
    realiser : ↯⁺ 𝔸
    tracks   : {x : ⌞ X ⌟} {a : ↯ ⌞ 𝔸 ⌟} (ah : [ X ] a ⊩ x) → [ Y ] realiser ⋆ a ⊩ map x

open Assembly-hom public

to-assembly-hom
  : ∀ {𝔸 : PCA ℓA} {X : Assembly 𝔸 ℓ} {Y : Assembly 𝔸 ℓ'}
  → make-assembly-hom X Y
  → Assembly-hom X Y
{-# INLINE to-assembly-hom #-}

to-assembly-hom f = record { make-assembly-hom f using (map) ; tracked = inc record { make-assembly-hom f } }

module _ (𝔸 : PCA ℓA) where
  open Realisability.Base 𝔸
  open Realisability.PCA.Sugar 𝔸
  open Realisability.Data.Bool 𝔸

  open Assembly-hom
  open Precategory
```
-->

This consideration is necessary for assemblies and assembly morphisms to
be a category: in an arbitrary pca $\bA$, composition of programs need
not be unital or associative.

```agda
  Assemblies : ∀ ℓ → Precategory (lsuc ℓ ⊔ ℓA) (ℓA ⊔ ℓ)
  Assemblies ℓ .Ob      = Assembly 𝔸 ℓ
  Assemblies ℓ .Hom     = Assembly-hom
  Assemblies ℓ .Hom-set x y = hlevel 2
  Assemblies ℓ .id      = record where
    map x   = x
    tracked = inc id⊢
  Assemblies ℓ ._∘_ f g = record where
    map x   = f · (g · x)
    tracked = ⦇ f .tracked ∘⊢ g .tracked ⦈
  Assemblies ℓ .idr   f     = ext λ _ → refl
  Assemblies ℓ .idl   f     = ext λ _ → refl
  Assemblies ℓ .assoc f g h = ext λ _ → refl
```

::: warning
Unlike most other categories constructed on the 1Lab, the category of
assemblies is not [[univalent|univalent category]]; see [univalence of
categories of assemblies](Cat.Instances.Assemblies.Univalence.html).[^univalence]
:::

[^univalence]:
    This is essentially *because* of of assemblies such as `𝟚`{.Agda}
    and its "flipped" counterpart, described above. The identity map is
    a computable isomorphism between them, realised by the `` `not
    ``{.Agda} program, which does not extend to a path (unless $\bA$ is
    trivial).

However, these two assemblies *are* still identical in the type
`Assembly`{.Agda}, where we allow the identification between the sets to
be nontrivial --- their realisability relations are identical over the
`not`{.Agda} equivalence --- hence the comment above about these being
non-trivial assemblies "over bool".

<!--
```agda
  _ = not
  _ = `not
```
-->

## The assembly of booleans

The assembly of booleans, $\tt{2}$, is the simplest example of an
assembly which contains actual computability data. Its construction is
entirely straightforward:

```agda
  𝟚 : Assembly 𝔸 lzero
  𝟚 .Ob          = Bool
  𝟚 .has-is-set  = hlevel 2
  𝟚 .realisers true  = singleton⁺ `true
  𝟚 .realisers false = singleton⁺ `false
  𝟚 .realised  true  = inc (`true .fst , inc refl)
  𝟚 .realised  false = inc (`false .fst , inc refl)
```

We define the realisability relation as a function from `Bool`{.Agda},
by cases: the only option for realising the boolean `true`{.Agda} is
with the `` `true ``{.Agda} program, and similarly the `false`{.Agda}
boolean is realised by the `` `false ``{.Agda} program. Both elements
have those respective programs as their realisers.

## Indiscrete assemblies

However, the *assembly* of booleans is not the only assembly we can
construct on the *type* of booleans. As mentioned above, we could also
have inverted which program realises each boolean; but this is *still*
an assembly with nontrivial computability data. Now, we show that the
"ambient" world of sets and functions embeds [[fully faithful|fully
faithful functor]] into the category of assemblies over any pca $\bA$.

This is, perhaps, a bit surprising: maps of assemblies are computable by
definition, but arbitrary functions between sets need not be! The catch
is that, when equipping a set with the structure of an assembly, *we*
get to choose which programs compute each elements; and, above, we have
made a sensible choice. But we can always make an *adversarial* choice,
letting *every* program at all realise any element.

::: terminology
We denote the **indiscrete assembly** on a set $X$ as $\nabla X$,
following the literature. Note however that Bauer
[-@Bauer:Realisability] refers to these as *constant assemblies*, while
de Jong [-@deJong:Realisability] does not assign them a name but merely
singles them out as embedding classical logic in $\thecat{Asm}(\bA)$.
:::

```agda
  ∇ : ∀ {ℓ} (X : Type ℓ) ⦃ _ : H-Level X 2 ⦄ → Assembly 𝔸 ℓ
  ∇ X .Ob          = X
  ∇ X .has-is-set  = hlevel 2
  ∇ X .realisers x = record
    { mem     = def
    ; defined = λ x → x
    }
  ∇ X .realised x = inc (expr ⟨ x ⟩ x , abs↓ _ _)
```

The important thing to know about these is that any function of sets $X
\to Y$ extends to a computable map of assemblies $(X, \Vdash) \to \nabla
Y$ --- this is because the only requirement for $e \Vdash_{\nabla Y} f
x$ is that $e$ is defined, and assemblies are defined so that if $e
\Vdash_X x$ then $e$ is defined.

<details>
<summary>Following the general logic of [[adjoint functors]], this means
that $\nabla (-)$ is a functor $\Sets \to \thecat{Asm}(\bA)$, for any
$\bA$ at all --- and moreover that $\nabla$ is a [[right adjoint]] to
the functor $\Gamma : \thecat{Asm}(\bA) \to \Sets$ which projects the
underlying set of each assembly.</summary>

```agda
  Cofree : Functor (Sets ℓ) (Assemblies ℓ)
  Cofree .F₀ X = ∇ ⌞ X ⌟
  Cofree .F₁ f = to-assembly-hom record where
    map       = f
    realiser  = val ⟨ x ⟩ x
    tracks ha = subst ⌞_⌟ (sym (abs-β _ [] (_ , ha))) ha
  Cofree .F-id    = ext λ _ → refl
  Cofree .F-∘ f g = ext λ _ → refl

  Forget : Functor (Assemblies ℓ) (Sets ℓ)
  Forget .F₀ X    = el! ⌞ X ⌟
  Forget .F₁ f    = f ·_
  Forget .F-id    = refl
  Forget .F-∘ f g = refl

  Forget⊣∇ : Forget {ℓ} ⊣ Cofree
  Forget⊣∇ .unit .η X = to-assembly-hom record where
    map x     = x
    realiser  = val ⟨ x ⟩ x
    tracks ha = subst ⌞_⌟ (sym (abs-β _ [] (_ , X .defined ha))) (X .defined ha)

  Forget⊣∇ .unit .is-natural x y f = ext λ _ → refl
  Forget⊣∇ .counit .η X a = a
  Forget⊣∇ .counit .is-natural x y f = refl
  Forget⊣∇ .zig = refl
  Forget⊣∇ .zag = ext λ _ → refl
```

</details>

The indiscrete assemblies $\nabla X$ are generally poor as *domains* for
computable functions, since a realiser for $f : \nabla X \to (Y,
\Vdash)$ would have to choose realisers for $f(x)$ given no information
about $x$. Indeed, we can show that if there are non-constant maps
$\nabla \{0, 1\} \to \tt{2}$, then $\bA$ is [[trivial|trivial pca]].

```agda
  non-constant-nabla-map
    : (f : Assembly-hom (∇ Bool) 𝟚)
    → f · true ≠ f · false
    → is-trivial-pca 𝔸
  non-constant-nabla-map f x = case f .tracked of λ where
    record { realiser = (fp , f↓) ; tracks = t } →
      let
        a = t {true}  {`true .fst} (`true .snd)
        b = t {false} {`true .fst} (`true .snd)

        cases
          : ∀ b b' (x : ↯ ⌞ 𝔸 ⌟)
          → [ 𝟚 ] x ⊩ b → [ 𝟚 ] x ⊩ b'
          → b ≠ b' → `true .fst ≡ `false .fst
        cases = λ where
          true true   p → rec! λ rb rb' t≠t → absurd (t≠t refl)
          true false  p → rec! λ rb rb' _   → rb ∙ sym rb'
          false true  p → rec! λ rb rb' _   → rb' ∙ sym rb
          false false p → rec! λ rb rb' f≠f → absurd (f≠f refl)
      in cases (f · true) (f · false) _ a b x
```

<!--
```agda
module Asm {ℓA ℓ} {𝔸 : PCA ℓA} = Cat (Assemblies 𝔸 ℓ)
```
-->
