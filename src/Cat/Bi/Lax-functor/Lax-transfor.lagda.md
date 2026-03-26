<!--
```agda
open import Cat.Functor.Coherence hiding (_◆_)
open import Cat.Functor.Base
open import Cat.Bi.Solver
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Bi.Reasoning as Br
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Bi.Lax-functor.Lax-transfor
  {o h l o' h' l'} {B : Prebicategory o h l} {C : Prebicategory o' h' l'}
  where
```

<!--
```agda
private
  module B  = Prebicategory B
  module C  = Br C
  module CH = C.Hom

open Prebicategory C
open Pseudonatural
open Lax-transfor
open Cr.Inverses
open Cr._≅_
open _=>_

module _ {F : Lax-functor B C} where
```
-->

# Identity and composition for lax and pseudonatural transformations

In the same way that [[natural transformations]] between [[functors]]
can be [composed], so can [[lax transformations]] and pseudonatural
transformations between [[lax functors]] in the setting of
[[bicategories]].

[composed]: Cat.Functor.Base.html

The identity lax transformation is given by identities componentwise as
one might expect.  Since this is a lax transformation, we have to show
that "directed" naturality holds by providing a natural transformation
$F_1(f)\id \To \id G_1(f)$.  In a category, this would be a case of
removing the identity on one side and introducing it on the other; in a
bicategory this takes the form of using the unitors $\rho$ and $\lambda$
in succession.

```agda
  idlx : F =>ₗ F
  idlx .σ a       = id
  idlx .naturator = (unitor-l .to ∘nt unitor-r .from) ◂ _
```

Luckily, the compatibility equations with respect to $F$'s unitor and
compositor boil down to an equality of pure coherence 2-cells, which our
[bicategory solver] can handle.

[bicategory solver]: Cat.Bi.Solver.html

```agda
  idlx .ν-compositor f g = bicat! C
  idlx .ν-unitor         = bicat! C
```

This construction also gives rise to a pseudonatural transformation,
since all the components are invertible.

```agda
  idpx : F =>ₚ F
  idpx .lax             = idlx
  idpx .naturator-inv f = CH.invertible-∘ (CH.inverses→invertible (C.λ≅ .inverses))
    (CH.is-invertible.op (CH.inverses→invertible (C.ρ≅ .inverses)))
```

<!--
```agda
module _ {F G H : Lax-functor B C} where
  private
    module F = Lax-functor F
    module G = Lax-functor G
    module H = Lax-functor H
```
-->

To compose two lax transformations $\alpha : G \To H$ and $\beta : F \To
G$, we take their componentwise composition.  We must give a naturator
of type $H_1(f) (\alpha_a \beta_a) \To (\alpha_b \beta_b) F_1(f)$.
Just like when proving naturality for the composition of natural
transformations, this amounts to first applying the naturator of
$\alpha$ to turn $H_1(f)\alpha_a$ into $\alpha_b G_1(f)$, and then the
naturator of $\beta$ to turn $G_1(f) \beta_a$ into $\beta_b F_1(f)$.
However, since we are working in a bicategory, associativity holds only
up to isomorphism, and we must insert explicit applications of the
associator between each step.

```agda
  _∘lx_ : G =>ₗ H → F =>ₗ G → F =>ₗ H
  _∘lx_ α β = lx module ∘lx where
```

<!--
```agda
    private
      module α = Lax-transfor α
      module β = Lax-transfor β
```
-->

```agda
    ν : ∀ {a b} → preaction C (α.σ b ⊗ β.σ b) F∘ H.P₁ => postaction C (α.σ a ⊗ β.σ a) F∘ F.P₁
    ν {a} {b} =
      (C.▶-assoc .from ◂ F.P₁) ∘nt
      nat-assoc-to (postaction C (α.σ a) ▸ β.naturator) ∘nt
      (nat-unassoc-to ⊙ nat-unassoc-from) (C.◀-▶-comm .to ◂ G.P₁) ∘nt
      nat-assoc-from (preaction C (β.σ b) ▸ α.naturator) ∘nt
      (C.◀-assoc .to ◂ H.P₁)
```

Here, `▶-assoc`{.Agda}, `◀-▶-comm`{.Agda}, and `◀-assoc`{.Agda} are all
repackagings of the associator.

<!--
```agda
    lx : _ =>ₗ _
```
-->

```agda
    lx .σ x       = α.σ x ⊗ β.σ x
    lx .naturator = ν
```

Because our naturator involves three occurrences of the associator, the
coherence diagram with respect to the compositors of $F$ and $H$ is
truly nightmarish.  Fortunately, our bicategory solver can handle most
of the heavy lifting, and all we need to do is recognize the
opportunities to apply the coherence data from $\alpha$ and $\beta$ in
sequence.

```agda
    lx .ν-compositor {a = a} {b} {c} f g =
      ν .η (f B.⊗ g) ∘ H.γ→ _ ◀ (α.σ a ⊗ β.σ a)
        ≡⟨ bicat! C ⟩
        α← _ ∘ α.σ c ▶ β.ν→ (f B.⊗ g) ∘ α→ _
      ∘ ⌜ α.ν→ (f B.⊗ g) ∘ H.γ→ _ ◀ α.σ a ⌝ ◀ β.σ a ∘ α← _
        ≡⟨ ap! (α.ν-compositor f g) ⟩
        α← _ ∘ α.σ c ▶ β.ν→ (f B.⊗ g) ∘ α→ _ ∘ (α.σ c ▶ G.γ→ _ ∘ α→ _
      ∘ α.ν→ f ◀ G.₁ g ∘ α← _ ∘ H.₁ f ▶ α.ν→ g ∘ α→ _) ◀ β.σ a ∘ α← _
        ≡⟨ bicat! C ⟩
        α← _ ∘ α.σ c ▶ ⌜ β.ν→ (f B.⊗ g) ∘ G.γ→ _ ◀ β.σ a ⌝ ∘ α→ _ ∘ α→ _ ◀ β.σ a
      ∘ (α.ν→ f ◀ G.₁ g) ◀ β.σ a ∘ α← _ ◀ β.σ a ∘ (H.₁ f ▶ α.ν→ g) ◀ β.σ a
      ∘ α→ _ ◀ β.σ a ∘ α← _
        ≡⟨ ap! (β.ν-compositor f g) ⟩
      α← _ ∘ α.σ c ▶ (β.σ c ▶ F.γ→ _ ∘ α→ _ ∘ β.ν→ f ◀ F.₁ g ∘ α← _ ∘ G.₁ f ▶ β.ν→ g ∘ α→ _)
      ∘ α→ _ ∘ α→ _ ◀ β.σ a ∘ (α.ν→ f ◀ G.₁ g) ◀ β.σ a ∘ α← _ ◀ β.σ a
      ∘ (H.₁ f ▶ α.ν→ g) ◀ β.σ a ∘ α→ _ ◀ β.σ a ∘ α← _
        ≡⟨ bicat! C ⟩
      (α.σ c ⊗ β.σ c) ▶ F.γ→ _ ∘ α→ _ ∘ ν .η f ◀ F.₁ g ∘ α← _ ∘ H.₁ f ▶ ν .η g ∘ α→ _
        ∎
```

<details>
<summary>
We elide the proof showing compatibility with the unitors, which is
similar in spirit.
</summary>
```agda
    lx .ν-unitor {a} =
      ν .η B.id ∘ H.υ→ ◀ _
        ≡⟨ bicat! C ⟩
      α← _ ∘ α.σ a ▶ β.ν→ _ ∘ α→ _ ∘ ⌜ α.ν→ _ ∘ H.υ→ ◀ α.σ a ⌝ ◀ β.σ a ∘ α← _
        ≡⟨ ap! α.ν-unitor ⟩
      α← _ ∘ α.σ a ▶ β.ν→ _ ∘ α→ _ ∘ (α.σ a ▶ G.υ→ ∘ ρ→ _ ∘ λ← _) ◀ β.σ a ∘ α← _
        ≡⟨ bicat! C ⟩
      α← _ ∘ α.σ a ▶ ⌜ β.ν→ _ ∘ G.υ→ ◀ β.σ a ⌝ ∘ α→ _ ∘ ρ→ _ ◀ β.σ a ∘ λ← _ ◀ β.σ a ∘ α← _
        ≡⟨ ap! β.ν-unitor ⟩
      α← _ ∘ α.σ a ▶ (β.σ a ▶ F.υ→ ∘ ρ→ _ ∘ λ← _) ∘ α→ _ ∘ ρ→ _ ◀ β.σ a ∘ λ← _ ◀ β.σ a ∘ α← _
        ≡⟨ bicat! C ⟩
      (α.σ a ⊗ β.σ a) ▶ F.υ→ ∘ ρ→ (α.σ a ⊗ β.σ a) ∘ λ← (α.σ a ⊗ β.σ a)
        ∎
```
</details>

<!--
```agda
  {-# DISPLAY ∘lx.lx f g = f ∘lx g #-}
```
-->

The same construction lets us compose pseudonatural transformations,
since if the naturators of $\alpha$ and $\beta$ are invertible, then the
composite constructed above is invertible, too.

```agda
  _∘px_ : G =>ₚ H → F =>ₚ G → F =>ₚ H
  _∘px_ α β .lax             = α .lax ∘lx β .lax
  _∘px_ α β .naturator-inv f = CH.invertible-∘
    (CH.is-invertible.op (CH.inverses→invertible (C.α≅ .inverses)))
    $ CH.invertible-∘ (C.▶.F-map-invertible (β .naturator-inv f))
    $ CH.invertible-∘ (CH.inverses→invertible (C.α≅ .inverses))
    $ CH.invertible-∘ (C.◀.F-map-invertible (α .naturator-inv f))
    $ CH.is-invertible.op (CH.inverses→invertible (C.α≅ .inverses))
```
