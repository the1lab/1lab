<!--
```agda
open import Cat.Bi.Lax-functor.Lax-transfor
open import Cat.Bi.Solver
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Bi.Reasoning as Br
```
-->

```agda
module Cat.Bi.Lax-functor.Modification
  {o h l o' h' l'} {B : Prebicategory o h l} {C : Prebicategory o' h' l'}
  where
```

# Identity and composition of modifications

In analogy with how functors between categories $\cC$ and $\cD$ and
together with natural transformations form the [[functor category]]
$[\cC,\cD]$, [[lax functors]] between [[bicategories]] $\bf{B}$ and
$\bf{C}$ similarly [form a bicategory] $[\bf{C},\bf{D}]$ where 0-cells
are lax functors and 1-cells are [[lax transformations]].

[form a bicategory]: Cat.Bi.Lax-functor.Base.html

The 2-cells in this bicategory, that is, morphisms between lax
transformations, are given by [[modifications]].  Here, we describe how
modifications can be composed both vertically and horizontally,
similarly to natural transformations between functors.  In fact, these
constructions very much resemble the corresponding constructions on
natural transformations, so we won't dwell too much on the details.

<!--
```agda
unquoteDecl H-Level-Modification = declare-record-hlevel 2 H-Level-Modification (quote Modification)

open Prebicategory C
open Lax-transfor
open Modification

private
  module B  = Prebicategory B
  module C  = Br C
  module CH = C.Hom

module _ {F G : Lax-functor B C} where
  private
    module F  = Lax-functor F
    module G  = Lax-functor G
```
-->

The identity modification has identity components.

```agda
  idmd : {α : F =>ₗ G} → Modification α α
  idmd .Γ _        = Hom.id
  idmd .is-natural = C.▶.elimr refl ∙ C.◀.introl refl
```

The vertical composition of two modifications between lax
transformations is given by the componentwise composition.

```agda
  _∘md_ : {α β γ : F =>ₗ G} → Modification β γ → Modification α β → Modification α γ
  _∘md_ f g .Γ a                                    = f .Γ a ∘ g .Γ a
  _∘md_ {x} {y} {z} f g .is-natural {a} {b} {f = h} =
    ν→ z h ∘ G.₁ h ▶ (f .Γ a ∘ g .Γ a)       ≡⟨ CH.refl⟩∘⟨ C.▶-distribr ⟩
    ν→ z h ∘ G.₁ h ▶ f .Γ a ∘ G.₁ h ▶ g .Γ a ≡⟨ CH.extendl $ f .is-natural ⟩
    f .Γ b ◀ F.₁ h ∘ ν→ y h ∘ G.₁ h ▶ g .Γ a ≡⟨ CH.refl⟩∘⟨ g .is-natural ⟩
    f .Γ b ◀ F.₁ h ∘ g .Γ b ◀ F.₁ h ∘ ν→ x h ≡⟨ CH.pulll $ sym C.◀-distribl ⟩
    (f .Γ b ∘ g .Γ b) ◀ F.₁ h ∘ ν→ x h       ∎
```

Before proceeding to horizontal composition, we take a moment to note
that modifications, consisting of families of 2-cells (which form a
set), also themselves form a set.

```agda
  opaque
    Mod-is-set : {α β : F =>ₗ G} → is-set (Modification α β)
    Mod-is-set = hlevel 2
```

We can characterize equality of modifications by an extensionality
principle: two modifications are equal if and only if they have
identical components.

```agda
  Mod-pathp : {α α' β β' : F =>ₗ G}
            → (p : α ≡ α') (q : β ≡ β')
            → {a : Modification α β} {b : Modification α' β'}
            → (∀ x → PathP _ (a .Γ x) (b .Γ x))
            → PathP (λ i → Modification (p i) (q i)) a b
  Mod-pathp p q path i .Γ x                            = path x i
  Mod-pathp p q {a} {b} path i .is-natural {x} {y} {f} =
    is-prop→pathp
      (λ i → CH.Hom-set _ _
        (ν→ (q i) f ∘ G.₁ f ▶ path x i) (path y i ◀ F.₁ f ∘ ν→ (p i) f))
      (a .is-natural)
      (b .is-natural) i

  Mod-path : {α β : F =>ₗ G} {a b : Modification α β}
           → ((x : _) → a .Γ x ≡ b .Γ x)
           → a ≡ b
  Mod-path = Mod-pathp refl refl
```

<!--
```agda
  _Γᵈ_ : {α α' β β' : F =>ₗ G} {p : α ≡ α'} {q : β ≡ β'}
       → {a : Modification α β} {b : Modification α' β'}
       → PathP (λ i → Modification (p i) (q i)) a b
       → ∀ x → PathP _ (a .Γ x) (b .Γ x)
  p Γᵈ x = apd (λ i e → e .Γ x) p

  _Γₚ_ : {α β : F =>ₗ G} {a b : Modification α β} → a ≡ b → ∀ x → a .Γ x ≡ b .Γ x
  p Γₚ x = ap (λ e → e .Γ x) p

  infixl 45 _Γₚ_

  instance
    Extensional-modification
      : ∀ {ℓr} {α β : F =>ₗ G}
      → ⦃ sa : {x : B.Ob} → Extensional (α .σ x ⇒ β .σ x) ℓr ⦄
      → Extensional (Modification α β) (o ⊔ ℓr)
    Extensional-modification ⦃ sa ⦄ .Pathᵉ f g = ∀ i → Pathᵉ sa (f .Γ i) (g .Γ i)
    Extensional-modification ⦃ sa ⦄ .reflᵉ x i = reflᵉ sa (x .Γ i)
    Extensional-modification ⦃ sa ⦄ .idsᵉ .to-path x = Mod-path λ i →
      sa .idsᵉ .to-path (x i)
    Extensional-modification ⦃ sa ⦄ .idsᵉ .to-path-over h =
      is-prop→pathp (λ i → Π-is-hlevel 1 λ _ → Pathᵉ-is-hlevel 1 sa (hlevel 2)) _ _

module _ {F G H : Lax-functor B C} {α α' : G =>ₗ H} {β β' : F =>ₗ G} where
  private
    module F  = Lax-functor F
    module G  = Lax-functor G
    module H  = Lax-functor H
    module α  = Lax-transfor α
    module α' = Lax-transfor α'
    module β  = Lax-transfor β
    module β' = Lax-transfor β'
```
-->

Finally, we proceed to describe the horizontal composition of
modifications.  Here we must give a modification from the composite
$\alpha \beta$ to the composite $\alpha' \beta'$, where $\alpha$,
$\alpha'$, $\beta$, and $\beta'$ are lax transformations, given a
modification from $\alpha$ to $\alpha'$ and one from $\beta$ to
$\beta'$.  Recalling that the composition $\alpha \beta$ is given by the
componentwise composition $(\alpha \beta)_a = \alpha_a \beta_a$, we can
use the horizontal composition native to the target bicategory to
construct our composite modification.

```agda
  _◆md_ : Modification α α' → Modification β β' → Modification (α ∘lx β) (α' ∘lx β')
  (f ◆md g) .Γ x = f .Γ x C.◆ g .Γ x
```

<details>
<summary>
Checking the naturality of this construction is straightforward in
principle, but because it involves the naturators of composite lax
transformations, which are very large terms, the proof gets unwieldy.
We leave the proof in this `<details>`{.html}-block for the interested
reader.
</summary>

```agda
  (f ◆md g) .is-natural {a} {b} {x} =
        (C.α← _ C.∘ α'.σ b C.▶ β'.ν→ x C.∘ C.α→ _ C.∘ α'.ν→ x C.◀ β'.σ a C.∘ C.α← _)
    C.∘ H.₁ x C.▶ (f .Γ a C.◆ g .Γ a)
      ≡⟨ bicat! C ⟩
        C.α← _ C.∘ α'.σ b C.▶ β'.ν→ x C.∘ C.α→ _ C.∘ ⌜ α'.ν→ x C.∘ H.₁ x C.▶ f .Γ a ⌝ C.◀ β'.σ a
    C.∘ C.α← _ C.∘ H.₁ x C.▶ (α.σ a C.▶ g .Γ a)
      ≡⟨ ap! (f .is-natural) ⟩
        C.α← _ C.∘ α'.σ b C.▶ β'.ν→ x C.∘ C.α→ _ C.∘ (f .Γ b C.◀ G.₁ x C.∘ α.ν→ x) C.◀ β'.σ a
    C.∘ C.α← _ C.∘ H.₁ x C.▶ (α.σ a C.▶ g .Γ a)
      ≡⟨ bicat! C ⟩
        C.α← _ C.∘ f .Γ b C.◀ (β'.σ b C.⊗ F.₁ x)
    C.∘ α.σ b C.▶ ⌜ β'.ν→ x C.∘ G.₁ x C.▶ g .Γ a ⌝ C.∘ C.α→ _ C.∘ α.ν→ x C.◀ β.σ a C.∘ C.α← _
      ≡⟨ ap! (g .is-natural) ⟩
        C.α← _ C.∘ f .Γ b C.◀ (β'.σ b C.⊗ F.₁ x)
    C.∘ α.σ b C.▶ (g .Γ b C.◀ F.₁ x C.∘ β.ν→ x) C.∘ C.α→ _ C.∘ α.ν→ x C.◀ β.σ a C.∘ C.α← _
      ≡⟨ bicat! C ⟩
        (f .Γ b C.◆ g .Γ b) C.◀ F.₁ x C.∘ C.α← _ C.∘ α.σ b C.▶ β.ν→ x C.∘ C.α→ _
    C.∘ α.ν→ x C.◀ β.σ a C.∘ C.α← _
      ∎
```
</details>
