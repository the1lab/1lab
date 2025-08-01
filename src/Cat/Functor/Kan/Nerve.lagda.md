---
description: |
  We use the calculation of left Kan extensions as certain colimits to
  associate a "nerve" (restricted Yoneda embedding) and "realization"
  (left Kan extension along よ) adjunction given any functor.
---

<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.Kan.Pointwise
open import Cat.Diagram.Colimit.Base
open import Cat.Instances.Functor
open import Cat.Functor.Kan.Base
open import Cat.Diagram.Initial
open import Cat.Functor.Adjoint
open import Cat.Functor.Compose
open import Cat.Instances.Comma
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning
```
-->

```agda
module Cat.Functor.Kan.Nerve where
```

<!--
```agda
private
  variable o' o κ : Level
open Func
open _=>_
open is-lan
```
-->

# Nerve and realisation

Let $F : \cC \to \cD$ be a functor from a [$\kappa$-small] category
$\cC$ to a locally $\kappa$-small, $\kappa$-[cocomplete] category $\cD$.
$F$ induces a pair of [[adjoint functors]], as in the diagram below,
where $|-| \dashv \bf{N}$. In general, the left adjoint is called
"realization", and the right adjoint is called "nerve".

[$\kappa$-small]: 1Lab.intro.html#universes-and-size-issues
[cocomplete]: Cat.Diagram.Colimit.Base.html#cocompleteness

~~~{.quiver}
\[\begin{tikzcd}
  {\mathrm{PSh}(\mathcal{C})} && {\mathcal{D}}
  \arrow[""{name=0, anchor=center, inner sep=0}, "{\mathbf{N}}"', shift right=2, from=1-3, to=1-1]
  \arrow[""{name=1, anchor=center, inner sep=0}, "{|-|}"', shift right=2, from=1-1, to=1-3]
  \arrow["\dashv"{anchor=center, rotate=90}, draw=none, from=1, to=0]
\end{tikzcd}\]
~~~

An example to keep in mind is the inclusion $F : \Delta \mono \strcat$
from the simplex category to the [[category of strict categories]],
which sends the $n$-simplex to the finite [[poset]] $[n]$. In this case,
the left adjoint is the ordinary realisation of a simplicial set
$[\Delta\op,\Sets]$ as a [[strict category]], and the right adjoint gives
the simplicial nerve of a strict category.

Since these adjunctions come for very cheap ($\kappa$-cocompleteness of
the codomain category is all we need), they are built out of very thin
abstract nonsense: The "realisation" left adjoint is given by the [[left
Kan extension]] of $F$ along the [[Yoneda embedding]] $\yo$, which can be
[computed] as a particular colimit, and the "nerve" right adjoint is
given by the _restricted_ Yoneda embedding functor $X \mapsto \hom(F(-),
X)$.

[computed]: Cat.Functor.Kan.Pointwise.html

<!--
```agda
module _
  {o' o κ} {C : Precategory o' κ} {D : Precategory o κ}
  (F : Functor C D)
  where
    private
      module C = Cat.Reasoning C
      module D = Cat.Reasoning D
      module F = Func F
```
-->

:::{.definition .commented-out #nerve}
The **nerve** $\cD \to \psh(\cC)$ along a functor $F : \cC \to \cD$ is
the composition
$$
\cD \xto{\yo} \psh(\cD) \xto{(- \circ F)} \psh(\cC)
$$
of $\cD$'s [[Yoneda embedding]] with precomposition by $F$.
:::

```agda
    Nerve : Functor D (PSh κ C)
    Nerve .F₀ c    = Hom-into D c F∘ Functor.op F
    Nerve .F₁ f    = よ₁ D f ◂ (Functor.op F)
    Nerve .F-id    = ext λ _ _ → D.idl _
    Nerve .F-∘ _ _ = ext λ _ _ → sym (D.assoc _ _ _)
```

The action of $F$ on morphisms assembles into a natural transformation
$\yo_\cC \To \rm{Nerve}(F) \circ F$, which is universal in the following
sense: the nerve functor associated to $F$ is the [[left Kan extension]]
of $\cC$'s [[Yoneda embedding]] along $F$.

```agda
    coapprox : よ C => Nerve F∘ F
    coapprox .η x .η y f            = F.₁ f
    coapprox .η x .is-natural _ _ _ = ext λ _   → F.F-∘ _ _
    coapprox .is-natural _ _ _      = ext λ _ _ → F.F-∘ _ _
```

~~~{.quiver}
\[\begin{tikzcd}
  {\cC} && {\psh(\cC)} \\
  \\
  {\cD}
  \arrow["{\rm{yo}_\cC}", from=1-1, to=1-3]
  \arrow["F"', from=1-1, to=3-1]
  \arrow["{\rm{Nerve}(F)}"', from=3-1, to=1-3]
\end{tikzcd}\]
~~~

If we're given a functor $M : \cD \to \psh(\cC)$ and natural
transformation $\yo_\cC \to MF$, we can produce a natural transformation
$\alpha : \rm{Nerve}(F) \to M$ using $M$'s own action on morphisms,
since --- in components --- we have to transform an element of $f :
\hom(Fc,d)$ into one of $M(d)(c)$. Using $\alpha$, we obtain an element
of $M(Fc)(c)$, which maps under $M(f)$ to what we want.

```agda
    Nerve-is-lan : is-lan F (よ C) Nerve coapprox
    Nerve-is-lan .σ {M = M} α .η d .η c f =
      M .F₁ f .η c (α .η c .η c C.id)
```

<details>
<summary>
The construction is concluded by straightforward, though tedious,
computations using naturality. It's not very enlightening.
</summary>

```agda
    Nerve-is-lan .σ {M = M} α .η d .is-natural x y f = funext λ g →
      M.₁ (g D.∘ F.₁ f) .η y (α .η y .η y C.id)          ≡⟨ M.F-∘ g (F .F₁ f) ηₚ _ $ₚ _ ⟩
      M.₁ g .η y (M .F₁ (F.₁ f) .η y (α .η y .η y C.id)) ≡˘⟨ ap (M.F₁ g .η y) (α .is-natural _ _ _ ηₚ _ $ₚ _) ⟩
      M.₁ g .η y (α .η x .η y ⌜ f C.∘ C.id ⌝)            ≡⟨ ap! C.id-comm ⟩
      M.₁ g .η y (α .η x .η y (C.id C.∘ f))              ≡⟨ ap (M.₁ g .η y) (α .η _ .is-natural _ _ _ $ₚ _) ⟩
      M.₁ g .η y (M.₀ (F.₀ x) .F₁ f (α .η x .η x C.id))  ≡⟨ M.₁ g .is-natural _ _ _ $ₚ _ ⟩
      M.₀ d .F₁ f (M.₁ g .η x (α .η x .η x C.id))        ∎
      where module M = Functor M

    Nerve-is-lan .σ {M = M} α .is-natural x y f = ext λ z g →
      M .F-∘ f g ηₚ _ $ₚ _

    Nerve-is-lan .σ-comm {M = M} {α = α} = ext λ x y f →
      M.₁ (F.₁ f) .η y (α .η y .η y C.id) ≡˘⟨ α .is-natural _ _ _ ηₚ _ $ₚ _ ⟩
      α .η x .η y (f C.∘ C.id)            ≡⟨ ap (α .η x .η y) (C.idr _) ⟩
      α .η x .η y f                       ∎
      where module M = Functor M

    Nerve-is-lan .σ-uniq {M = M} {α = α} {σ' = σ'} p = ext λ x y f →
      M.₁ f .η y (α .η y .η y C.id)          ≡⟨ ap (M.₁ f .η y) (p ηₚ _ ηₚ _ $ₚ _) ⟩
      M.₁ f .η y (σ' .η _ .η y ⌜ F.₁ C.id ⌝) ≡⟨ ap! F.F-id ⟩
      M.₁ f .η y (σ' .η _ .η y D.id)         ≡˘⟨ σ' .is-natural _ _ _ ηₚ _ $ₚ _ ⟩
      σ' .η x .η y (f D.∘ D.id)              ≡⟨ ap (σ' .η x .η y) (D.idr _) ⟩
      σ' .η x .η y f                         ∎
      where module M = Functor M
```
</summary>
</details>

<!--
```agda
module _
  {o κ κ'} {C : Precategory κ κ} {D : Precategory o κ'}
  (F : Functor C D)
  (cocompl : is-cocomplete κ κ D)
  where
```
-->

Since we have assumed $\cC$ is $\kappa$-small and $\cD$ is
$\kappa$-cocomplete, any functor $F : \cC \to \cD$ admits an extension
$\Lan_{\yo}(F)$. This instance of generalised abstract nonsense is the
left adjoint we were after, the "realisation" functor.

```agda
  Realisation : Functor (PSh κ C) D
  Realisation = Lan.Ext (cocomplete→lan (よ C) F cocompl)

  approx : F => Realisation F∘ よ C
  approx = Lan.eta (cocomplete→lan (よ C) F cocompl)

  Realisation-is-lan : is-lan (よ C) F Realisation approx
  Realisation-is-lan = Lan.has-lan (cocomplete→lan (よ C) F cocompl)
```

<!--
```agda
module _
  {o κ} {C : Precategory κ κ} {D : Precategory o κ}
  (F : Functor C D)
  (cocompl : is-cocomplete κ κ D)
  where

  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module F = Func F

    module ↓colim c' =
      comma-colimits→lan.↓colim (よ C) F (λ c'' → cocompl (F F∘ Dom (よ C) (!Const c''))) c'
```
-->

```agda
  Realisation⊣Nerve : Realisation F cocompl ⊣ Nerve F
  Realisation⊣Nerve = adj where
    open _⊣_
    open ↓Obj
    open ↓Hom
```

Recall that $\Lan_{\yo}(F)(P)$ is defined pointwise as the colimit under
the diagram

$$
(\yo_\cC \downarrow P) \to C \xto{F} D
$$,

where we can identify $\yo_\cC \downarrow P$ with the [category of
elements] of the presheaf $P$. Any object $i : \cC$ with
section $P(i)$ defines an object of this category, which in the proof
below we denote `elem`{.Agda}.

[category of elements]: Cat.Instances.Elements.html

```agda
    elem : (P : Functor (C ^op) (Sets κ)) (i : C.Ob)
         → (arg : P ʻ i) → ↓Obj (よ C) (!Const P)
    elem P i arg .dom = i
    elem P i arg .cod = tt
    elem P i arg .map .η j h = P .F₁ h arg
    elem P i arg .map .is-natural _ _ f = ext λ _ → P .F-∘ _ _ $ₚ _
```

The adjunction unit is easiest to describe: we must come up with a map
$F(i) \to \Lan_{\yo}(F)(P)$, in the context of an object $i : \cC$ and
section $a : P(i)$. This is an object in the diagram that we took a
colimit over, so the coprojection $\psi$ has a component expressing
precisely what we need. Naturality is omitted from this page for
brevity, but it follows from $\psi$'s universal property.

```agda
    adj : Realisation F cocompl ⊣ Nerve F
    adj .unit .η P .η i a = ↓colim.ψ P (elem P i a)
```

In the other direction, we're mapping _out_ of a colimit, into an
arbitrary object $o : \cD$. It will suffice to come up with a family of
compatible maps $F(j) \to o$, where $j$ is an object in the comma
category

$$
\yo_\cC \downarrow (\yo_\cD(o) \circ F)
$$.

These, by definition, come with (natural) functions $\hom_\cC(-, j) \to
\hom_\cD(F-, o)$, which we can evaluate at the identity morphism to get
the map we want. That this assembles into a map from the colimit follows
from that same naturality:

```agda
    adj .counit .η ob = ↓colim.universal _ (λ j → j .map .η _ C.id) comm
      where abstract
      comm
        : ∀ {x y} (f : ↓Hom (よ C) (!Const (Nerve F .F₀ ob)) x y)
        → y .map .η _ C.id D.∘ F.₁ (f .top) ≡ x .map .η _ C.id
      comm {x} {y} f =
        y .map .η _ C.id D.∘ F.₁ (f .top) ≡˘⟨ y .map .is-natural _ _ _ $ₚ _ ⟩
        y .map .η _ (C.id C.∘ f .top)     ≡⟨ ap (y .map .η _) C.id-comm-sym ⟩
        y .map .η _ (f .top C.∘ C.id)     ≡⟨ f .com ηₚ _ $ₚ _ ⟩
        x .map .η (x .dom) C.id           ∎
```

Naturality of this putative counit follows from the uniqueness of maps
from a colimit, and the triangle identities follow because, essentially,
"matching" on a colimit after applying one of the coprojections does the
obvious thing.

<!--
This proof is hateful.

```agda
    adj .unit .η P .is-natural x y f =
      funext λ _ → sym $ ↓colim.commutes P $ ↓hom (ext λ _ _ → P .F-∘ _ _ $ₚ _)
    adj .unit .is-natural x y f = ext λ i arg → sym $
        ↓colim.factors _ {j = elem x i arg} _ _
      ∙ ap (↓colim.ψ _) (↓Obj-path _ _ refl refl
          (ext λ _ _ → f .is-natural _ _ _ $ₚ _))

    adj .counit .is-natural x y f = ↓colim.unique₂ _ _
      (λ {x'} {y'} f →
        D.pullr (sym (y' .map .is-natural _ _ _ $ₚ _)
                  ∙ ap (y' .map .η _) C.id-comm-sym)
        ∙ ap (_ D.∘_) (f .com ηₚ _ $ₚ C.id))
      (λ j →
        D.pullr (↓colim.factors _ _ _)
        ∙ ↓colim.factors _ _ _)
      (λ j → D.pullr (↓colim.factors _ _ _))

    adj .zig {A} = ↓colim.unique₂ A _ (λ f → ↓colim.commutes _ f)
      (λ j →
          D.pullr (↓colim.factors _ _ _)
        ∙ ↓colim.factors _ _ _
        ∙ ap (↓colim.ψ _)
            (↓Obj-path _ _ refl refl
              (ext λ _ _ →
                  sym (j .map .is-natural _ _ _ $ₚ _)
                ∙ ap (j .map .η _) (C.idl _))))
      (λ j → D.idl _)
    adj .zag {d} = ext λ c f →
      ↓colim.factors (Nerve F .F₀ d) {j = elem _ c f} _ _
      ∙ F.elimr refl
```
-->
