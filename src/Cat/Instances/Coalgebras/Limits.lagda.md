<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.Kan.Unique
open import Cat.Functor.Naturality
open import Cat.Functor.Coherence
open import Cat.Instances.Coalgebras
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Limit.Cone
open import Cat.Functor.Kan.Base
open import Cat.Displayed.Total
open import Cat.Functor.Compose
open import Cat.Diagram.Comonad
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Coalgebras.Limits
  {o ℓ} (C : Precategory o ℓ) (W : Comonad C)
  where
```

<!--
```agda
open Cat.Reasoning C

open Total-hom
open _=>_

open Coalgebra-on
open Comonad W using (module W ; module comult ; module counit ; W-∘ ; W-id ; W₀ ; W₁)
```
-->

# Arbitrary limits of coalgebras

This module concerns itself with the more general construction of
[[limits]] in a [[category of coalgebras]], as mentioned in the (more
focused) construction of [[finite limits of coalgebras]]. Namely, if
$(W, \eps, \delta)$ is a [[comonad]] on $\cC$ which, as a functor,
preserves $\cI$-shaped limits, then the forgetful functor $U : \cC_W \to
\cC$ preserves _and_ reflects those same limits.

<!--
```agda
module
  _ {oi ℓi} {I : Precategory oi ℓi}
    (pres : ∀ (F : Functor I C) {X η} (l : is-ran !F F X η) → preserves-ran (Comonad.W W) l)
  where
```
-->

We start by showing reflection: Let $F : \cI \to \cC_W$ be a diagram of
$W$-coalgebras, $L$ be a coalgebra, and $\phi$ be a natural
transformation $\Delta(L) \to F$. If $(UL, U\phi)$ is the limit of $UF$
in $\cC$, then $(L, \phi)$ is the limit of $F$ in $\cC_W$.

```agda
  is-limit-coalgebra
    : ∀ (F : Functor I (Coalgebras W)) {K phi}
    → (l : is-ran !F (πᶠ _ F∘ F) (πᶠ _ F∘ K) (nat-assoc-from (πᶠ _ ▸ phi)))
    → reflects-ran (πᶠ (Coalgebras-over W)) l
  is-limit-coalgebra F {K} {phi} l = to-is-limitp mk fixup where
```

It will suffice to show the following: if $\eta_j : x \to Fj$ is a
natural family of coalgebra homomorphisms, then one may construct a map
$\nu : x \to L$ satisfying $\phi_j \nu = \eta_j$. For if we are given
such a map, we can show that $\nu$ is a coalgebra homomorphism $x \to
L$. Since $WL$ is a limit, we may argue for preservation componentwise
against the projections $W\phi_j$, and we have

$$
\begin{align*}
& \phantom{=} W\phi_j \circ W\nu \circ x  \\
&          =  Fj \circ \eta_j             \\
&          =  W\phi_j \circ L \circ \nu
\end{align*}
$$

so that $W\nu \circ x = L \circ \nu$, as required. Showing that $\nu$ is
indeed the unique map factoring $\eta_j$ through $L$ is done through
exactly the same style of argument.

<!--
```agda
    module K = Functor K
    module F = Functor F

    module l = is-limit l
    module l' = is-limit (pres _ l)
    open make-is-limit

    module
      _ {x : Coalgebras.Ob W}
        (eta : (j : Precategory.Ob I) → Coalgebras.Hom W x (F.₀ j))
        (nat : ∀ {x y} (f : Precategory.Hom I x y) → Coalgebras._∘_ W (F.₁ f) (eta x) ≡ eta y)
      where
```
-->

That's very well and good, but does such $\nu$ exist? Well, yes: much
like in the finite case, we note that $Fj \circ \eta_j$ is also natural
in $j$, so that the limit factorisation

$$
\langle Fj \circ \eta_j \rangle_j : x \to WL
$$

exists. By composing with $\eps$, we obtain a map $x \to WL \to L$, and
with a short calculation we establish that this map satisfies the
commutativity condition we remarked was sufficient above; we're done!

```agda
      opaque
        ν : Hom (x .fst) (K.₀ tt .fst)
        ν = counit.ε _ ∘ l'.universal (λ j → F.₀ j .snd .ρ ∘ eta j .hom) λ {x} {y} f →
          W₁ (F.₁ f .hom) ∘ F.₀ x .snd .ρ ∘ eta x .hom ≡⟨ pulll (F.₁ f .preserves) ⟩
          (F.₀ y .snd .ρ ∘ F.₁ f .hom) ∘ eta x .hom    ≡⟨ pullr (ap hom (nat _)) ⟩
          F.₀ y .snd .ρ ∘ eta y .hom                   ∎

        ν-β : ∀ {j} → phi .η j .hom ∘ ν ≡ eta j .hom
        ν-β {j} =
          phi .η j .hom ∘ ν                         ≡⟨ pulll (sym (counit.is-natural _ _ _)) ⟩
          (counit.ε _ ∘ l'.ψ j) ∘ l'.universal _ _  ≡⟨ pullr (l'.factors _ _) ⟩
          counit.ε _ ∘ F.₀ j .snd .ρ ∘ eta j .hom   ≡⟨ cancell (F.₀ _ .snd .ρ-counit) ⟩
          eta j .hom                                ∎
```

<!--
```agda
    mk : make-is-limit F (K.₀ tt)
    mk .ψ j .hom       = l.ψ j
    mk .ψ j .preserves = phi .η j .preserves
    mk .commutes f = coalgebra-hom-path W (l.commutes f)
    mk .universal eta nat .hom = ν eta nat
    mk .universal eta nat .preserves = l'.unique₂ _
      (λ f → pulll (F.₁ f .preserves) ∙ pullr (ap hom (nat _)))
      (λ j → W.pulll (ν-β eta nat) ∙ eta j .preserves)
      (λ j → pulll (phi .η j .preserves) ∙ pullr (ν-β eta nat))
    mk .factors eta nat = coalgebra-hom-path W (ν-β eta nat)
    mk .unique eta nat other comm = coalgebra-hom-path W (l.unique₂ _
      (λ f → ap hom (nat f)) (λ j → ap hom (comm j)) (λ j → ν-β eta nat))

    abstract
      fixup : ∀ {j} → mk .ψ j ≡ phi .η j
      fixup = coalgebra-hom-path W refl
```
-->

```agda
  Coalgebra-on-limit
    : (F : Functor I (Coalgebras W))
    → (L : Limit (πᶠ (Coalgebras-over W) F∘ F))
    → Coalgebra-on W (Limit.apex L)
  Coalgebra-on-limit F L = coalg module Coalgebra-on-limit where
```

<!--
```agda
    private
      module L   = Limit L
      module L'  = is-limit (pres (πᶠ _ F∘ F) L.has-limit)
      module L'' = is-limit (pres _ (pres (πᶠ _ F∘ F) L.has-limit))
      module F   = Functor F
```
-->

```agda
    opaque
      ν : Hom L.apex (W₀ L.apex)
      ν = L'.universal (λ j → F.₀ j .snd .ρ ∘ L.ψ j) λ {x} {y} h →
        W₁ (F.₁ h .hom) ∘ F.₀ x .snd .ρ ∘ L.eps .η x ≡⟨ pulll (F.₁ h .preserves) ⟩
        (F.₀ y .snd .ρ ∘ F.₁ h .hom) ∘ L.eps .η x    ≡⟨ pullr (sym (L.eps .is-natural _ _ _) ∙ elimr L.Ext.F-id) ⟩
        F.₀ y .snd .ρ ∘ L.eps .η y                   ∎

      ν-β : ∀ {j} → W₁ (L.eps .η j) ∘ ν ≡ F.₀ j .snd .ρ ∘ L.eps .η j
      ν-β = L'.factors _ _
```

```agda
    coalg : Coalgebra-on W (Limit.apex L)
    coalg .ρ = ν
    coalg .ρ-counit = L.unique₂ _
      (λ f → sym (L.eps .is-natural _ _ f) ∙ elimr L.Ext.F-id)
      (λ j → pulll (sym (counit.is-natural _ _ _))
          ·· pullr ν-β
          ·· cancell (F.₀ j .snd .ρ-counit))
      (λ j → idr (L.eps .η j))
    coalg .ρ-comult = L''.unique₂ _
      (λ f → W.extendl (F.₁ f .preserves) ∙ ap₂ _∘_ refl
        ( pulll (F.₁ f .preserves)
        ∙ pullr (sym (L.eps .is-natural _ _ f) ∙ elimr L.Ext.F-id)))
      (λ j → W.extendl ν-β ∙ ap₂ _∘_ refl ν-β)
      λ j → pulll (sym (comult.is-natural _ _ _))
         ·· pullr ν-β
         ·· extendl (sym (F.₀ j .snd .ρ-comult))
```

```agda
  open Ran
  open is-ran

  Coalgebra-limit
    : (F : Functor I (Coalgebras W))
    → Limit (πᶠ (Coalgebras-over W) F∘ F)
    → Limit F
  Coalgebra-limit F lim .Ext = const! (_ , Coalgebra-on-limit F lim)

  Coalgebra-limit F lim .eps .η x .hom       = lim .eps .η x
  Coalgebra-limit F lim .eps .η x .preserves = Coalgebra-on-limit.ν-β F lim
  Coalgebra-limit F lim .eps .is-natural x y f = coalgebra-hom-path W $
    ap₂ _∘_ refl (sym (lim .Ext .Functor.F-id)) ∙ lim .eps .is-natural x y f
```

```agda
  Coalgebra-limit F lim .has-ran = is-limit-coalgebra F $ natural-isos→is-ran
    idni idni rem₁
    (Nat-path λ x → idl _ ∙ elimr (elimr refl ∙ lim .Ext .Functor.F-id))
    (lim .has-ran)

    where
    open make-natural-iso

    rem₁ : lim .Ext ≅ⁿ πᶠ (Coalgebras-over W) F∘ const! (_ , Coalgebra-on-limit F lim)
    rem₁ = to-natural-iso λ where
      .eta x → id
      .inv x → id
      .eta∘inv x → idl id
      .inv∘eta x → idl id
      .natural x y f → eliml refl ∙ intror (lim .Ext .Functor.F-id)
```
