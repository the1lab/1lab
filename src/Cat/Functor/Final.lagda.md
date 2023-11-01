<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Colimit.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Functor.Final where
```

# Final functors

A **final functor** expresses an equivalence of diagram schemata for the
purposes of computing colimits: If $F : \cC \to \cD$ is final,
then colimits for $D : \cD \to \cE$ are equivalents to colimits
for $D\circ F : \cC \to \cE$. A terminological warning: In older
literature (e.g. [@Borceux:vol1] and [@AdamekRosicky]), these functors
are called **cofinal**, but we stick with terminology from the nLab
here.

<!--
```agda
module
  _ {o ℓ o' ℓ'} {𝒞 : Precategory o ℓ} {𝒟 : Precategory o' ℓ'}
    (F : Functor 𝒞 𝒟)
  where

  open Functor

  private
    module 𝒞 = Cr 𝒞
    module 𝒟 = Cr 𝒟
    module F = Functor F
```
-->

Finality has an elementary characterisation: We define a functor $F$ to
be final if, for every $d$, the comma category $d \swarrow F$ is pointed
and connected. That is, unpacking, the following data: For every object
$d : \cD$, an object $d_0$ and a map $d_! : d \to F(d_0)$, and for
every span

~~~{.quiver .short-05}
\[\begin{tikzcd}
  & x \\
  Fa && Fb\text{,}
  \arrow["f", from=1-2, to=2-1]
  \arrow["g"', from=1-2, to=2-3]
\end{tikzcd}\]
~~~

a map $f : a \to b$, such that the triangle

~~~{.quiver .short-05}
\[\begin{tikzcd}
  & x \\
  Fa && Fb
  \arrow["f", from=1-2, to=2-1]
  \arrow["g"', from=1-2, to=2-3]
  \arrow["{F(f)}"', from=2-1, to=2-3]
\end{tikzcd}\]
~~~

commutes.

```agda
  record is-final : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
    field
      point : 𝒟.Ob → 𝒞.Ob
      map   : ∀ d → 𝒟.Hom d (F.₀ (point d))
      extend
        : ∀ {a b x} (f : 𝒟.Hom x (F.₀ a)) (g : 𝒟.Hom x (F.₀ b))
        → 𝒞.Hom a b
      extend-commutes
        : ∀ {a b x} (f : 𝒟.Hom x (F.₀ a)) (g : 𝒟.Hom x (F.₀ b))
        → g ≡ F.₁ (extend f g) 𝒟.∘ f
```

<!--
```agda
  module
    _ {o'' ℓ''} {ℰ : Precategory o'' ℓ''} {D : Functor 𝒟 ℰ} (final : is-final)
    where
    private
      module fin = is-final final
      module D = Func D
      module ℰ = Cr ℰ
      open _=>_
```
-->

The utility of this definition comes, as mentioned, from the ability to
move (colimiting) cocones back and forth between a diagram $D$ and its
restriction $D_{|F}$ to the domain category $\cC$. If we have a
cocone $\{DF(x) \to K\}$, then precomposition with the map $D(x_!) :
D(x) \to DF(x_0)$ (where $x_!$ comes from the finality of $F$) defines a
cocone $\{D(x) \to K\}$.

```agda
    extend-cocone : ∀ {coapex} → D F∘ F => Const coapex → D => Const coapex
    extend-cocone cone .η x = cone .η _ ℰ.∘ D.₁ (fin.map x)
    extend-cocone cone .is-natural x y f =
      ℰ.pullr (sym (D.F-∘ _ _))
      ·· ℰ.pushl (sym (cone .is-natural _ _ _ ∙ ℰ.idl _))
      ·· (ℰ.refl⟩∘⟨ D.collapse (sym (fin.extend-commutes _ _)))
      ∙ sym (ℰ.idl _)
```

In the other direction, suppose that we have a cocone $\{D(x) \to K\}$
--- inserting $F$ in the appropriate places makes a cocone $\{DF(x) \to
K\}$.

```agda
    restrict-cocone : ∀ {coapex} → D => Const coapex → D F∘ F => Const coapex
    restrict-cocone K .η x = K .η (F.F₀ x)
    restrict-cocone K .is-natural x y f = K .is-natural (F.F₀ x) (F.F₀ y) (F.F₁ f)
```

A computation using connectedness of the comma categories shows that
these formulae are mutually inverse:

```agda
    open is-iso
    extend-cocone-is-iso : ∀ {coapex} → is-iso (extend-cocone {coapex})
    extend-cocone-is-iso .inv = restrict-cocone
    extend-cocone-is-iso .rinv x =
      Nat-path λ o →
        x .is-natural _ _ _ ∙ ℰ.idl _
    extend-cocone-is-iso .linv x =
      Nat-path λ o →
        (sym (ℰ.idl _) ∙ sym (x .is-natural _ _ (fin.extend (fin.map (F.F₀ o)) 𝒟.id)) ℰ.⟩∘⟨refl)
        ·· ℰ.pullr (D.collapse (fin.extend-commutes _ _ ∙ 𝒟.idr _))
        ·· x .is-natural _ _ _
        ∙ ℰ.idl _
```

The most important conclusion that we get is the following: If you can
show that the restricted cocone is a colimit, then the original cocone
was a colimit, too! We'll do this in two steps: First, show that the
_extension_ of a colimiting cocone is a colimit. Then, using the fact
that `restrict-cocone`{.Agda} is an equivalence, we'll be able to fix up
the polarity mismatch.

```agda
    extend-is-colimit
      : ∀ {coapex} (K : D F∘ F => Const coapex)
      → is-colimit (D F∘ F) coapex K
      → is-colimit D coapex (extend-cocone K)
```

<details>
<summary>
The proof of the auxiliary lemma is a direct computation, so I'll leave
it in this `<details>`{.html} tag for the curious reader only.
</summary>

```agda
    extend-is-colimit {coapex} K colim =
      to-is-colimitp mc refl
      module extend-is-colimit where
        module colim = is-colimit colim
        open make-is-colimit

        mc : make-is-colimit D coapex
        mc .ψ x = extend-cocone K .η x
        mc .commutes f = extend-cocone K .is-natural _ _ _ ∙ ℰ.idl _
        mc .universal eps p =
          colim.universal (λ j → eps (F.F₀ j)) λ f → p (F.F₁ f)
        mc .factors eps p =
          ℰ.pulll (colim.factors _ _)
          ∙ p (fin.map _)
        mc .unique eps p other q =
          colim.unique _ _ _ λ j →
            other ℰ.∘ K .η j                                  ≡⟨ ℰ.refl⟩∘⟨ (sym (ℰ.idl _) ∙ sym (K .is-natural _ _ _)) ⟩
            other ℰ.∘ K .η _ ℰ.∘ D.F₁ (F.F₁ (fin.extend _ _)) ≡⟨ ℰ.refl⟩∘⟨ ℰ.refl⟩∘⟨ ap D.₁ (sym (𝒟.idr _) ∙ sym (fin.extend-commutes _ _)) ⟩
            other ℰ.∘ K .η _ ℰ.∘ D.F₁ (fin.map _)             ≡⟨ q (F.F₀ j) ⟩
            eps (F.F₀ j)                                      ∎
```

</details>

```agda
    is-colimit-restrict
      : ∀ {coapex}
      → (K : D => Const coapex)
      → is-colimit (D F∘ F) coapex (restrict-cocone K)
      → is-colimit D coapex K
    is-colimit-restrict {coapex} K colim =
      to-is-colimitp
        (extend-is-colimit.mc (restrict-cocone K) colim)
        (extend-cocone-is-iso .rinv K ηₚ _)
        where open is-iso
```

<!--
```agda
module
  _ {o ℓ o' ℓ' o'' ℓ''}
    {𝒞 : Precategory o ℓ} {𝒟 : Precategory o' ℓ'} {ℰ : Precategory o'' ℓ''}
    (F : Functor 𝒞 𝒟) (G : Functor 𝒟 ℰ)
    (f-fin : is-final F) (g-fin : is-final G)
  where
  private
    module 𝒟 = Cr 𝒟
    module ℰ = Cr ℰ
    module G = Functor G
    module F = Functor F
    module ff = is-final f-fin
    module gf = is-final g-fin
    open is-final
```
-->

Another short computation shows us that final functors are closed under
composition.

```agda
  F∘-is-final : is-final (G F∘ F)
  F∘-is-final .point e    = ff.point (gf.point e)
  F∘-is-final .map d      = G.₁ (ff.map _) ℰ.∘ gf.map _
  F∘-is-final .extend f g = ff.extend 𝒟.id (gf.extend f g)
  F∘-is-final .extend-commutes f g =
    g                                                ≡⟨ gf.extend-commutes _ _ ⟩
    G.₁ ⌜ g-fin .extend f g ⌝ ℰ.∘ f                  ≡⟨ ap! (ff.extend-commutes _ _ ∙ 𝒟.elimr refl) ⟩
    G.₁ (F.₁ (ff.extend 𝒟.id (gf.extend f g))) ℰ.∘ f ∎
```
