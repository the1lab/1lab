```agda
open import Cat.Diagram.Colimit.Base
open import Cat.Prelude

import Cat.Reasoning as Cr

module Cat.Functor.Final where
```

# Final functors

A **final functor** expresses an equivalence of diagram schemata for the
purposes of computing colimits: If $F : \ca{C} \to \ca{D}$ is final,
then colimits for $D : \ca{D} \to \ca{E}$ are equivalents to colimits
for $D\circ F : \ca{C} \to \ca{E}$. A terminological warning: In older
literature (e.g. [@Borceux:vol1] and [@AdamekRosicky]), these functors
are called **cofinal**, but we stick with terminology from the nLab
here.

<!--
```agda
module
  _ {o ℓ o′ ℓ′} {𝒞 : Precategory o ℓ} {𝒟 : Precategory o′ ℓ′}
    (F : Functor 𝒞 𝒟)
  where

  open Cocone-hom
  open Functor
  open Cocone

  private
    module 𝒞 = Cr 𝒞
    module 𝒟 = Cr 𝒟
    module F = Functor F
```
-->

Finality has an elementary characterisation: We define a functor $F$ to
be final if, for every $d$, the comma category $d \swarrow F$ is pointed
and connected. That is, unpacking, the following data: For every object
$d : \ca{D}$, an object $d_0$ and a map $d_! : d \to F(d_0)$, and for
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
  record is-final : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
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
    _ {o′′ ℓ′′} {ℰ : Precategory o′′ ℓ′′} {D : Functor 𝒟 ℰ} (final : is-final)
    where
    private
      module fin = is-final final
      module D = Functor D
      module ℰ = Cr ℰ
```
-->

The utility of this definition comes, as mentioned, from the ability to
move (colimiting) cocones back and forth between a diagram $D$ and its
restriction $D_{|F}$ to the domain category $\ca{C}$. If we have a
cocone $\{DF(x) \to K\}$, then precomposition with the map $D(x_!) :
D(x) \to DF(x_0)$ (where $x_!$ comes from the finality of $F$) defines a
cocone $\{D(x) \to K\}$.

```agda
    extend-cocone : Cocone (D F∘ F) → Cocone D
    extend-cocone cone = cone′ where
      open is-iso
      module cone = Cocone cone
      cone′ : Cocone D
      cone′ .coapex = cone.coapex
      cone′ .ψ x = cone.ψ _ ℰ.∘ D.₁ (fin.map x)
      cone′ .commutes f =
        (cone.ψ _ ℰ.∘ D.₁ (fin.map _)) ℰ.∘ D.₁ f ≡⟨ ℰ.pullr (sym (D.F-∘ _ _)) ⟩
        cone.ψ _ ℰ.∘ D.₁ (fin.map _ 𝒟.∘ f)       ≡⟨ ℰ.pushl (sym (cone.commutes (fin.extend (fin.map _ 𝒟.∘ f) (fin.map _)))) ⟩
        cone.ψ _ ℰ.∘ _                           ≡⟨ ℰ.refl⟩∘⟨ sym (D.F-∘ _ _) ∙ ap D.₁ (sym (fin.extend-commutes _ _)) ⟩
        cone.ψ _ ℰ.∘ D.₁ (fin.map _)             ∎
```

In the other direction, suppose that we have a cocone $\{D(x) \to K\}$
--- inserting $F$ in the appropriate places makes a cocone $\{DF(x) \to
K\}$.

```agda
    restrict-cocone : Cocone D → Cocone (D F∘ F)
    restrict-cocone K = K′ where
      module K = Cocone K
      K′ : Cocone (D F∘ F)
      K′ .coapex = K.coapex
      K′ .ψ x = K.ψ (F.F₀ x)
      K′ .commutes f = K.commutes (F.F₁ f)
```

A computation using connectedness of the comma categories shows that
these formulae are mutually inverse:

```agda
    open is-iso
    extend-cocone-is-iso : is-iso extend-cocone
    extend-cocone-is-iso .inv = restrict-cocone
    extend-cocone-is-iso .rinv x = Cocone-path _ refl $ λ o →
      x .commutes _
    extend-cocone-is-iso .linv x = Cocone-path _ refl $ λ o →
      x .ψ _ ℰ.∘ D.₁ (fin.map (F.F₀ o))                           ≡˘⟨ x .commutes (fin.extend (fin.map (F.F₀ o)) 𝒟.id) ℰ.⟩∘⟨refl ⟩
      (x .ψ o ℰ.∘ D.₁ (F.₁ (fin.extend _ _))) ℰ.∘ D.₁ (fin.map _) ≡⟨ ℰ.pullr (sym (D.F-∘ _ _) ·· ap D.₁ (fin.extend-commutes _ _) ·· ap D.₁ (𝒟.idr _)) ⟩
      x .ψ o ℰ.∘ D.₁ (F.₁ (fin.extend _ _))                       ≡⟨ x .commutes _ ⟩
      x .ψ o                                                      ∎

    restriction-eqv : Cocone (D F∘ F) ≃ Cocone D
    restriction-eqv = _ , is-iso→is-equiv extend-cocone-is-iso
```

The most important conclusion that we get is the following: If you can
show that the restricted cocone is a colimit, then the original cocone
was a colimit, too! We'll do this in two steps: First, show that the
_extension_ of a colimiting cocone is a colimit. Then, using the fact
that `restrict-cocone`{.Agda} is an equivalence, we'll be able to fix up
the polarity mismatch.

```agda
    extend-is-colimit
      : (K : Cocone (D F∘ F))
      → is-colimit (D F∘ F) K → is-colimit D (extend-cocone K)
```

<details>
<summary>
The proof of the auxiliary lemma is a direct computation, so I'll leave
it in this `<details>`{.html} tag for the curious reader only.
</summary>

```agda
    extend-is-colimit K colim x = contr x¡ x¡-unique where
      module K = Cocone K
      module x = Cocone x
      x′ : Cocone (D F∘ F)
      x′ = restrict-cocone x

      x′¡ = colim x′
      x¡ : Cocone-hom D (extend-cocone K) x
      x¡ .hom = x′¡ .centre .hom
      x¡ .commutes o =
        x′¡ .centre .hom ℰ.∘ K.ψ _ ℰ.∘ D.₁ _    ≡⟨ ℰ.pulll (x′¡ .centre .commutes _) ⟩
        x′ .ψ _ ℰ.∘ D.₁ (fin.map o)             ≡⟨ x .commutes _ ⟩
        x.ψ o                                   ∎

      x¡-unique : ∀ h′ → x¡ ≡ h′
      x¡-unique h′ = Cocone-hom-path D $ ap hom $ x′¡ .paths go where
        go : Cocone-hom (D F∘ F) K x′
        go .hom = h′ .hom
        go .commutes o =
          h′ .hom ℰ.∘ K.ψ o                     ≡˘⟨ ℰ.refl⟩∘⟨ K.commutes (fin.extend 𝒟.id (fin.map _)) ⟩
          h′ .hom ℰ.∘ K.ψ _ ℰ.∘ D.₁ (F.₁ _)     ≡⟨ ℰ.refl⟩∘⟨ ℰ.refl⟩∘⟨ ap D.₁ (𝒟.intror refl ∙ sym (fin.extend-commutes _ _)) ⟩
          h′ .hom ℰ.∘ K.ψ _ ℰ.∘ D.₁ (fin.map _) ≡⟨ h′ .commutes _ ⟩
          x.ψ (F.₀ o)                           ∎
```

</details>

```agda
    is-colimit-restrict
      : (K : Cocone D)
      → is-colimit (D F∘ F) (restrict-cocone K) → is-colimit D K
    is-colimit-restrict K colim = subst (is-colimit D)
      (Equiv.ε restriction-eqv _)
      (extend-is-colimit (restrict-cocone K) colim)
```

<!--
```agda
module
  _ {o ℓ o′ ℓ′ o′′ ℓ′′}
    {𝒞 : Precategory o ℓ} {𝒟 : Precategory o′ ℓ′} {ℰ : Precategory o′′ ℓ′′}
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
