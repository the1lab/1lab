<!--
```agda
open import Cat.Displayed.Instances.Factorisations
open import Cat.Morphism.Factorisation.Algebraic
open import Cat.Instances.Shape.Interval
open import Cat.Monoidal.Diagram.Monoid
open import Cat.Functor.Naturality
open import Cat.Displayed.Section
open import Cat.Instances.Product
open import Cat.Diagram.Initial
open import Cat.Diagram.Monad
open import Cat.Monoidal.Base
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Functor.Bifunctor as Bi
import Cat.Reasoning

open Monoidal-category
open make-natural-iso
open Section
open Functor
open _=>s_
open _=>_
```
-->

```agda
module Cat.Monoidal.Instances.Factorisations {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
private Ff = Factorisations C
open Cat.Reasoning C
open Factorisation using (adjust ; annihilate ; collapse ; weave)
```
-->

# Monoidal structure on functorial factorisations

We show how to equip the category $\Ff{\cC}$ of [[functorial
factorisations]] on $\cC$ with the structure of a [[monoidal category]],
such that a [monoid] on some factorisation $F : \Ff{\cC}$ is precisely a
[[right weak factorisation structure]] on $\cC$.

[monoid]: Cat.Monoidal.Diagram.Monoid.html

The unit factorisation sends each $X \xto{f} Y$ to $X \xto{\id} X \xto{f} Y$.

```agda
Ff-unit : Factorisation C
Ff-unit .S₀ (_ , _ , f) = record
  { map = id
  ; out = f
  ; com = intror refl
  }
Ff-unit .S₁ f = record
  { sq₀ = id-comm-sym
  ; sq₁ = f .com
  }
Ff-unit .S-id    = ext refl
Ff-unit .S-∘ f g = ext refl
```

<details>
<summary>
We can easily calculate that the this unit factorisation is [[initial]].

```agda
Ff-unit-is-initial : is-initial (Factorisations C) Ff-unit
```
</summary>

```agda
Ff-unit-is-initial other = record where
  module o = Factorisation other
  centre = record
    { map = λ (X , Y , f) → record
      { map = o.λ→ f
      ; sq₀ = refl
      ; sq₁ = sym (o.factors f) ∙ introl refl
      }
    ; com = λ x y f → Interpolant-pathp (other .S₁ f .sq₀)
    }
  paths h = ext λ x y f →
    o.λ→ f          ≡⟨ h .sq₀ᶠᶠ f ⟩
    h .mapᶠᶠ f ∘ id ≡⟨ elimr refl ⟩
    h .mapᶠᶠ f      ∎
```

</details>

If $F, F' : \Ff{\cC}$ are a pair of factorisations, their tensor $F
\otimes F'$ sends a map $X \xto{F} Y$ to the composite
$$
X \xto{\lambda_f} M(f) \xto{\lambda'_{\rho_f}} M'(\rho_f) \xto{\rho'_{\rho_f}} Y
$$
with "middle object" $M'(\rho_f)$, i.e. everything but the last arrow is
the left factor.

```agda
module _ (F G : Factorisation C) where
  private
    module F = Factorisation F
    module G = Factorisation G

  _⊗ᶠᶠ_ : Factorisation C
  _⊗ᶠᶠ_ .S₀ (_ , _ , f) = record where
    mid = G.Mid (F.ρ→ f)
    map = G.λ→ (F.ρ→ f) ∘ F.λ→ f
    out = G.ρ→ (F.ρ→ f)
    com = sym (pulll (sym (G.factors _)) ∙ sym (F.factors _))

  _⊗ᶠᶠ_ .S₁ sq = record where
    open Interpolant (G .S₁ record { com = S₁ F sq .sq₁ })
      using (sq₁ ; map)
      renaming (sq₀ to α)

    sq₀ = sym (pulll (sym α) ∙ extendr (sym (F .S₁ sq .sq₀)))

  _⊗ᶠᶠ_ .S-id    = ext (G.annihilate (ext (F.annihilate refl ,ₚ refl)))
  _⊗ᶠᶠ_ .S-∘ f g = ext (G.expand     (ext (F.expand refl ,ₚ refl)))
```

<details>
<summary>Showing that this extends to a functor is slightly annoying,
but unsurprising.</summary>

```agda
Ff-tensor-functor : Functor (Ff ×ᶜ Ff) Ff
Ff-tensor-functor .F₀ (F , F') = F ⊗ᶠᶠ F'
Ff-tensor-functor .F₁ {X , Y} {X' , Y'} (f , g) .map (_ , _ , h) =
  let
    sq = record { com = f .sq₁ᶠᶠ h ∙ introl refl }
    h' = g .map (_ , _ , Factorisation.ρ→ X h)
  in record
    { map = Y' .S₁ sq .map ∘ h' .map
    ; sq₀ = sym
      ( pullr (pulll (sym (h' .sq₀)))
     ∙∙ pulll (pulll (sym (Y' .S₁ sq .sq₀))  ∙ elimr refl)
     ∙∙ pullr (sym (f .sq₀ᶠᶠ h))
      ∙ intror refl)
    ; sq₁ = pulll (Y' .S₁ sq .sq₁)
          ∙ pullr (h' .sq₁ ∙ eliml refl)
    }

Ff-tensor-functor .F₁ {X , Y} {X' , Y'} (f , g) .com α β h = Interpolant-pathp $
    pullr (g .comᶠᶠ _)
  ∙ extendl (weave Y' (ext (f .comᶠᶠ _ ,ₚ id-comm-sym)))

Ff-tensor-functor .F-id {_ , Y} = ext λ x y h → elimr refl ∙ annihilate Y (ext refl)

Ff-tensor-functor .F-∘ {X , X'} {Y , Y'} {Z , Z'} f g = ext λ x y h →
    pulll (sym (f .snd .comᶠᶠ _)) ∙∙ pullr (sym (g .snd .comᶠᶠ _)) ∙∙ sym
    (ap₂ _∘_ (sym (f .snd .comᶠᶠ _)) (sym (g .snd .comᶠᶠ _))
  ∙∙ pullr (extendl (sym (g .snd .comᶠᶠ _)))
  ∙∙ ap₂ _∘_ refl (ap₂ _∘_ refl (collapse X' (ext (refl ,ₚ idl id)))))
```

</details>

The following snippet, showing part of the construction of the
associator, is typical of the construction of the monoidal structure on
$\Ff{\cC}$: every *component* of the natural isomorphisms is the
identity, but we end up having to shuffle quite a few identity morphisms
around.

```agda
private
  assc : Associator-for {O = ⊤} (λ _ _ → Ff) Ff-tensor-functor
  assc = to-natural-iso mk where
    mk : make-natural-iso (compose-assocˡ Ff-tensor-functor) _
    mk .eta X .map x = record
      { map = id
      ; sq₀ = elimr refl ∙∙ pullr refl ∙∙ introl refl
      ; sq₁ = id-comm
      }
    mk .inv X .map x = record
      { map = id
      ; sq₀ = elimr refl ∙∙ pulll refl ∙∙ introl refl
      ; sq₁ = id-comm
      }
```

<!--
```agda
    mk .eta X .com x y f = Interpolant-pathp id-comm-sym
    mk .inv X .com x y f = Interpolant-pathp id-comm-sym
    mk .eta∘inv x = ext λ x y f → idl id
    mk .inv∘eta x = ext λ x y f → idl id
    mk .natural (X , X') (Y , Y') f = ext λ x y h →
         pullr (elimr refl)
      ∙∙ pulll (Factorisation.collapse (Y' .snd) (ext (refl ,ₚ idl id)))
      ∙∙ introl refl
```
-->

<details>
<summary>
```agda
Ff-monoidal : Monoidal-category Ff
Ff-monoidal .-⊗-        = Ff-tensor-functor
Ff-monoidal .Unit       = Ff-unit
```

We thus choose not to comment much on the construction of the unitors
and proof of the triangle and pentagon identities.
</summary>

```agda
Ff-monoidal .unitor-l   = to-natural-iso mk where
  mk : make-natural-iso (Id {C = Ff}) (Bi.Right Ff-tensor-functor Ff-unit)
  mk .eta X .map _ = record { sq₀ = cancelr (idl id) ∙ introl refl ; sq₁ = id-comm }
  mk .inv X .map _ = record { sq₀ = introl refl                    ; sq₁ = id-comm }

  mk .eta X .com x y f = Interpolant-pathp $
    eliml refl ∙∙ adjust X (ext refl) ∙∙ intror refl
  mk .inv X .com x y f = Interpolant-pathp $
    eliml refl ∙∙ adjust X (ext refl) ∙∙ intror refl

  mk .eta∘inv x     = ext λ x y f → idl id
  mk .inv∘eta x     = ext λ x y f → idl id
  mk .natural X Y f = ext λ x y g →
    elimr refl ∙∙ eliml (annihilate Y (ext refl)) ∙∙ introl refl

Ff-monoidal .unitor-r   = to-natural-iso mk where
  mk : make-natural-iso (Id {C = Ff}) (Bi.Left Ff-tensor-functor Ff-unit)
  mk .eta X .map _ = record { sq₀ = elimr refl                     ; sq₁ = id-comm }
  mk .inv X .map _ = record { sq₀ = elimr refl ∙ insertl (idl id)  ; sq₁ = id-comm }

  mk .eta X .com x y f = Interpolant-pathp $
    eliml refl ∙∙ Factorisation.adjust X (ext refl) ∙∙ intror refl
  mk .inv X .com x y f = Interpolant-pathp $
    eliml refl ∙∙ Factorisation.adjust X (ext refl) ∙∙ intror refl

  mk .eta∘inv x     = ext λ x y f → idl id
  mk .inv∘eta x     = ext λ x y f → idl id
  mk .natural X Y f = ext λ x y g → cancelr (idl id) ∙ introl refl

Ff-monoidal .associator = assc
Ff-monoidal .triangle   = ext λ x y f → pullr (idl id)
Ff-monoidal .pentagon {B = B} {C = C} {D = D} = ext λ x y f →
  pullr
    (  cancell (idl id)
    ∙∙ elimr refl
    ∙∙ annihilate D (ext (annihilate C (ext (annihilate B (ext refl) ,ₚ refl)) ,ₚ refl)))
  ∙ ap (_∘ id) (annihilate D (ext refl))
```

</details>

# Monoids on functorial factorisations

<!--
```agda
module _ {F : Factorisation C} (m : Monoid-on Ff-monoidal F) where
  private
    module m = Monoid-on m
    module F = Factorisation F
  open is-monad
  open Rwfs-on
```
-->

We will now show that a monoid (on some functorial factorisation $F :
\Ff{\cC}$) in this monoidal structure can be tweaked into a [[right weak
factorisation structure]] on $F$. First, note that the components of the
monoidal multiplication on $F$ can be reassembled into a *monadic*
multiplication on the right factor.

```agda
  private
    monoid→mult : F.R F∘ F.R => F.R
    monoid→mult .η (X , Y , f) = record where
      top = m.μ .mapᶠᶠ f
      bot = id
      com = m.μ .sq₁ᶠᶠ f ∙ introl refl
    monoid→mult .is-natural x y f = ext $
      ap₂ _∘_ refl (F.adjust (ext refl)) ∙ m.μ .comᶠᶠ _ ,ₚ
      id-comm-sym
```

<details>
<summary>For ease of calculation below, we can also extract a *unit* map
from the monoid structure on $F$.

```agda
    monoid→unit        : Id => F.R
    monoid-unit-agrees : monoid→unit ≡ F.R-η
```

Of course, what we need to show is that the monoid multiplication makes
the [[right factor functor]] $R$, *with its canonical unit* $\eta$, into
a monad. However, that the unit derived from the monoid agrees with
$\eta$ is an easy corollary of initiality for the unit factorisation.
</summary>

```agda
    monoid→unit .η (X , Y , f) = record
      { top = m.η .mapᶠᶠ f
      ; bot = id
      ; com = m.η .sq₁ᶠᶠ f ∙ introl refl
      }
    monoid→unit .is-natural x y f = ext (m.η .comᶠᶠ _ ,ₚ id-comm-sym)

    monoid-unit-agrees = ext λ (x , y , f) →
        intror refl
      ∙ sym (m.η .sq₀ᶠᶠ f) ,ₚ refl
```

</details>

The calculation that these two are a monad on $R$ is a straightforward
repackaging of the corresponding monoid laws.

```agda
    monoid-mult-is-monad : is-monad monoid→unit monoid→mult
    monoid-mult-is-monad .μ-unitr {X , Y , f} = ext $
         ap₂ _∘_ refl (F.adjust (ext refl) ∙ intror refl)
       ∙ apd (λ i x → x .mapᶠᶠ f) m.μ-unitl
      ,ₚ idl id

    monoid-mult-is-monad .μ-unitl {X , Y , f} = ext $
         ap₂ _∘_ refl (introl (F.annihilate (ext refl)))
       ∙ apd (λ i x → x .mapᶠᶠ f) m.μ-unitr
      ,ₚ idl id

    monoid-mult-is-monad .μ-assoc {X , Y , f} = ext $
         ap₂ _∘_ refl (F.adjust (ext (refl ,ₚ refl)) ∙∙ intror refl ∙∙ intror refl)
      ∙∙ apd (λ i x → x .mapᶠᶠ f) (sym m.μ-assoc)
      ∙∙ ap₂ _∘_ refl (eliml (F.annihilate (ext refl)))
      ,ₚ refl
```

We can then transport this along the proof that the units agree to
extend $(R, \eta)$ to a monad. This transport will not compute very
nicely, but since "being a monad" is a proposition once the unit and
multiplication are fixed, this does not matter.

```agda
  monoid-on→rwfs-on : Rwfs-on F
  monoid-on→rwfs-on .R-μ     = monoid→mult
  monoid-on→rwfs-on .R-monad = done where abstract
    done : is-monad F.R-η monoid→mult
    done = subst
      (λ e → is-monad e monoid→mult) monoid-unit-agrees
      monoid-mult-is-monad
```
