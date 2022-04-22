```agda
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Terminal
open import Cat.Functor.Base
open import Cat.Morphism
open import Cat.Prelude hiding (J)

module Cat.Functor.Conservative where
```

<!--
```agda
private variable
  o h o₁ h₁ : Level
  C D J : Precategory o h
open Precategory
open Functor
```
-->

# Conservative Functors

We say a functor is _conservative_ if it reflects isomorphisms. More concretely,
if $f : A \to B$ is some morphism $\ca{C}$, and if $F(f)$ is an iso in $\ca{D}$,
then $f$ must have already been an iso in $\ca{C}$!

```agda
is-conservative : Functor C D → Type _
is-conservative {C = C} {D = D} F =
  ∀ {A B} {f : C .Hom A B}
  → is-invertible D (F .F₁ f) → is-invertible C f
```

As a general fact, conservative functors reflect limits that they preserve
(given those limits exist in the first place!).

The rough proof sketch is as follows: Let $K$ be some cone in $C$ such that
$F(K)$ is a limit in $D$, and $L$ a limit in $C$ of the same diagram.
By the universal property of $L$, there exists a map $\eta$ from the apex of $K$
to the apex of $L$ in $C$. Furthermore, as $F(K)$ is a limit in $D$, $F(\eta)$
becomes an isomorphism in $D$. However, $F$ is conservative, which implies that
$\eta$ was an isomorphism in $C$ all along! This means that $K$ must be a limit
in $C$ as well (see `apex-iso→is-limit`{.Agda}).

```agda
module _ {F : Functor C D} (conservative : is-conservative F) where
  conservative-reflects-limits : ∀ {Dia : Functor J C} → (L : Limit Dia)
                               → (∀ (K : Cone Dia) → Preserves-limit F K)
                               → (∀ (K : Cone Dia) → Reflects-limit F K)
  conservative-reflects-limits {Dia = Dia} L-lim preserves K limits =
    apex-iso→is-limit Dia K L-lim
      $ conservative
      $ subst (λ ϕ → is-invertible D ϕ) F-preserves-universal
      $ Cone-invertible→apex-invertible (F F∘ Dia)
      $ !-invertible (Cones (F F∘ Dia)) F∘L-lim K-lim
    where
      F∘L-lim : Limit (F F∘ Dia)
      F∘L-lim .Terminal.top = F-map-cone F (Terminal.top L-lim)
      F∘L-lim .Terminal.has⊤ = preserves (Terminal.top L-lim) (Terminal.has⊤ L-lim)

      K-lim : Limit (F F∘ Dia)
      K-lim .Terminal.top = F-map-cone F K
      K-lim .Terminal.has⊤ = limits

      module L-lim = Terminal L-lim
      module F∘L-lim = Terminal F∘L-lim
      open Cone-hom

      F-preserves-universal
        : hom F∘L-lim.! ≡ F .F₁ (hom {x = K} L-lim.!)
      F-preserves-universal =
        hom F∘L-lim.! ≡⟨ ap hom (F∘L-lim.!-unique (F-map-cone-hom F L-lim.!)) ⟩
        hom (F-map-cone-hom F (Terminal.! L-lim)) ≡⟨⟩
        F .F₁ (hom L-lim.!) ∎
```
