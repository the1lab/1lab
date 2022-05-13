```agda
open import Cat.Functor.Adjoint.Continuous
open import Cat.Instances.Functor.Duality
open import Cat.Diagram.Colimit.Base
open import Cat.Functor.Equivalence
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Equaliser
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Diagram.Duals
open import Cat.Prelude

module Cat.Instances.Functor.Limits where
```

# Limits in functor categories

Let $\ca{C}$ be a category admitting $\ca{D}$-shaped limits. Then the
functor category $[\ca{E},\ca{S}]$, for $\ca{E}$ _any_ category, also
admits $\ca{D}$-shaped limits. In particular, if $\ca{C}$ is
$(\iota,\kappa)$-complete, then so is $[\ca{E},\ca{C}]$.

```agda
module _
  {o₁ ℓ₁} {C : Precategory o₁ ℓ₁}
  {o₂ ℓ₂} {D : Precategory o₂ ℓ₂}
  {o₃ ℓ₃} {E : Precategory o₃ ℓ₃}
  (has-D-lims : ∀ (F : Functor D C) → Limit F)
  (F : Functor D Cat[ E , C ])
  where
```

<!--
```agda
  open Cone-hom
  open Terminal
  open Functor
  open Cone
  open _=>_

  import Cat.Reasoning C as C
  import Cat.Reasoning D as D
  import Cat.Reasoning E as E

  private
    module F = Functor F
```
-->

Let $F : \ca{D} \to [\ca{E},\ca{C}]$ be a diagram, and suppose $\ca{C}$
admits limits of $\ca{D}$-shaped diagrams; We wish to compute the limit
$\lim F$. First, observe that we can `Uncurry`{.Agda} $F$ to obtain a
functor $F' : \ca{D} \times \ca{E} \to \ca{C}$; By fixing the value of
the $\ca{E}$ coordinate (say, to $x$), we obtain a family $F(-, x)$ of
$\ca{D}$-shaped diagrams in $\ca{C}$, which, by assumption, all have
limits.

```agda
    F-uncurried : Functor (D ×ᶜ E) C
    F-uncurried = Uncurry {C = D} {D = E} {E = C} F

    import Cat.Functor.Bifunctor {C = D} {D = E} {E = C} F-uncurried as F′
```

Let us call the limit of $F(-, x)$ --- taken in $\ca{C}$ ---
`lim-for`{.Agda}, and similarly the unique, "terminating" cone
homomorphism $K \to \lim F(-, x)$ will be called `!-for`{.Agda}.

```agda
    lim-for : ∀ x → _
    lim-for x = has-D-lims (F′.Left x) .top

    !-for : ∀ {x} K → _
    !-for {x} K = has-D-lims (F′.Left x) .has⊤ K .centre

    !-for-unique : ∀ {x} {K} h → !-for K ≡ h
    !-for-unique {x} {K} = has-D-lims (F′.Left x) .has⊤ K .paths
```

The two _fundamental_ --- and very similar looking! --- constructions
are `Lift-cone`{.Agda} and `map-cone`{.Agda} below. `Lift-cone`{.Agda}
lets us take a component of a cone for $F$ --- in the functor category
--- into a cone for $F(y)$, in $\ca{C}$. Furthermore, at the same time
as we perform this lifting, we can "adjust" the cone by a map $(x
\xto{f} y) \in \ca{E}$.

```agda
  Lift-cone : ∀ {x y} (K : Cone F) (f : E.Hom x y) → Cone (F′.Left y)
  Lift-cone {x} {y} K f .apex = K .apex .F₀ x
  Lift-cone {x} {y} K f .ψ z  = F′.second f C.∘ K .ψ z .η _
  Lift-cone {x} {y} K g .commutes f =
    F′.first f C.∘ F′.second g C.∘ K .ψ _ .η x ≡⟨ C.extendl F′.first∘second ⟩
    F′.second g C.∘ F′.first f C.∘ K .ψ _ .η x ≡⟨ ap (F′.second _ C.∘_) (ap₂ C._∘_ (C.elimr (F-id (F.₀ _))) refl ∙ ap (λ e → e .η x) (K .commutes f)) ⟩
    F′.second g C.∘ K .ψ _ .η x                ∎
```

The function `map-cone`{.Agda} is `Lift-cone`{.Agda}, but specialised to
the case where $K = \lim F(-, x)$ is the `lim-for`{.Agda} a particular
point in $\ca{E}$.

```agda
  map-cone : ∀ {x y} (f : E.Hom x y) → Cone (F′.Left y)
  map-cone {x} f .apex       = lim-for x .apex
  map-cone {x} f .ψ z        = F′.second f C.∘ lim-for x .ψ z
  map-cone {x} f .commutes g =
    F′.first g C.∘ F′.second f C.∘ lim-for x .ψ _ ≡⟨ C.extendl F′.first∘second ⟩
    F′.second f C.∘ F′.first g C.∘ lim-for x .ψ _ ≡⟨ ap (F′.second _ C.∘_) (lim-for x .commutes _) ⟩
    F′.second f C.∘ lim-for x .ψ _                ∎
```

### The cone

We are now ready to build a universal cone over $F$, in the category $[
\ca{E}, \ca{C} ]$, meaning the apex will be given by a functor $A : \ca{E}
\to \ca{C}$. Using the fact that $\ca{C}$ was assumed to have
$\ca{D}$-shaped limits, `the-apex`{.Agda} will be given by $x \mapsto
\lim F(-, x)$. Similarly, the choice of map is essentially unique: we
must map $\lim F(-, x) \to \lim F(-, y)$, but the space of maps $X \to
\lim F(-, y)$ is contractible.

```agda
  functor-cone : Cone F
  functor-cone .apex  = the-apex where
    the-apex : Functor E C
    the-apex .F₀ x = lim-for x .apex
    the-apex .F₁ {x} {y} f = !-for (map-cone f) .hom
```

<details>
<summary> We use that contractibility of mapping spaces to prove
`the-apex`{.Agda} is actually a functor. </summary>

```agda
    the-apex .F-id = ap hom (!-for-unique map) where
      map : Cone-hom _ _ _
      map .hom = C.id
      map .commutes _ = C.idr _ ∙ C.introl F′.second-id
    the-apex .F-∘ {x} {y} {z} f g = ap hom (!-for-unique map)
      where
        map : Cone-hom _ _ _
        map .hom = the-apex .F₁ f C.∘ the-apex .F₁ g
        map .commutes o =
          (lim-for z .ψ o C.∘ _ C.∘ _)                               ≡⟨ C.extendl (!-for (map-cone f) .commutes _) ⟩
          (F′.second f C.∘ lim-for y .ψ o C.∘ _)                     ≡⟨ ap (F′.second f C.∘_) (!-for (map-cone g) .commutes _) ⟩
          (F′.second f C.∘ F′.second g C.∘ lim-for x .ψ o)           ≡⟨ C.pulll (sym F′.second∘second) ⟩
          (F′.second (f E.∘ g) C.∘ has-D-lims (F′.Left x) .top .ψ o) ∎
```

</details>

We must now give the construction of the actual cone, i.e. the natural
$\psi'_x$ transformations $A \To F(x)$. The natural transformations are
defined componentwise by taking $(\psi'_x)_y$ to be the map underlying
the cone homomorphism $\psi_x : (\lim F(-,y)) \to F(x)(y)$; This is
natural because $\psi$ is a family of cone homomorphisms, and the cone
commutes since each limiting cone $\lim F(-,x)$ is indeed a cone.

```agda
  functor-cone .ψ x .η y              = lim-for y .ψ x
  functor-cone .ψ x .is-natural y z f =
    !-for (map-cone f) .commutes _ ∙ ap₂ C._∘_ (C.eliml (λ i → F.F-id i .η z)) refl
  functor-cone .commutes f = Nat-path λ x →
      ap₂ C._∘_ (C.intror (F-id (F.₀ _))) refl ∙ lim-for _ .commutes f
```

### The maps

For the `functor-cone`{.Agda} --- our candidate for $\lim F$ --- to be
limiting, we must, given some other cone $K$, find a unique cone
homomorphism $K \to \lim F$. We'll be fine, though: We can (using
`Lift-cone`{.Agda}) _explode_ $K$ into a bunch of cones $K_x$, each lying
over $F(-,x)$, and use the universal property of $\lim F(-,x)$ to find
cone homs $K_x \to \lim F(-,x)$. Assuming these maps assemble to a
natural transformation $K_x \to \lim F$, we can show they commute with
everything in sight:

```agda
  functor-! : ∀ K → Cone-hom F K functor-cone
  functor-! K = ch where
    map : ∀ x → Cone-hom (F′.Left x) (Lift-cone K E.id) (lim-for x)
    map x = !-for (Lift-cone K E.id)

    ch : Cone-hom F K functor-cone
    ch .hom .η x = map _ .hom
    ch .commutes _ = Nat-path λ x → map _ .commutes _ ∙ C.eliml F′.second-id
```

The hard part, then, is showing that this is a natural transformation.
We'll do this in a roundabout way: We'll show that both composites in
the naturality square inhabit the same _contractible_ space of cone
homomorphisms, namely that of $\id{Lift-cone}(K,f) \to \lim F(-,y)$,
and thus conclude that they are unique. This isn't too hard, but it is
quite tedious:

```agda
    ch .hom .is-natural x y f =
      map y .hom C.∘ K .apex .F₁ f            ≡⟨ (λ i → is-contr→is-prop (has-D-lims (F′.Left y) .has⊤ (Lift-cone K f)) h1 h2 i .hom) ⟩
      !-for (map-cone f) .hom C.∘ map x .hom  ∎
      where
        h1 : Cone-hom (F′.Left y) (Lift-cone K f) (lim-for y)
        h1 .hom = map y .hom C.∘ K .apex .F₁ f
        h1 .commutes o =
          lim-for y .ψ o C.∘ map y .hom C.∘ K .apex .F₁ f  ≡⟨ C.pulll (map y .commutes _ ∙ C.eliml F′.second-id) ⟩
          K .ψ _ .η _ C.∘ K .apex .F₁ f                    ≡⟨ K .ψ _ .is-natural _ _ _ ⟩
          F₁ (F.₀ o) f C.∘ K .ψ o .η x                     ≡⟨ ap (C._∘ K .ψ o .η x) (C.introl (ap (λ e → e .η y) (F-id F))) ⟩
          F′.second f C.∘ K .ψ o .η x                      ∎

        h2 : Cone-hom (F′.Left y) (Lift-cone K f) (lim-for y)
        h2 .hom = has-D-lims (F′.Left y) .has⊤ (map-cone f) .centre .hom C.∘ map x .hom
        h2 .commutes o =
          lim-for y .ψ o C.∘ !-for (map-cone f) .hom C.∘ map x .hom  ≡⟨ C.pulll (has-D-lims (F′.Left y) .has⊤ (map-cone f) .centre .commutes _) ⟩
          (F′.second f C.∘ lim-for x .ψ o) C.∘ map x .hom            ≡⟨ C.pullr (map x .commutes _ ∙ C.eliml F′.second-id) ⟩
          F′.second f C.∘ K .ψ o .η x                                ∎
```

Since we built the natural transformation underlying `functor-!`{.Agda}
out of the unique maps `!-for`{.Agda}, we can appeal to `that
uniqueness`{.Agda ident=!-for-unique} here to conclude that
`functor-!`{.Agda} is itself unique, showing that we put together a
limit $\lim F$.

```agda
  functor-!-unique : ∀ {K} (h : Cone-hom F K functor-cone) → functor-! K ≡ h
  functor-!-unique h = Cone-hom-path _ (Nat-path λ x → ap hom (!-for-unique hom'))
    where
      hom' : ∀ {x} → Cone-hom (F′.Left x) _ _
      hom' {x} .hom = h .hom .η x
      hom' {x} .commutes o = ap (λ e → e .η _) (h .commutes o) ∙ C.introl F′.second-id

  functor-limit : Limit F
  functor-limit .top            = functor-cone
  functor-limit .has⊤ x .centre = functor-! x
  functor-limit .has⊤ x .paths  = functor-!-unique
```

As a corollary, if $\ca{D}$ is an $(o,\ell)$-complete category, then so
is $[\ca{C},\ca{D}]$.

```agda
Functor-cat-is-complete :
  ∀ {o ℓ} {o₁ ℓ₁} {C : Precategory o₁ ℓ₁} {o₂ ℓ₂} {D : Precategory o₂ ℓ₂}
  → is-complete o ℓ D → is-complete o ℓ Cat[ C , D ]
Functor-cat-is-complete D-complete = functor-limit D-complete
```

<!--
```agda
module _
  {o₁ ℓ₁} {C : Precategory o₁ ℓ₁}
  {o₂ ℓ₂} {D : Precategory o₂ ℓ₂}
  {o₃ ℓ₃} {E : Precategory o₃ ℓ₃}
  (has-D-colims : ∀ (F : Functor D C) → Colimit F)
  (F : Functor D Cat[ E , C ])
  where

  functor-colimit : Colimit F
  functor-colimit = colim where
    F′ : Functor (D ^op) Cat[ E ^op , C ^op ]
    F′ = op-functor→ F∘ Functor.op F

    F′-lim : Limit F′
    F′-lim = functor-limit
      (λ f → subst Limit F^op^op≡F (Colimit→Co-limit _ (has-D-colims (Functor.op f))))
      F′

    LF′′ : Limit (op-functor← {C = E} {D = C} F∘ (op-functor→ F∘ Functor.op F))
    LF′′ = right-adjoint-limit (is-equivalence.F⊣F⁻¹ op-functor-is-equiv) F′-lim

    LFop : Limit (Functor.op F)
    LFop = subst Limit (F∘-assoc ∙ ap (_F∘ Functor.op F) op-functor←→ ∙ F∘-idl) LF′′

    colim : Colimit F
    colim = Co-limit→Colimit _ LFop

Functor-cat-is-cocomplete :
  ∀ {o ℓ} {o₁ ℓ₁} {C : Precategory o₁ ℓ₁} {o₂ ℓ₂} {D : Precategory o₂ ℓ₂}
  → is-cocomplete o ℓ D → is-cocomplete o ℓ Cat[ C , D ]
Functor-cat-is-cocomplete D-cocomplete = functor-colimit D-cocomplete
```
-->
