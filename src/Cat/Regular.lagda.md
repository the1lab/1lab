<!--
```agda
open import Cat.Diagram.Coequaliser.RegularEpi
open import Cat.Diagram.Pullback.Properties
open import Cat.Morphism.Factorisation
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Coequaliser
open import Cat.Morphism.StrongEpi
open import Cat.Diagram.Pullback
open import Cat.Diagram.Product
open import Cat.Prelude

open import Data.Power

import Cat.Functor.Bifunctor as Bifunctor
import Cat.Reasoning as Cr
```
-->

<<<<<<< HEAD
```agda
=======
open Functor

>>>>>>> 0b184fa (wip: regular category refactor)
module Cat.Regular where
```

# Regular categories

A **regular category** is a category with [pullback]-stable [image]
factorizations. To define regular categories, we use the theory of
[orthogonal morphisms], specifically [strong epimorphisms]: A regular
category is one where every morphism factors as a strong epimorphism
followed by a monomorphism, and strong epimorphisms are stable under
pullback.

[pullback]: Cat.Diagram.Pullback.html
[image]: Cat.Diagram.Image.html
[regular epi]: Cat.Diagram.Coequaliser.RegularEpi.html
[orthogonal morphisms]: Cat.Morphism.Orthogonal.html
[strong epimorphisms]: Cat.Morphism.StrongEpi.html

At face value, it's a bit weird to take the definition of regular
categories to talk about strong, rather than _regular_, epimorphisms.
But it turns out that strong epimorphisms correspond pretty directly to
the idea of an image factorisation, or at least much _more_ directly
than regular epimorphisms do. As we shall see, in a regular category,
every strong epimorphism is regular.

<!--
```agda
module _ {o ℓ} (𝒞 : Precategory o ℓ) where
  private module C = Cr 𝒞

  StrongEpi : ∀ {a b} → C.Hom a b → Ω
  StrongEpi x = elΩ (is-strong-epi 𝒞 x)

  Mono : ∀ {a b} → C.Hom a b → Ω
  Mono x = elΩ (C.is-monic x)
```
-->

```agda
  record is-regular : Type (o ⊔ ℓ) where
    field
      factor : ∀ {a b} (f : C.Hom a b) → Factorisation 𝒞 StrongEpi Mono f
      stable : is-pullback-stable 𝒞 (is-strong-epi 𝒞)
      has-is-lex : Finitely-complete 𝒞

    module factor {a b} (f : C.Hom a b) = Factorisation (factor f)
    module lex = Finitely-complete has-is-lex
```

We also introduce some more palatable names for the components of the
provided factorisations: Letting $f : A \to B$ be a map and $A \epi X
\mono B$ its image factorisation, we refer to $X$ as $\im(f)$, to $A
\epi X$ as `a↠im[_]`{.Agda}, and $X \mono B$ as `im[_]↪b`{.Agda}. These
latter two names have a placeholder for the morphism we are factoring.

```agda
    im[_] : ∀ {a b} (f : C.Hom a b) → C.Ob
    im[ f ] = factor f .Factorisation.mediating

    im[_]↪b : ∀ {a b} (f : C.Hom a b) → im[ f ] C.↪ b
    im[ f ]↪b = record { monic = out! (factor f .Factorisation.forget∈M) }

    a↠im[_] : ∀ {a b} (f : C.Hom a b) → C.Hom a im[ f ]
    a↠im[ f ] = factor f .Factorisation.mediate
```

<!--
```agda
  module _ (r : is-regular) where
    private module r = is-regular r
    open Cartesian 𝒞 r.lex.products
    open C

    mono→im-iso
      : ∀ {a b} (f : C.Hom a b)
      → C.is-monic f
      → C.is-invertible r.a↠im[ f ]
    mono→im-iso f x = res where
      open Factorisation
      rem₁ : f ≡ r.im[ f ]↪b .C.mor C.∘ r.a↠im[ f ]
      rem₁ = r.factor f .factors

      p = out! (r.factor f .mediate∈E) .snd (record { monic = x })
        (sym (r.factor f .factors) ∙ sym (C.idr _))
      res = C.make-invertible (p .centre .fst)
        (out! (r.factor f .mediate∈E) .fst _ _
          (C.pullr (p .centre .snd .fst) ∙ C.id-comm))
        (p .centre .snd .fst)
```
-->

# Strong epis are regular

This section formalises the proof of A1.3.4 from [@Elephant], which says
that every strong epimorphism^[Note: Johnstone prefers to work with
"covers" instead, which in our lingo are _extremal_ epimorphism. In a
finitely complete category, strong and extremal epimorphisms coincide]
in a regular category is regular. Actually, we'll show that every strong
epimorphism in a regular category is **effective**: it's the coequaliser
of its kernel pair.

```agda
  -- Johnstone, A.1.3.4
  module _ (r : is-regular) {A B} (f : C.Hom A B) (is-s : is-strong-epi 𝒞 f) where
    private
      module r = is-regular r
      module kp = Pullback (r.lex.pullbacks f f)
        renaming (apex to R ; p₁ to a ; p₂ to b)
```

<!--
```agda
      open kp using (R ; a ; b ; square)
      open Cartesian 𝒞 r.lex.products
      open C
```
-->

For a strong epimorphism $f : A \epi B$, start by pulling $f$ back along
itself to form the kernel pair $(a, b) : R \tto A$. We want to show that
$f$ coequalises $a$ and $b$, which means that any morphism $c : A \to C$
satisfying $ca = cb$ should have a unique factorisation through $f$. So,
quantify over such morphisms and let's get started.

```agda
    private module Make {C} {c : C.Hom A C} (w : c C.∘ a ≡ c C.∘ b) where
```

We start by calculating the image factorisation of $(f,c) : A \to B
\times C$,

$$
A \xepi{d} D \xmono {(g, h)} B \times C \text{.}
$$



```agda
      dgh : Factorisation 𝒞 StrongEpi Mono ⟨ f , c ⟩
      dgh = r.factor ⟨ f , c ⟩
      module dgh = Factorisation dgh
        renaming (mediating to D ; forget to gh ; mediate to d)
      open dgh using (D ; d ; gh)

      g : C.Hom D B
      g = π₁ C.∘ gh

      h : C.Hom D C
      h = π₂ C.∘ gh
```

Following Johnstone, we show that $g$ is an isomorphism, so that
$hg^{-1}$ is the factorisation we're looking for.^[Johnstone says it's
_clearly_ unique, but the tiny calculation is included at the end of the
proof since it wasn't clear to me] Since $f$ is an extremal epimorphism,
any monomorphism through which it factors must be an iso. And since we have

$$
f = \pi_1(f,c) = \pi_1(g,h)d = gd\text{,}
$$

it will suffice to show that $g$ is a monomorphism. So assume you're
given $k, l : E \to D$ with $gk = gl$; Let's show that $k = l$.

```agda
      g-monic : C.is-monic g
      g-monic {e} k l w′ = out! dgh.forget∈M _ _ rem₈ where
        d×d = ×-functor .F₁ (d , d)
        module pb = Pullback (r.lex.pullbacks ⟨ k , l ⟩ d×d)
          renaming (p₁ to p ; apex to P ; p₂ to mn ; square to sq′-)
        open pb using (p ; P ; mn ; sq′-)
        m = π₁ C.∘ mn
        n = π₂ C.∘ mn
        sq′ : ⟨ k C.∘ p , l C.∘ p ⟩ ≡ ⟨ d C.∘ m , d C.∘ n ⟩
        sq′ = sym (⟨⟩∘ _) ∙ sq′- ∙ ⟨⟩-unique _ (C.pulll π₁∘⟨⟩ ∙ C.pullr refl)
                                               (C.pulll π₂∘⟨⟩ ∙ C.pullr refl)

        q : C.Hom P R
        q = kp.limiting $
          f ∘ m         ≡⟨ C.pushl (extend-π₁ dgh.factors ∙ C.pulll refl) ⟩
          g ∘ d ∘ m     ≡˘⟨ refl⟩∘⟨ by-π₁ sq′ ⟩
          g ∘ k ∘ p     ≡⟨ C.extendl w′ ⟩
          g ∘ l ∘ p     ≡⟨ refl⟩∘⟨ by-π₂ sq′ ⟩
          g ∘ d ∘ n     ≡˘⟨ C.pushl (extend-π₁ dgh.factors ∙ C.pulll refl) ⟩
          f ∘ n         ∎

        rem₁ = h ∘ k ∘ p     ≡⟨ refl⟩∘⟨ by-π₁ sq′ ⟩
               h ∘ d ∘ m     ≡⟨ pulll (pullr (sym dgh.factors) ∙ π₂∘⟨⟩) ⟩
               c ∘ m         ≡˘⟨ refl⟩∘⟨ kp.p₁∘limiting ⟩
               c ∘ a ∘ q     ≡⟨ extendl w ⟩
               c ∘ b ∘ q     ≡⟨ refl⟩∘⟨ kp.p₂∘limiting ⟩
               c ∘ n         ≡˘⟨ pulll (pullr (sym dgh.factors) ∙ π₂∘⟨⟩) ⟩
               h ∘ d ∘ n     ≡˘⟨ refl⟩∘⟨ by-π₂ sq′ ⟩
               h ∘ l ∘ p     ∎

        open is-pullback

        rem₂ : is-strong-epi 𝒞 (×-functor .F₁ (d , id))
        rem₂ = r.stable d π₁ {p2 = π₁} (out! dgh.mediate∈E) λ where
          .square → π₁∘⟨⟩
          .limiting {p₁' = p₁'} {p₂'} p → ⟨ p₂' , π₂ ∘ p₁' ⟩
          .p₁∘limiting {p₁' = p₁'} {p₂'} {p = p} → ⟨⟩∘ _
            ·· ap₂ ⟨_,_⟩ (pullr π₁∘⟨⟩ ∙ sym p) (pullr π₂∘⟨⟩ ∙ idl _)
            ·· sym (⟨⟩-unique _ refl refl)
          .p₂∘limiting → π₁∘⟨⟩
          .unique {p = p} {lim'} q r → ⟨⟩-unique _ r $ sym $
            ap (π₂ ∘_) (sym q) ∙ pulll π₂∘⟨⟩ ∙ ap (_∘ lim') (idl _)

        rem₃ : is-strong-epi 𝒞 (×-functor .F₁ (id , d))
        rem₃ = r.stable d π₂ {p2 = π₂} (out! dgh.mediate∈E) λ where
          .square → π₂∘⟨⟩
          .limiting {p₁' = p₁'} {p₂'} p → ⟨ π₁ ∘ p₁' , p₂' ⟩
          .p₁∘limiting {p = p} → ⟨⟩∘ _
            ·· ap₂ ⟨_,_⟩ (pullr π₁∘⟨⟩ ∙ idl _) (pullr π₂∘⟨⟩)
            ·· sym (⟨⟩-unique _ refl p)
          .p₂∘limiting → π₂∘⟨⟩
          .unique {p = p} {lim'} q r → ⟨⟩-unique _
            (sym (ap (π₁ ∘_) (sym q) ∙ pulll π₁∘⟨⟩ ∙ ap (_∘ lim') (idl _)))
            r

        rem₄ = sym (×-functor .F-∘ _ _)
             ∙ ap (×-functor .F₁) (Σ-pathp (idl _) (idr _))

        rem₅ : is-strong-epi 𝒞 d×d
        rem₅ = subst (is-strong-epi 𝒞) rem₄ (strong-epi-compose 𝒞 _ _ rem₂ rem₃)

        rem₆ : is-strong-epi 𝒞 p
        rem₆ = r.stable _ _ rem₅ pb.has-is-pb

        rem₇ : h ∘ k ≡ h ∘ l
        rem₇ = rem₆ .fst _ _ $
          (h ∘ k) ∘ p   ≡⟨ sym (assoc _ _ _) ∙ rem₁ ⟩
          h ∘ l ∘ p     ≡⟨ pulll refl ⟩
          (h ∘ l) ∘ p   ∎

        rem₈ : gh C.∘ k ≡ gh C.∘ l
        rem₈ =
          gh ∘ k              ≡⟨ ⟨⟩-unique _ refl refl ⟩∘⟨refl ⟩
          ⟨ g , h ⟩ ∘ k       ≡⟨ ⟨⟩∘ _ ⟩
          ⟨ g ∘ k , h ∘ k ⟩   ≡⟨ ap₂ ⟨_,_⟩ w′ rem₇ ⟩
          ⟨ g ∘ l , h ∘ l ⟩   ≡˘⟨ ⟨⟩∘ _ ⟩
          ⟨ g , h ⟩ ∘ l       ≡˘⟨ ⟨⟩-unique _ refl refl ⟩∘⟨refl ⟩
          gh ∘ l              ∎

      g-iso : is-invertible g
      g-iso = make-invertible (p .centre .fst) (p .centre .snd .snd)
        (out! dgh.mediate∈E .fst _ _
          ( pullr (pullr (sym dgh.factors) ∙ π₁∘⟨⟩)
          ∙ p .centre .snd .fst ∙ introl refl))
        module g-ortho where
          p = is-s .snd (record { monic = g-monic })
            (idl _ ∙ sym (pullr (sym dgh.factors) ∙ π₁∘⟨⟩))
      module g = _≅_ (invertible→iso _ g-iso)

      compute =
        (h ∘ g.from) ∘ f                           ≡⟨ pullr refl ∙ pullr refl ⟩
        π₂ ∘ dgh.gh ∘ g.from ∘ f                   ≡⟨ refl ⟩∘⟨ ⟨⟩-unique _ refl refl ⟩∘⟨ refl ⟩
        π₂ ∘ ⟨ g , h ⟩ ∘ g.from ∘ f                ≡⟨ refl⟩∘⟨ ⟨⟩∘ _ ⟩
        π₂ ∘ ⟨ g ∘ g.from ∘ f , h ∘ g.from ∘ f ⟩   ≡⟨ π₂∘⟨⟩ ⟩
        h ∘ g.from ∘ f                             ≡⟨ refl⟩∘⟨ g-ortho.p .centre .snd .fst ⟩
        h ∘ dgh.d                                  ≡⟨ pullr (sym dgh.factors) ⟩
        π₂ ∘ ⟨ f , c ⟩                             ≡⟨ π₂∘⟨⟩ ⟩
        c                                          ∎

    open is-regular-epi renaming (r to Kp)
    open is-coequaliser
    is-strong-epi→is-regular-epi : is-regular-epi 𝒞 f
    is-strong-epi→is-regular-epi = go where
      go : is-regular-epi 𝒞 f
      go .Kp = kp.R
      go .arr₁ = kp.a
      go .arr₂ = kp.b
      go .has-is-coeq .coequal = kp.square
      go .has-is-coeq .coequalise w = Make.h w ∘ Make.g.from w
      go .has-is-coeq .universal {e′ = e′} {p = w} = Make.compute w
      go .has-is-coeq .unique {e′ = e′} {w} {colim} q = is-s .fst _ _ $
        colim ∘ f                      ≡˘⟨ q ⟩
        e′                             ≡˘⟨ Make.compute w ⟩
        (Make.h w ∘ Make.g.from w) ∘ f ∎
```
