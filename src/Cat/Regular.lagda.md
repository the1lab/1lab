```agda
open import Cat.Diagram.Coequaliser.RegularEpi
open import Cat.Instances.Sets.Complete
open import Cat.Functor.FullSubcategory
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Coequaliser
open import Cat.Diagram.Pullback
open import Cat.Instances.Comma
open import Cat.Instances.Slice
open import Cat.Diagram.Product
open import Cat.Diagram.Initial
open import Cat.Diagram.Image
open import Cat.Prelude

import Cat.Reasoning as Cr

open import Data.Set.Surjection

module Cat.Regular where
```

<!--
```agda
open is-regular-epi
open is-coequaliser
open Coequaliser
open is-pullback
open Pullback
open Initial
open /-Hom
open /-Obj
open ↓Obj
open ↓Hom
```
-->

# Regular categories

A **regular category** is a category with [pullback]-stable [image]
factorizations^[though see there, "image" here means "tightest
monomorphism through with a morphism factors"]. For the definition, we
unpack this into more elementary conditions^[using the fact that any
image is a [regular epi]], but that is essentially the gist of it.
Regular categories abound: Any [topos] is a regular category^[hence the
category $\sets$], every category of models for an algebraic theory in a
regular category^[thus groups, rings, monoids, etc], all [abelian
categories] are regular, etc.

[pullback]: Cat.Diagram.Pullback.html
[image]: Cat.Diagram.Image.html
[regular epi]: Cat.Diagram.Coequaliser.RegularEpi.html
[topos]: Topoi.Base.html
[abelian categories]: Cat.Abelian.Base.html

A regular category is a [finitely complete] category^[so, in particular,
a category equipped with a choice of pullbacks for any pair of
morphisms] such that:

[finitely complete]: Cat.Diagram.Pullback.html

```agda
record is-regular {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ ℓ) where
  private module C = Cr C
  field has-is-lex : Finitely-complete C
  open Finitely-complete has-is-lex public
```

- The kernel pair $d \times_c d \tto d$ of any morphism $f : d \to c$
(hence the pullback of $f$ along $f$, see the diagram below) admits a
coequaliser,

  ~~~{.quiver}
  \[\begin{tikzcd}
    {d \times_cd} && d \\
    \\
    d && c\text{,}
    \arrow["f", from=1-3, to=3-3]
    \arrow["f"', from=3-1, to=3-3]
    \arrow["{p_1}", from=1-1, to=1-3]
    \arrow["{p_2}"', from=1-1, to=3-1]
  \end{tikzcd}\]
  ~~~

  which we write concisely as $d \times_c d \tto d \to
  \mathrm{coeq}(p_1, p_2)$.

- Regular epimorphisms are stable under change-of-base.

```agda
  field
    kernel-pair-coeq
      : ∀ {d c} (f : C.Hom d c)
      → Coequaliser C (pullbacks f f .Pullback.p₁) (pullbacks f f .Pullback.p₂)
    regular-epi-stability
      : ∀ {e d c} (f : C.Hom d c) (g : C.Hom e c)
      → is-regular-epi C f
      → is-regular-epi C (pullbacks f g .Pullback.p₂)

open is-regular
```

The basic example of regular category is the category $\sets$. As
mentioned in the introductory paragraph, this is an instance of a more
general fact, but we prove it here in this specific case first, for the
sake of concreteness.

```agda
Sets-is-regular : ∀ {ℓ} → is-regular (Sets ℓ)
Sets-is-regular .has-is-lex = Sets-finitely-complete
```

Note that the cofork given by $f$'s kernel pair^[for any map $f$] has a
coequaliser in $\sets$, because _every_ cofork has a coequaliser in
$\sets$: it is a cocomplete category. But we can compute it very
directly as the [_quotient set_] of $f$'s kernel pair.

[_quotient set_]: Data.Set.Coequaliser.html#quotients

```agda
Sets-is-regular .kernel-pair-coeq {d} {c} f = coequ where
  coequ : Coequaliser (Sets _) _ _
  coequ .coapex = el! (∣ d ∣ / λ x y → f x ≡ f y)
  coequ .coeq = inc
  coequ .has-is-coeq .coequal = funext λ { (x , y , p) → quot p }
  coequ .has-is-coeq .coequalise {e′ = e′} p =
    Coeq-rec hlevel! e′ (p $ₚ_)
  coequ .has-is-coeq .universal = refl
  coequ .has-is-coeq .unique {e′ = e′} {p} {colim = colim} q = funext $
    Coeq-elim-prop (λ _ → hlevel!)
      λ e → sym (q $ₚ e)
```

To prove that the pullback of a regular epimorphism is regular, we
appeal to [the correspondence between surjections and epis][epi]: We
must (merely) come up with a fibre of the pulled-back map over a given
point, which would be annoying, but note that the map we started with
gives us the data we need (because it is a surjection).

[epi]: Data.Set.Surjection.html

```agda
Sets-is-regular .regular-epi-stability {e} {d} {C} f g f-re =
  surjective→regular-epi _ e _ λ x → do
    (f , p) ← epi→surjective d C f
      (λ {c} → is-coequaliser→is-epic (Sets _) f (f-re .has-is-coeq) {c = c})
      (g x)
    pure ((f , x , p) , refl)
```

## Image factorisations

Morphisms in a regular category have an [image factorisation]: The
**regular image**^[note that some authors call it the regular *co**image
instead, but we will not use this terminology]. The strategy is as
follows: letting $f : c \to d$ be some morphism, the axioms for a
regular category ensure its kernel pair has a coequaliser $d \times_c d
\tto d \to \id{coeq}(p1,p2)$. We can factor $f$ as

[image factorisation]: Cat.Diagram.Image.html

$$
c \to \id{coeq}(p1, p2) \to d
$$

and prove that this is an image factorisation.

```agda
module _ {o ℓ} (C : Precategory o ℓ) (reg : is-regular C) where
  private
    module C = Cr C
    module r = is-regular reg

  dom→coim : ∀ {x y} (f : C.Hom x y) → C.Hom x (r.kernel-pair-coeq f .coapex)
  dom→coim f = r.kernel-pair-coeq f .coeq

  coim→cod : ∀ {x y} (f : C.Hom x y) → C.Hom (r.kernel-pair-coeq f .coapex) y
  coim→cod f = r.kernel-pair-coeq f .coequalise {e′ = f} (r.pullbacks f f .square)

  postulate
    coim↪cod : ∀ {x y} (f : C.Hom x y) → C.is-monic (coim→cod f)
    -- coim↪cod {x} {y} f {E} g h p = {!   !} where
    --   module i×i = Product
    --     (r.products
    --       (r.kernel-pair-coeq f .coapex)
    --       (r.kernel-pair-coeq f .coapex))
    --   module x×x = Product
    --     (r.products
    --       x x)
    --   module V = Pullback
    --     (r.pullbacks
    --       i×i.⟨ g , h ⟩
    --       i×i.⟨ dom→coim f C.∘ x×x.π₁ , dom→coim f C.∘ x×x.π₂ ⟩)
    --   module ker = Pullback (r.pullbacks f f)
    --   q0 = x×x.π₁ C.∘ V.p₂
    --   q1 = x×x.π₂ C.∘ V.p₂
    --   m = coim→cod f
    --   e = dom→coim f
    --   vsq :
    --       (i×i.⟨ g , h ⟩ C.∘ V.p₁)
    --     ≡ (i×i.⟨ e C.∘ x×x.π₁ , e C.∘ x×x.π₂ ⟩ C.∘ V.p₂)
    --   vsq = V.square

    --   arr : C.Hom V.apex ker.apex
    --   arr = ker.limiting {p₁' = q0} {p₂' = q1} $
    --     f C.∘ q0              ≡⟨ C.pushl (sym (r.kernel-pair-coeq f .universal)) ⟩
    --     m C.∘ e C.∘ q0        ≡⟨ ap (m C.∘_) (sym i×i.π₁∘factor ∙ ap₂ C._∘_ refl (i×i.unique₂ i×i.π₁∘factor i×i.π₂∘factor (C.pulll i×i.π₁∘factor ∙ C.pullr refl) (C.pulll i×i.π₂∘factor ∙ C.pullr refl) ∙ sym vsq) ∙ C.pulll i×i.π₁∘factor) ⟩
    --     m C.∘ g C.∘ V.p₁      ≡⟨ C.extendl p ⟩
    --     m C.∘ h C.∘ V.p₁      ≡⟨ ap (m C.∘_) (sym i×i.π₂∘factor ∙ ap₂ C._∘_ refl (i×i.unique₂ i×i.π₁∘factor i×i.π₂∘factor (C.pulll i×i.π₁∘factor) (C.pulll i×i.π₂∘factor) ∙ vsq) ∙ C.extendl i×i.π₂∘factor) ⟩
    --     m C.∘ e C.∘ q1        ≡⟨ C.pulll (r.kernel-pair-coeq f .universal) ⟩
    --     f C.∘ x×x.π₂ C.∘ V.p₂ ∎

    --   arr-p : x×x.⟨ q0 , q1 ⟩ ≡ x×x.⟨ ker.p₁ , ker.p₂ ⟩ C.∘ arr

    --   postulate
    --   q : g C.∘ V.p₁ ≡ h C.∘ V.p₁
    --   -- q =
    --   --   g C.∘ V.p₁           ≡⟨ {! !} ⟩
    --   --   e C.∘ q0             ≡⟨ {! !} ⟩
    --   --   e C.∘ ker.p₁ C.∘ arr ≡⟨ {! !} ⟩
    --   --   e C.∘ ker.p₂ C.∘ arr ≡⟨ {! !} ⟩
    --   --   e C.∘ q1             ≡⟨ {! !} ⟩
    --   --   h C.∘ V.p₁           ∎


  -- regular-image : ∀ {x y} (f : C.Hom x y) → Image C f
  -- regular-image f .bot .x = tt
  -- regular-image f .bot .y = restrict (cut (coim→cod f)) (coim↪cod f)
  -- regular-image f .bot .map .map      = dom→coim f
  -- regular-image f .bot .map .commutes = r.kernel-pair-coeq f .universal
  -- regular-image f .has⊥ x₁ = {!   !}
```
