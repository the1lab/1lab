```agda
open import Cat.Diagram.Coequaliser.RegularEpi
open import Cat.Diagram.Pullback.Properties
open import Cat.Functor.FullSubcategory
open import Cat.Instances.Sets.Complete
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Coequaliser
open import Cat.Diagram.Pullback
open import Cat.Diagram.Initial
open import Cat.Diagram.Product
open import Cat.Instances.Comma
open import Cat.Instances.Slice
open import Cat.Instances.Sets
open import Cat.Diagram.Image
open import Cat.Prelude

open import Data.Set.Surjection

import Cat.Reasoning as Cr

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
category $\Sets$], every category of models for an algebraic theory in a
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
  field has-is-cat : is-category C
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

  regular-epi-stable
    : ∀ {e d c P} (f : C.Hom d c) (g : C.Hom e c)
        {p1 : C.Hom P d} {p2 : C.Hom P e}
    → is-regular-epi C f
    → is-pullback C p1 f p2 g
    → is-regular-epi C p2
  regular-epi-stable f g f-re pb =
    transport
      (ap₂ (λ x m → is-regular-epi C {a = x} m)
        (ap apex $ Pullback-unique has-is-cat (pullbacks f g) (record { has-is-pb = pb }))
        (ap p₂ $ Pullback-unique has-is-cat (pullbacks f g) (record { has-is-pb = pb })))
      (regular-epi-stability f g f-re)

open is-regular
```

The basic example of regular category is the category $\Sets$. As
mentioned in the introductory paragraph, this is an instance of a more
general fact, but we prove it here in this specific case first, for the
sake of concreteness.

```agda
Sets-is-regular : ∀ {ℓ} → is-regular (Sets ℓ)
Sets-is-regular .has-is-cat = Sets-is-category
Sets-is-regular .has-is-lex = Sets-finitely-complete
```

Note that the cofork given by $f$'s kernel pair^[for any map $f$] has a
coequaliser in $\Sets$, because _every_ cofork has a coequaliser in
$\Sets$: it is a cocomplete category. But we can compute it very
directly as the [_quotient set_] of $f$'s kernel pair.

[_quotient set_]: Data.Set.Coequaliser.html#quotients

```agda
Sets-is-regular .kernel-pair-coeq {d} {c} f = coequ where
  coequ : Coequaliser (Sets _) _ _
  coequ .coapex = el! (∣ d ∣ / λ x y → f x ≡ f y)
  coequ .coeq = inc
  coequ .has-is-coeq .coequal = funext λ { (x , y , p) → quot p }
  coequ .has-is-coeq .universal {e′ = e′} p =
    Coeq-rec hlevel! e′ (p $ₚ_)
  coequ .has-is-coeq .factors = refl
  coequ .has-is-coeq .unique {e′ = e′} {p} {colim = colim} q = funext $
    Coeq-elim-prop (λ _ → hlevel!)
      λ e → q $ₚ e
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
