<!--
```agda
open import Cat.Morphism.Factorisation
open import Cat.Diagram.Limit.Finite
open import Cat.Morphism.Orthogonal
open import Cat.Morphism.StrongEpi
open import Cat.Diagram.Pullback
open import Cat.Instances.Slice
open import Cat.Prelude
open import Cat.Regular

import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Regular.Slice
  {o ℓ} {C : Precategory o ℓ} (y : Precategory.Ob C)
  (reg : is-regular C)
  where
```

# Regular categories are stable under slicing

Let $\cC$ be a [regular category]: a [[finitely complete category]]
where maps have [[pullback-stable]] [strong epi]-[mono] factorisations.
In this module, we'll establish that, for any object $y : \cC$, the
[slice] $\cC/y$ is _also_ a regular category. If we motivate regular
categories by the well-behaved calculus of relations of their internal
language, stability under slicing means that relations _remain_
well-behaved under passing to arbitrary contexts.

[regular category]: Cat.Regular.html
[pullback-stable]: Cat.Diagram.Pullback.html#stability
[strong epi]: Cat.Morphism.StrongEpi.html
[mono]: Cat.Morphism.html#monos
[slice]: Cat.Instances.Slice.html

<!--
```agda
private
  module r = is-regular reg
  C/y = Slice C y
  module C/y = Cr C/y
open Cr C
open Factorisation
open is-regular
open Functor
open /-Obj
open /-Hom

private
  C/y-lex : Finitely-complete C/y
  C/y-lex = with-pullbacks C/y Slice-terminal-object pb where
    pb : ∀ {A B X} (f : C/y.Hom A X) (g : C/y.Hom B X) → Pullback C/y f g
    pb {A = A} f g = below where
      above = r.lex.pullbacks (f .map) (g .map)

      below : Pullback C/y f g
      below .Pullback.apex = cut (A .map ∘ above .Pullback.p₁)
      below .Pullback.p₁ .map      = above .Pullback.p₁
      below .Pullback.p₁ .commutes = refl
      below .Pullback.p₂ .map      = above .Pullback.p₂
      below .Pullback.p₂ .commutes =
        pushl (sym (g .commutes)) ∙ ap₂ _∘_ refl (sym (above .Pullback.square)) ∙ pulll (f .commutes)
      below .Pullback.has-is-pb = pullback-above→pullback-below (above .Pullback.has-is-pb)

  pres-mono
    : ∀ {a b} (h : a C/y.↪ b)
    → a .domain ↪ b .domain
  pres-mono h .mor = h .mor .map
  pres-mono {a = A} h .monic a b p = ap map $ h .C/y.monic
    {c = cut (A .map ∘ a)}
    (record { commutes = refl })
    (record { commutes = pushl (sym (h .mor .commutes)) ·· ap₂ _∘_ refl (sym p) ·· pulll (h .mor .commutes) })
    (ext p)
```
-->

Other than finite limits, which we have already extensively investigated
in slice categories (see [limits in slices][slilim]), what remains of
the proof is a characterisation of the [strong epimorphisms] in a slice
$\cC/y$. To do this, we will freely use that $\cC$ and $\cC/y$ are
finitely complete, and instead characterise the _extremal_ epimorphisms.

[slilim]: Cat.Instances.Slice.Limit.html
[strong epimorphisms]: Cat.Morphism.StrongEpi.html

For this, it will suffice to show that the inclusion functor $\cC/y
\mono \cC$ both preserves and reflects extermal epimorphisms. Given an
extremal epi $h : a \epi b$ over $y$, and a non-trivial factorisation of
$h$ through a monomorphism $m$ in $\cC$, we can show that $m$ itself is
a monomorphism $bm \to b$ over $y$, and that it factors $h$ in $\cC/y$.
It follows that $m$ is invertible as a map over $y$, meaning it is
invertible in $\cC$.

```agda
  preserve-cover
    : ∀ {a b} (h : C/y.Hom a b)
    → is-strong-epi C/y h
    → is-strong-epi C (h .map)
  preserve-cover {b = B} h cover = is-extremal-epi→is-strong-epi C r.has-is-lex λ m g p →
    let
      mono : cut (B .map ∘ m .mor) C/y.↪ B
      mono = record
        { mor   = record { map = m .mor ; commutes = refl }
        ; monic = λ g h p → ext (m .monic _ _ (ap map p))
        }

      inv : C/y.is-invertible (record { map = m .mor ; commutes = refl })
      inv = extreme mono
        (record { map = g ; commutes = pullr (sym p) ∙ h .commutes })
        (ext p)
    in make-invertible
      (inv .C/y.is-invertible.inv .map)
      (ap map (inv .C/y.is-invertible.invl))
      (ap map (inv .C/y.is-invertible.invr))
    where extreme = is-strong-epi→is-extremal-epi C/y cover
```

In the converse direction, suppose $a \to b$ is a map over $y$ which is
a strong epimorphism in $\cC$. Since the projection functor $\cC/y \to
\cC$ preserves monos (it preserves pullbacks), any non-trivial
factorisation of $a \to b$ through a monomorphism $m$ over $y$ must
still be a non-trivial factorisation when regarded in $\cC$. We can then
calculate that the inverse to $m$ is still a map over $y$.

```agda
  reflect-cover
    : ∀ {a b} (h : C/y.Hom a b)
    → is-strong-epi C (h .map)
    → is-strong-epi C/y h
  reflect-cover h cover = is-extremal-epi→is-strong-epi C/y C/y-lex λ m g p →
    let inv = extn (pres-mono m) (g .map) (ap map p)
    in C/y.make-invertible
      (record
        { map      = inv .is-invertible.inv
        ; commutes = invertible→epic inv _ _ $
          cancelr (inv .is-invertible.invr) ∙ sym (m .mor .commutes)
        })
      (ext (inv .is-invertible.invl))
      (ext (inv .is-invertible.invr))
    where extn = is-strong-epi→is-extremal-epi C cover
```

Since the projection functor preserves and reflects strong epimorphisms,
we can compute [[image factorisations]] over $y$ as image factorisations in
$\cC$. And since the projection functor additionally preserves
pullbacks, by the same argument, it suffices for strong epimorphisms to
be stable under pullback in $\cC$ for them to be stable under pullback
in $\cC/y$, too.

```agda
slice-is-regular : is-regular (Slice C y)
slice-is-regular .factor {a} {b} f = fact' where
  fact = r.factor (f .map)
  private module f = Factorisation fact

  fact' : Factorisation C/y (StrongEpi C/y) (Mono C/y) f
  fact' .mediating = cut (b .map ∘ f.forget)
  fact' .mediate = record { commutes = pullr (sym f.factors) ∙ f .commutes }
  fact' .forget .map      = f.forget
  fact' .forget .commutes = refl
  fact' .mediate∈E = do
    c ← f.mediate∈E
    pure (reflect-cover (fact' .mediate) c)
  fact' .forget∈M = inc λ g h p → ext $ out! f.forget∈M (g .map) (h .map) (ap map p)
  fact' .factors = ext f.factors

slice-is-regular .stable {B = B} f g {p1} {p2} cover is-pb =
  reflect-cover p1 $ r.stable _ _
    (preserve-cover _ cover)
    (pullback-below→pullback-above is-pb)

slice-is-regular .has-is-lex = C/y-lex
```
