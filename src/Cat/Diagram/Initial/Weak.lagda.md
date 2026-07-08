<!--
```agda
open import Cat.Diagram.Equaliser.Joint
open import Cat.Diagram.Limit.Equaliser
open import Cat.Diagram.Product.Indexed
open import Cat.Diagram.Limit.Product
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Equaliser
open import Cat.Diagram.Initial
open import Cat.Univalent
open import Cat.Prelude

import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Diagram.Initial.Weak where
```

# Weakly initial objects and families {defines="weakly-initial-object"}

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat C
```
-->

A **weakly initial object** is like an [[initial object]], but dropping
the requirement of uniqueness. Explicitly, an object $X$ is weakly
initial in $\cC$, if, for every $Y : \cC$, there merely exists an arrow
$X \to Y$.

```agda
  is-weak-initial : ⌞ C ⌟ → Type _
  is-weak-initial X = ∀ Y → ∥ Hom X Y ∥
```

::: {.definition #weakly-initial-family}
We can weaken this even further, by allowing a family of objects rather
than the single object $X$: a family $(F_i)_{i : I}$ is weakly initial
if, for every $Y$, there exists a $j : I$ and a map $F_j \to Y$. Note
that we don't (can't!) impose any compatibility conditions between the
choices of indices.

```agda
  is-weak-initial-fam : ∀ {ℓ'} {I : Type ℓ'} (F : I → ⌞ C ⌟) → Type _
  is-weak-initial-fam {I = I} F = (Y : ⌞ C ⌟) → ∃[ i ∈ I ] (Hom (F i) Y)
```
:::

The connection between these notions is the following: the [[indexed
product]] of a weakly initial family $F$ is a weakly initial object.

```agda
  is-wif→is-weak-initial
    : ∀ {ℓ'} {I : Type ℓ'} (F : I → ⌞ C ⌟) {ΠF} {πf : ∀ i → Hom ΠF (F i)}
    → is-weak-initial-fam F
    → is-indexed-product C F πf
    → (y : ⌞ C ⌟) → ∥ Hom ΠF y ∥
  is-wif→is-weak-initial F {πf = πf} wif ip y = do
    (ix , h) ← wif y
    pure (h ∘ πf ix)
```

We can also connect these notions to the non-weak initial objects.
Suppose $\cC$ has all [[equalisers]], including [[joint equalisers]] for
small families. If $X$ is a weakly initial object, then the domain of
the joint equaliser $i : L \to X$ of all arrows $X \to X$ is an initial object.

```agda
  is-weak-initial→equaliser
    : ∀ (X : ⌞ C ⌟) {L} {l : Hom L X}
    → (∀ y → ∥ Hom X y ∥)
    → is-joint-equaliser C {I = Hom X X} (λ x → x) l
    → has-equalisers C
    → is-initial C L
  {-# INLINE is-weak-initial→equaliser #-}
  is-weak-initial→equaliser X {L} {i} is-wi lim eqs = L-initial where
    open is-joint-equaliser lim
```

Since, for any $Y$, the space of maps $e \to Y$ is inhabited, it will
suffice to show that it is a [[proposition]]. To this end, given two
arrows $f, g : L \to Y$, consider their equaliser $j : E \to L$. First,
we have some arrow $k : X \to E$.

```agda
    p' : ∀ {y} → is-prop (Hom L y)
    p' f g = ∥-∥-out! do
      let
        module fg = Equaliser (eqs f g)
        open fg renaming (equ to j) using ()

      k ← is-wi fg.apex
```

Then, we can calculate: as maps $L \to X$, we have $i = ijki$;

```agda
      let
        p =
          i               ≡⟨ introl refl ⟩
          id ∘ i          ≡⟨ equal {j = i ∘ j ∘ k} ⟩
          (i ∘ j ∘ k) ∘ i ≡⟨ pullr (pullr refl) ⟩
          i ∘ j ∘ k ∘ i   ∎
```

Then, since a joint equaliser is a [[monomorphism]], we can cancel $i$
from both sides to get $jki = \id$;

```agda
        r : j ∘ k ∘ i ≡ id
        r = is-joint-equaliser→is-monic (j ∘ k ∘ i) id (sym p ∙ intror refl)
```

Finally, if we have $g, h : L \to Z$ with $gj = hj$, then we can
calculate $$g = gjki = hjki = h$$, so $j$ is an [[epimorphism]]. So,
since $j$ equalises $f$ and $g$ by construction, we have $f = g$!

```agda
        s : is-epic j
        s g h α = intror r ∙ extendl α ∙ elimr r

      pure (s f g fg.equal)

    cen : ∀ {y} → Hom L y
    cen {y} = ∥-∥-out p' ((_∘ i) <$> is-wi y)

    L-initial : is-initial C L
    {-# INLINE L-initial #-}
    L-initial = hom-contr→is-initial λ y → is-prop∙→is-contr p' cen
```

Putting this together, we can show that, if a [[complete category]] has
a small weakly initial family, then it has an initial object.

```agda
  is-complete-weak-initial→initial
    : ∀ {κ} {I : Type κ} (F : I → ⌞ C ⌟)
    → is-complete κ (ℓ ⊔ κ) C
    → is-weak-initial-fam F
    → Initial C
  is-complete-weak-initial→initial {κ = κ} {I} F compl wif =
    record { has-is-init = equal-is-initial } where
```

<details>
<summary>The proof is by pasting together the results above.</summary>

```agda
      open Indexed-product

      prod : Indexed-product C F
      prod = Limit→IP C F (is-complete-lower κ ℓ κ κ compl _)

      prod-is-wi : is-weak-initial (prod .ΠF)
      prod-is-wi = is-wif→is-weak-initial F wif (prod .has-is-ip)

      equal : Joint-equaliser C {I = Hom (prod .ΠF) (prod .ΠF)} λ h → h
      equal = Limit→Joint-equaliser C _ id (is-complete-lower κ κ lzero ℓ compl _)
      open Joint-equaliser equal using (has-is-je)

      equal-is-initial = is-weak-initial→equaliser _ prod-is-wi has-is-je λ f g →
        Limit→Equaliser C (is-complete-lower κ (ℓ ⊔ κ) lzero lzero compl _)
```

</details>
