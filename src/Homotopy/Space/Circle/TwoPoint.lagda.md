<!--
```agda
open import 1Lab.Prelude

open import Data.Int.Universal
open import Data.Int

open import Homotopy.Space.Circle hiding (ΩS¹≃integers)
```
-->

```agda
module Homotopy.Space.Circle.TwoPoint where
```

# Spaces: The circle with two point constructors

We can add additional points onto the [[circle]], and still end up with
a space that is homotopy-equivalent to `S¹`{.Agda}.

~~~{.quiver}
\begin{tikzpicture}
\node[draw,circle,label=below:{$\rm{south}$},fill,outer sep=0.1cm, inner sep=0pt, minimum size=0.1cm] (south) at (0, -1) {};
\node[draw,circle,label=above:{$\rm{north}$},fill,outer sep=0.1cm, inner sep=0pt, minimum size=0.1cm] (north) at (0, 1) {};
\draw[->, bend right=85, distance=1.2cm] (south) to node[right] {$\rm{east}\ i$} (north);
\draw[->, bend right=85, distance=1.2cm] (north) to node[left] {$\rm{west}\ i$} (south);
\end{tikzpicture}
~~~

```agda
data S¹₂ : Type where
  south : S¹₂
  north : S¹₂
  east : south ≡ north
  west : north ≡ south
```

The path which corresponds to `loop`{.Agda} is simply the composition of
`east`{.Agda} and `west`{.Agda}.

```agda
loop₂ : south ≡ south
loop₂ = east ∙ west
```

First we define a mapping from `S¹`{.Agda} to `S¹₂`{.Agda}.

```agda
S¹→S¹₂ : S¹ → S¹₂
S¹→S¹₂ base = south
S¹→S¹₂ (loop i) = loop₂ i
```

The inverse mapping is less obvious. `south`{.Agda} should of course map
to `base`{.Agda}.

<!--
```agda
_ = i0
_ = i1
```
-->

```agda
S¹₂→S¹ : S¹₂ → S¹
S¹₂→S¹ south = base
```

But what shall we map `north`{.Agda} (and by extension, `east`{.Agda}
and `west`{.Agda}) to? If the interval type were literally the unit
interval of the real numbers, $[0,1]$, then we could map `north`{.Agda}
to the point halfway along `loop`{.Agda}. However, the only two points
along the interval that we can name are `i0`{.Agda} and `i1`{.Agda}.
Thus, we need to map `north`{.Agda} to either `base`{.Agda}, `loop i0`,
or `loop i1`, since these are the only terms of type `S¹`{.Agda} that we
can name. However, all three of these terms are definitionally
`base`{.Agda}! So let's use that.

```agda
S¹₂→S¹ north = base
```

The question now arises how we map `east`{.Agda} and `west`{.Agda} onto
`S¹`{.Agda}. Recall that the composition `east ∙ west` should map to
`loop`{.Agda}. If we map `east`{.Agda} to `refl`{.Agda}, and
`west`{.Agda} to `loop`{.Agda}, then there will indeed be a path from
`ap S¹₂→S¹ (east ∙ west)` to `loop`{.Agda}.

```agda
S¹₂→S¹ (east i) = base
S¹₂→S¹ (west i) = loop i

loop₂→loop : ap S¹₂→S¹ loop₂ ≡ loop
loop₂→loop =
  ap S¹₂→S¹ loop₂                  ≡⟨⟩
  ap S¹₂→S¹ (east ∙ west)          ≡⟨ ap-∙ S¹₂→S¹ east west ⟩
  ap S¹₂→S¹ east ∙ ap S¹₂→S¹ west  ≡⟨⟩
  refl ∙ loop                      ≡⟨ ∙-idl _ ⟩
  loop                             ∎
```

As an aside, we can use this proof, along with `refl≠loop`{.Agda}, to
show that `loop₂`{.Agda} is similarly distinct from `refl`{.Agda}.

```agda
refl≠loop₂ : ¬ (refl ≡ loop₂)
refl≠loop₂ p = refl≠loop (ap (ap S¹₂→S¹) p ∙ loop₂→loop)
```

`loop₂→loop`{.Agda} is also enough to show that `S¹→S¹₂`{.Agda} and
`S¹₂→S¹`{.Agda} form an equivalence.

```agda
S¹₂≃S¹ : S¹₂ ≃ S¹
S¹₂≃S¹ = Iso→Equiv $
  S¹₂→S¹ , iso S¹→S¹₂
    (λ where
       base → refl
       (loop i) j → loop₂→loop j i)
    (λ where
       south → refl
       north → east
       (east i) j → east (i ∧ j)
       (west i) j → ∙-filler' east west (~ j) i)
```

Now we can borrow theorems about `S¹`{.Agda} and transport them to
theorems about `S¹₂`{.Agda}. The loop space at `south`{.Agda} is
equivalent to the integers.

```agda
module S¹₂Path {ℤ} (univ : Integers ℤ) where
  open S¹Path univ
  ΩS¹₂≃integers : (south ≡ south) ≃ ℤ
  ΩS¹₂≃integers = line→equiv (λ i → H i) ∙e ΩS¹≃integers
    where
      H : (south ≡ south) ≡ (base ≡ base)
      H = apd (λ i x → x ≡ x) (path→ua-pathp S¹₂≃S¹ refl)
```

The loop space at `north`{.Agda} is similarly equivalent to the
integers.

```agda
  ΩS¹₂≃integers' : (north ≡ north) ≃ ℤ
  ΩS¹₂≃integers' = line→equiv (λ i → H i) ∙e ΩS¹≃integers
    where
      H : (north ≡ north) ≡ (base ≡ base)
      H = apd (λ i x → x ≡ x) (path→ua-pathp S¹₂≃S¹ refl)

open S¹₂Path Int-integers public
```

<!--
```agda
private
  _ : ΩS¹₂≃integers .fst (loop₂ ∙ loop₂ ∙ loop₂) ≡ 3
  _ = same-difference refl

  _ : ΩS¹₂≃integers' .fst (west ∙ loop₂ ∙ east ∙ west ∙ loop₂ ∙ east) ≡ 4
  _ = same-difference refl
```
-->
