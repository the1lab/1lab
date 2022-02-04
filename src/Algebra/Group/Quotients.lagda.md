```agda
open import 1Lab.Prelude

open import Algebra.Group.Subgroup
open import Algebra.Group

open import Data.Set.Coequaliser
open import Data.Power

module Algebra.Group.Quotients where
```

<!--
```agda
private variable
  ℓ : Level
```
-->

# Quotient groups

Given a group $G$ and a normal subgroup $N$, the quotient $G/N$ is
obtained by identifying all of the elements $x, y : G$ whose difference
is in $N$. Classically, this would be constructed as a class of cosets
of $G$, but we define it directly by `quotienting`{.Agda ident=/} the
underlying set of $G$.

```agda
module _ (Grp : Group ℓ) (N : NormalSubgroup Grp) where
  open NormalSubgroup N renaming (subgroup to N?)
  open GroupOn (Grp .snd) renaming (inverse to inv)
  private G = Grp .fst

  private
    rel : G → G → Type ℓ
    rel x y = (x ⋆ inv y) ∈ N?

    rel-refl : ∀ x → rel x x
    rel-refl x = subst (_∈ N?) (sym inverseʳ) has-unit
```

We define a relation $\mathrm{rel}(x, y)$ on the underlying set of $G$
by $(x - y) \in N$, where $N$ is the normal subgroup we're quotienting
by. This relation is reflexive because $x - x$ is $0$, which is included
in every subgroup.

```agda
    T : Type ℓ
    T = G / rel
```

The underlying set of our quotient group, `T`{.Agda}, is the `set
quotient`{.Agda ident=/} of $G$ by the relation `rel`{.Agda}. We now
prove that the group operation (and the inverses) restrict to this
quotient, thus equipping `T`{.Agda} with a group structure.

```agda
    op : T → T → T
    op = Quot-op₂ rel-refl rel-refl _⋆_ (λ w x y z a b → rem₃ y z w x b a) where 
```

To prove that the group operation `_⋆_`{.Agda} descends to the quotient,
we prove that it takes related inputs to related outputs --- a
characterisation of binary operations on quotients we can invoke since
the relation we're quotienting by is reflexive. It suffices to show that
$(yw - zx) \in N$ whenever $w - x$ and $y - z$ are both in $N$, which is
a tedious but straightforward calculation:

```agda
      module
        _ (w x y z : G) 
          (w-x∈ : (w ⋆ inv x) ∈ N?) 
          (y-z∈ : (y ⋆ inv z) ∈ N?) where abstract
        rem₁ : ((w ⋆ inv x) ⋆ (inv z ⋆ y)) ∈ N?
        rem₁ = has-⋆ w-x∈ (has-comm y-z∈)

        rem₂ : ((w ⋆ (inv x ⋆ inv z)) ⋆ y) ∈ N?
        rem₂ = subst (_∈ N?) (associative ∙ ap (_⋆ y) (sym associative)) rem₁

        rem₃ : ((y ⋆ w) ⋆ inv (z ⋆ x)) ∈ N?
        rem₃ = subst (_∈ N?) (associative ∙ ap₂ _⋆_ refl (sym inv-comm)) 
          (has-comm rem₂)
```

To define inverses on the quotient, it suffices to show that whenever
$(x - y) \in N$, we also have $(x^{-1} - y) \in N$.

```agda
    inverse : T → T
    inverse = Coeq-rec squash (inc ∘ inv) λ { (x , y , r) → quot _ _ (p x y r) }
      where abstract
        p : ∀ x y → (x ⋆ inv y) ∈ N? → (inv x ⋆ inv (inv y)) ∈ N?
        p x y r = has-comm (subst (_∈ N?) inv-comm (has-inv r))
```

Even after this tedious algebra, it still remains to show that the
operation is associative and has inverses. Fortunately, since equality
in a group is a proposition, these follow from the group axioms on $G$
rather directly:

```agda
    GroupOn-T : GroupOn T
    GroupOn-T = makeGroup squash (inc unit) op inverse
      (Coeq-elimProp₃ (λ _ _ _ → squash _ _) 
        λ x y z i → inc (associative {x = x} {y} {z} (~ i)))
      (Coeq-elimProp (λ _ → squash _ _) λ x i → inc (inverseˡ {x = x} i))
      (Coeq-elimProp (λ _ → squash _ _) λ x i → inc (inverseʳ {x = x} i))
      (Coeq-elimProp (λ _ → squash _ _) λ x i → inc (idˡ {x = x} i))
  
  _/ᴳ_ : Group ℓ
  _/ᴳ_ = _ , GroupOn-T
```

We package together the underlying type `T`{.Agda} (which is not
exported) and the group structure on it in the type constructor
`_/ᴳ_`{.Agda}.
