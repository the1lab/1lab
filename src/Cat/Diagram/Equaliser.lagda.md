<!--
```agda
open import Cat.Prelude
```
-->

```agda
module Cat.Diagram.Equaliser {ℓ ℓ'} (C : Precategory ℓ ℓ') where
```

<!--
```agda
open import Cat.Reasoning C
private variable
  A B : Ob
  f g h : Hom A B
```
-->

# Equalisers {defines=equaliser}

The **equaliser** of two maps $f, g : A \to B$, when it exists,
represents the largest subobject of $A$ where $f$ and $g$ agree. In this
sense, the equaliser is the categorical generalisation of a _solution
set_: The solution set of an equation in one variable is largest subset
of the domain (i.e. what the variable ranges over) where the left- and
right-hand-sides agree.

```agda
record is-equaliser {E} (f g : Hom A B) (equ : Hom E A) : Type (ℓ ⊔ ℓ') where
  field
    equal     : f ∘ equ ≡ g ∘ equ
    universal : ∀ {F} {e' : Hom F A} (p : f ∘ e' ≡ g ∘ e') → Hom F E
    factors   : ∀ {F} {e' : Hom F A} {p : f ∘ e' ≡ g ∘ e'} → equ ∘ universal p ≡ e'
    unique
      : ∀ {F} {e' : Hom F A} {p : f ∘ e' ≡ g ∘ e'} {other : Hom F E}
      → equ ∘ other ≡ e'
      → other ≡ universal p

  equal-∘ : f ∘ equ ∘ h ≡ g ∘ equ ∘ h
  equal-∘ {h = h} =
    f ∘ equ ∘ h ≡⟨ extendl equal ⟩
    g ∘ equ ∘ h ∎

  unique₂
    : ∀ {F} {e' : Hom F A}  {o1 o2 : Hom F E}
    → f ∘ e' ≡ g ∘ e'
    → equ ∘ o1 ≡ e'
    → equ ∘ o2 ≡ e'
    → o1 ≡ o2
  unique₂ p q r = unique {p = p} q ∙ sym (unique r)
```

We can visualise the situation using the commutative diagram below:

~~~{.quiver}
\[\begin{tikzcd}
  E & A & B \\
  F
  \arrow["f", shift left=1, from=1-2, to=1-3]
  \arrow["g"', shift right=1, from=1-2, to=1-3]
  \arrow["{\rm{equ}}", hook, from=1-1, to=1-2]
  \arrow["{\exists!}", dashed, from=2-1, to=1-1]
  \arrow["e\prime"', from=2-1, to=1-2]
\end{tikzcd}\]
~~~

There is also a convenient bundling of an equalising arrow together with
its domain:

```agda
record Equaliser (f g : Hom A B) : Type (ℓ ⊔ ℓ') where
  field
    {apex}  : Ob
    equ     : Hom apex A
    has-is-eq : is-equaliser f g equ

  open is-equaliser has-is-eq public
```

## Equalisers are monic

As a small initial application, we prove that equaliser arrows are
always [[monic]]:

```agda
is-equaliser→is-monic
  : ∀ {E} (equ : Hom E A)
  → is-equaliser f g equ
  → is-monic equ
is-equaliser→is-monic equ equalises g h p =
  unique₂ (extendl equal) p refl
  where open is-equaliser equalises
```

# Categories with all equalisers

We also define a helper module for working with categories that have
equalisers of all parallel pairs of morphisms.

```agda
has-equalisers : Type _
has-equalisers = ∀ {a b} (f g : Hom a b) → Equaliser f g

module Equalisers (all-equalisers : has-equalisers) where
  module equaliser {a b} (f g : Hom a b) = Equaliser (all-equalisers f g)

  Equ : ∀ {a b} (f g : Hom a b) → Ob
  Equ = equaliser.apex
```
