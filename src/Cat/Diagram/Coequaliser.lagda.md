<!--
```agda
open import Cat.Prelude
```
-->

```agda
module Cat.Diagram.Coequaliser {o ℓ} (C : Precategory o ℓ) where

```

<!--
```agda
open import Cat.Reasoning C
private variable
  A B : Ob
  f g h : Hom A B
```
-->

# Coequalisers {defines="coequaliser"}

The **coequaliser** of two maps $f, g : A \to B$ (if it exists),
represents the largest quotient object of $B$ that identifies $f$
and $g$.

~~~{.quiver}
\[\begin{tikzcd}
  A & B & E \\
  && F
  \arrow["f", shift left=2, from=1-1, to=1-2]
  \arrow["g"', shift right=2, from=1-1, to=1-2]
  \arrow[from=1-2, to=1-3]
  \arrow[from=1-2, to=2-3]
  \arrow["{\exists!}", dashed, from=1-3, to=2-3]
\end{tikzcd}\]
~~~

```agda
record is-coequaliser {E} (f g : Hom A B) (coeq : Hom B E) : Type (o ⊔ ℓ) where
  field
    coequal    : coeq ∘ f ≡ coeq ∘ g
    universal  : ∀ {F} {e' : Hom B F} (p : e' ∘ f ≡ e' ∘ g) → Hom E F
    factors    : ∀ {F} {e' : Hom B F} {p : e' ∘ f ≡ e' ∘ g}
               → universal p ∘ coeq ≡ e'

    unique     : ∀ {F} {e' : Hom B F} {p : e' ∘ f ≡ e' ∘ g} {colim : Hom E F}
               → colim ∘ coeq ≡ e'
               → colim ≡ universal p

  unique₂
    : ∀ {F} {e' : Hom B F}  {o1 o2 : Hom E F}
    → (e' ∘ f ≡ e' ∘ g)
    → o1 ∘ coeq ≡ e'
    → o2 ∘ coeq ≡ e'
    → o1 ≡ o2
  unique₂ p q r = unique {p = p} q ∙ sym (unique r)

  id-coequalise : id ≡ universal coequal
  id-coequalise = unique (idl _)
```

There is also a convenient bundling of an coequalising arrow together with
its codomain:

```agda
record Coequaliser (f g : Hom A B) : Type (o ⊔ ℓ) where
  field
    {coapex}  : Ob
    coeq      : Hom B coapex
    has-is-coeq : is-coequaliser f g coeq

  open is-coequaliser has-is-coeq public
```

## Coequalisers are epic

Dually to the situation with [[equalisers]], coequaliser arrows are
always [[epic]].

```agda
is-coequaliser→is-epic
  : ∀ {E} (coequ : Hom A E)
  → is-coequaliser f g coequ
  → is-epic coequ
is-coequaliser→is-epic {f = f} {g = g} equ equalises h i p =
  h                            ≡⟨ unique p ⟩
  universal (extendr coequal) ≡˘⟨ unique refl ⟩
  i                            ∎
  where open is-coequaliser equalises

coequaliser-unique
  : ∀ {E E'} {c1 : Hom A E} {c2 : Hom A E'}
  → is-coequaliser f g c1
  → is-coequaliser f g c2
  → E ≅ E'
coequaliser-unique {c1 = c1} {c2} co1 co2 =
  make-iso
    (co1 .universal {e' = c2} (co2 .coequal))
    (co2 .universal {e' = c1} (co1 .coequal))
    (unique₂ co2 (co2 .coequal) (pullr (co2 .factors) ∙ co1 .factors) (idl _))
    (unique₂ co1 (co1 .coequal) (pullr (co1 .factors) ∙ co2 .factors) (idl _))
  where open is-coequaliser
```

# Categories with all coequalisers

We also define a helper module for working with categories that have
coequalisers of all parallel pairs of morphisms.

```agda
has-coequalisers : Type _
has-coequalisers = ∀ {a b} (f g : Hom a b) → Coequaliser f g

module Coequalisers (all-coequalisers : has-coequalisers) where
  module coequaliser {a b} (f g : Hom a b) = Coequaliser (all-coequalisers f g)

  Coequ : ∀ {a b} (f g : Hom a b) → Ob
  Coequ = coequaliser.coapex
```
