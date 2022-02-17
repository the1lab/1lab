```agda
open import Cat.Prelude

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

# Coequalisers

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
record IsCoequaliser {E} (f g : Hom A B) (coeq : Hom B E) : Type (o ⊔ ℓ) where
  field
    coequal    : coeq ∘ f ≡ coeq ∘ g
    coequalize : ∀ {F} {e′ : Hom B F} (p : e′ ∘ f ≡ e′ ∘ g) → Hom E F
    universal  : ∀ {F} {e′ : Hom B F} (p : e′ ∘ f ≡ e′ ∘ g)
                 → coequalize p ∘ coeq ≡ e′
    unique     : ∀ {F} {e′ : Hom B F} {p : e′ ∘ f ≡ e′ ∘ g} {colim : Hom E F}
                 → e′ ≡ colim ∘ coeq
                 → colim ≡ coequalize p

  unique₂ : (p q : h ∘ f ≡ h ∘ g) → coequalize p ≡ coequalize q
  unique₂ p q = unique (sym (universal p))

  id-coequalize : id ≡ coequalize coequal
  id-coequalize = unique (sym (idl _))

```

There is also a convenient bundling of an coequalising arrow together with
its codomain:

```agda
record Coequaliser (f g : Hom A B) : Type (o ⊔ ℓ) where
  field
    {coapex}  : Ob
    coeq      : Hom B coapex
    hasIsCoeq : IsCoequaliser f g coeq

  open IsCoequaliser hasIsCoeq public
```


