<!--
```agda
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Coequaliser where

```

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C
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
      coequ      : Hom B coapex
      has-is-coeq : is-coequaliser f g coequ

    open is-coequaliser has-is-coeq public
```

## Coequalisers are epic

Dually to the situation with [[equalisers]], coequaliser arrows are
always [[epic]].

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C
  private variable
    A B : Ob
    f g h : Hom A B
```
-->

```agda
  is-coequaliser→is-epic
    : ∀ {E} (coequ : Hom A E)
    → is-coequaliser C f g coequ
    → is-epic coequ
  is-coequaliser→is-epic {f = f} {g = g} equ equalises h i p =
    h                            ≡⟨ unique p ⟩
    universal (extendr coequal) ≡˘⟨ unique refl ⟩
    i                            ∎
    where open is-coequaliser equalises

  coequaliser-unique
    : ∀ {E E'} {c1 : Hom A E} {c2 : Hom A E'}
    → is-coequaliser C f g c1
    → is-coequaliser C f g c2
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

We also define a helper record for working with categories that have
coequalisers of all parallel pairs of morphisms.

```agda
record Coequalisers {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ ℓ) where
  no-eta-equality
  open Cat.Reasoning C
  field
    Coequ : ∀ {X Y} → Hom X Y → Hom X Y → Ob
    coequ : ∀ {X Y} → (f g : Hom X Y) → Hom Y (Coequ f g)
    coequal : ∀ {X Y} {f g : Hom X Y} → coequ f g ∘ f ≡ coequ f g ∘ g
    coequalise
      : ∀ {E X Y} {f g : Hom X Y}
      → (e' : Hom Y E)
      → e' ∘ f ≡ e' ∘ g
      → Hom (Coequ f g) E
    coequalise∘coequ
      : ∀ {E X Y} {f g : Hom X Y}
      → {e : Hom Y E} {p : e ∘ f ≡ e ∘ g}
      → coequalise e p ∘ coequ f g ≡ e
    coequalise-unique
      : ∀ {E X Y} {f g : Hom X Y}
      → {e : Hom Y E} {p : e ∘ f ≡ e ∘ g}
      → {other : Hom (Coequ f g) E}
      → other ∘ coequ f g ≡ e
      → other ≡ coequalise e p
```


<!--
```agda
  coequaliser : ∀ {X Y} (f g : Hom X Y) → Coequaliser C f g
  coequaliser f g .Coequaliser.coapex = Coequ f g
  coequaliser f g .Coequaliser.coequ = coequ f g
  coequaliser f g .Coequaliser.has-is-coeq .is-coequaliser.coequal = coequal
  coequaliser f g .Coequaliser.has-is-coeq .is-coequaliser.universal = coequalise _
  coequaliser f g .Coequaliser.has-is-coeq .is-coequaliser.factors = coequalise∘coequ
  coequaliser f g .Coequaliser.has-is-coeq .is-coequaliser.unique = coequalise-unique

  private module coequaliser {X Y} {f g : Hom X Y} = Coequaliser (coequaliser f g)
  open coequaliser
    using (has-is-coeq; id-coequalise)
    renaming (unique₂ to coequalise-unique₂)
    public
```
-->
