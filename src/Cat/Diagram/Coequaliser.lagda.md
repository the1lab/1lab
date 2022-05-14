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
record is-coequaliser {E} (f g : Hom A B) (coeq : Hom B E) : Type (o ⊔ ℓ) where
  field
    coequal    : coeq ∘ f ≡ coeq ∘ g
    coequalise : ∀ {F} {e′ : Hom B F} (p : e′ ∘ f ≡ e′ ∘ g) → Hom E F
    universal  : ∀ {F} {e′ : Hom B F} {p : e′ ∘ f ≡ e′ ∘ g}
               → coequalise p ∘ coeq ≡ e′

    unique     : ∀ {F} {e′ : Hom B F} {p : e′ ∘ f ≡ e′ ∘ g} {colim : Hom E F}
               → e′ ≡ colim ∘ coeq
               → colim ≡ coequalise p

  unique₂
    : ∀ {F} {e′ : Hom B F} {p : e′ ∘ f ≡ e′ ∘ g} {colim' colim'' : Hom E F}
    → e′ ≡ colim' ∘ coeq
    → e′ ≡ colim'' ∘ coeq
    → colim' ≡ colim''
  unique₂ {p = p} q r = unique {p = p} q ∙ sym (unique r)

  id-coequalise : id ≡ coequalise coequal
  id-coequalise = unique (sym (idl _))
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

Dually to the situation with [equalisers], coequaliser arrows are always
[epic]:

[epic]: Cat.Morphism.html#epis

```agda
is-coequaliser→is-epic
  : ∀ {E} (coequ : Hom A E)
  → is-coequaliser f g coequ
  → is-epic coequ
is-coequaliser→is-epic {f = f} {g = g} equ equalises h i p =
  h                            ≡⟨ unique (sym p) ⟩
  coequalise (extendr coequal) ≡˘⟨ unique refl ⟩
  i                            ∎
  where open is-coequaliser equalises

coequaliser-unique
  : ∀ {E E′} {c1 : Hom A E} {c2 : Hom A E′}
  → is-coequaliser f g c1
  → is-coequaliser f g c2
  → E ≅ E′
coequaliser-unique {c1 = c1} {c2} co1 co2 =
  make-iso
    (co1 .coequalise {e′ = c2} (co2 .coequal))
    (co2 .coequalise {e′ = c1} (co1 .coequal))
    (unique₂ co2 {p = co2 .coequal} (sym (pullr (co2 .universal) ∙ co1 .universal)) (introl refl))
    (unique₂ co1 {p = co1 .coequal} (sym (pullr (co1 .universal) ∙ co2 .universal)) (introl refl))
  where open is-coequaliser
```
