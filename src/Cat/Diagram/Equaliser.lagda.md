```agda
open import Cat.Prelude

module Cat.Diagram.Equaliser {ℓ ℓ′} (C : Precategory ℓ ℓ′) where
```

<!--
```agda
open import Cat.Reasoning C
private variable
  A B : Ob
  f g h : Hom A B
```
-->

# Equalisers

The **equaliser** of two maps $f, g : A \to B$, when it exists,
represents the largest subobject of $A$ where $f$ and $g$ agree. In this
sense, the equaliser is the categorical generalisation of a _solution
set_: The solution set of an equation in one variable is largest subset
of the domain (i.e. what the variable ranges over) where the left- and
right-hand-sides agree.

```agda
record IsEqualiser {E} (f g : Hom A B) (equ : Hom E A) : Type (ℓ ⊔ ℓ′) where
  field
    equal     : f ∘ equ ≡ g ∘ equ
    limiting  : ∀ {F} {e′ : Hom F A} (p : f ∘ e′ ≡ g ∘ e′) → Hom F E
    universal : ∀ {F} {e′ : Hom F A} {p : f ∘ e′ ≡ g ∘ e′} → equ ∘ limiting p ≡ e′
    unique 
      : ∀ {F} {e′ : Hom F A} {p : f ∘ e′ ≡ g ∘ e′} {lim' : Hom F E}
      → e′ ≡ equ ∘ lim'
      → lim' ≡ limiting p

  equal-∘ : f ∘ equ ∘ h ≡ g ∘ equ ∘ h
  equal-∘ {h = h} =
    f ∘ equ ∘ h ≡⟨ extendl equal ⟩
    g ∘ equ ∘ h ∎
```

We can visualise the situation using the commutative diagram below:

~~~{.quiver}
\[\begin{tikzcd}
  E & A & B \\
  F
  \arrow["f", shift left=1, from=1-2, to=1-3]
  \arrow["g"', shift right=1, from=1-2, to=1-3]
  \arrow["{\mathrm{equ}}", hook, from=1-1, to=1-2]
  \arrow["{\exists!}", dashed, from=2-1, to=1-1]
  \arrow["e\prime"', from=2-1, to=1-2]
\end{tikzcd}\]
~~~

There is also a convenient bundling of an equalising arrow together with
its domain:

```agda
record Equaliser (f g : Hom A B) : Type (ℓ ⊔ ℓ′) where
  field
    {apex}  : Ob
    equ     : Hom apex A
    hasIsEq : IsEqualiser f g equ

  open IsEqualiser hasIsEq public   
```

## Equalisers are monic

As a small initial application, we prove that equaliser arrows are
always [monic]:

[monic]: Cat.Morphism.html#monos

```agda
IsEqualiser→isMonic 
  : ∀ {E} (equ : Hom E A)
  → IsEqualiser f g equ
  → isMonic equ
IsEqualiser→isMonic equ equalises g h p = 
  g                ≡⟨ unique (sym p) ⟩
  limiting equal-∘ ≡˘⟨ unique refl ⟩
  h ∎
  where open IsEqualiser equalises
```
