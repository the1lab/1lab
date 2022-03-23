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
record is-equaliser {E} (f g : Hom A B) (equ : Hom E A) : Type (ℓ ⊔ ℓ′) where
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

  unique₂
    : ∀ {F} {e′ : Hom F A} {p : f ∘ e′ ≡ g ∘ e′} {lim' lim'' : Hom F E}
    → e′ ≡ equ ∘ lim'
    → e′ ≡ equ ∘ lim''
    → lim' ≡ lim''
  unique₂ {p = p} q r = unique {p = p} q ∙ sym (unique r)
```

We can visualise the situation using the commutative diagram below:

~~~{.quiver}
\[\begin{tikzcd}
  E & A & B \\
  F
  \arrow["f", shift left=1, from=1-2, to=1-3]
  \arrow["g"', shift right=1, from=1-2, to=1-3]
  \arrow["{\id{equ}}", hook, from=1-1, to=1-2]
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
    has-is-eq : is-equaliser f g equ

  open is-equaliser has-is-eq public
```

## Equalisers are monic

As a small initial application, we prove that equaliser arrows are
always [monic]:

[monic]: Cat.Morphism.html#monos

```agda
is-equaliser→is-monic
  : ∀ {E} (equ : Hom E A)
  → is-equaliser f g equ
  → is-monic equ
is-equaliser→is-monic equ equalises g h p =
  g                ≡⟨ unique (sym p) ⟩
  limiting equal-∘ ≡˘⟨ unique refl ⟩
  h ∎
  where open is-equaliser equalises
```
