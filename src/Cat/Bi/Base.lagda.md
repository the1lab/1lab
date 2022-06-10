```agda
open import Cat.Instances.Product
open import Cat.Instances.Functor
open import Cat.Prelude

import Cat.Functor.Bifunctor as Bi
import Cat.Functor.Reasoning as Fr
import Cat.Reasoning as Cr

module Cat.Bi.Base where
```

# Prebicategories

<!--
```agda
open _=>_

private module _ where
  open Functor
  compose-assocˡ
    : ∀ {o ℓ ℓ′} {O : Type o} {H : O → O → Precategory ℓ ℓ′}
    → (C : ∀ {A B C} → Functor (H B C ×ᶜ H A B) (H A C))
    → ∀ {A B C D}
    → Functor (H C D ×ᶜ H B C ×ᶜ H A B) (H A D)
  compose-assocˡ C .F₀ (F , G , H) = C .F₀ (C .F₀ (F , G) , H)
  compose-assocˡ C .F₁ (f , g , h) = C .F₁ (C .F₁ (f , g) , h)
  compose-assocˡ C .F-id = ap (C .F₁) (Σ-pathp (C .F-id) refl) ∙ C .F-id
  compose-assocˡ C .F-∘ f g = ap (C .F₁) (Σ-pathp (C .F-∘ _ _) refl) ∙ C .F-∘ _ _

  compose-assocʳ
    : ∀ {o ℓ ℓ′} {O : Type o} {H : O → O → Precategory ℓ ℓ′}
    → (C : ∀ {A B C} → Functor (H B C ×ᶜ H A B) (H A C))
    → ∀ {A B C D}
    → Functor (H C D ×ᶜ H B C ×ᶜ H A B) (H A D)
  compose-assocʳ C .F₀ (F , G , H) = C .F₀ (F , C .F₀ (G , H))
  compose-assocʳ C .F₁ (f , g , h) = C .F₁ (f , C .F₁ (g , h))
  compose-assocʳ C .F-id = ap (C .F₁) (Σ-pathp refl (C .F-id)) ∙ C .F-id
  compose-assocʳ C .F-∘ f g = ap (C .F₁) (Σ-pathp refl (C .F-∘ _ _)) ∙ C .F-∘ _ _

private variable o ℓ ℓ′ o₁ ℓ₁ ℓ₁′ : Level
```
-->

A (pre)**bicategory** is the natural higher-dimensional generalisation
of a (pre)[category]. Whereas a precategory has $\hom$-[sets], a
prebicategory has $\hom$-precategories. While this generalisation might
seem simple, in reality, we must be very careful when setting up the
resulting structure: The key observation is that precategories have no
notion of equality of objects, so everything which _was_ an equation in
the definition of precategories must be replaced with (sufficiently
coherent) specified isomorphisms.

[sets]: 1Lab.HLevel.html#is-set

The data of a prebicategory consists of a type of objects $\bf{Ob}$, and
for each $A, B : \bf{Ob}$, a precategory $\hom(A, B)$. We refer to the
type of objects of $\hom(A, B)$ by $A \mapsto B$, and call its
inhabitants **maps** or **1-cells**; In the second dimension, between
each pair of maps $f, g$, we have a set of **2-cells** (sometimes
**homotopies**), written $f \To g$.

The composition operation of $\hom(A,B)$, called **vertical
composition**, will be written $\alpha \otimes \beta$. As for why it's
called _vertical_ composition, note that it reduces pasting diagrams of
the form

~~~{.quiver .short-1}
\[\begin{tikzcd}
  A && {B\text{.}}
  \arrow[""{name=0, anchor=center, inner sep=0}, curve={height=-18pt}, from=1-1, to=1-3]
  \arrow[""{name=1, anchor=center, inner sep=0}, curve={height=18pt}, from=1-1, to=1-3]
  \arrow[""{name=2, anchor=center, inner sep=0}, from=1-1, to=1-3]
  \arrow["\alpha", shorten <=2pt, shorten >=2pt, Rightarrow, from=0, to=2]
  \arrow["\beta", shorten <=2pt, shorten >=2pt, Rightarrow, from=2, to=1]
\end{tikzcd}\]
~~~

[category]: Cat.Base.html

```agda
record Prebicategory o ℓ ℓ′ : Type (lsuc (o ⊔ ℓ ⊔ ℓ′)) where
  no-eta-equality
  field
    Ob  : Type o
    Hom : Ob → Ob → Precategory ℓ ℓ′
```

Zooming out to consider the whole bicategory, we see that each object
has a specified identity 1-cell as in the case for ordinary categories,
but the composition operation, rather than being a function, is a
funct*or*. This, intuitively, makes sense: since we have replaced our
$\hom$-sets with $\hom$-precategories, we should replace our maps of
sets for maps of precategories, i.e., functors.

```agda
  field
    id      : ∀ {A} → Precategory.Ob (Hom A A)
    compose : ∀ {A B C} → Functor (Hom B C ×ᶜ Hom A B) (Hom A C)
```

Before moving on to the isomorphisms witnessing identity and
associativity, we introduce a bunch of notation for the different
classes of maps and all the composition operations. Observe that the
action of the composition functor on homotopies reduces "horizontal"
pasting diagrams like

~~~{.quiver .short-05}
\[\begin{tikzcd}
  A & B & {C\text{,}}
  \arrow[""{name=0, anchor=center, inner sep=0}, "{g_1}", curve={height=-12pt}, from=1-1, to=1-2]
  \arrow[""{name=1, anchor=center, inner sep=0}, "{g_2}"', curve={height=12pt}, from=1-1, to=1-2]
  \arrow[""{name=2, anchor=center, inner sep=0}, "{f_1}", curve={height=-12pt}, from=1-2, to=1-3]
  \arrow[""{name=3, anchor=center, inner sep=0}, "{f_2}"', curve={height=12pt}, from=1-2, to=1-3]
  \arrow["\alpha", shorten <=3pt, shorten >=3pt, Rightarrow, from=0, to=1]
  \arrow["\beta"', shorten <=3pt, shorten >=3pt, Rightarrow, from=2, to=3]
\end{tikzcd}\]
~~~

whence the name **horizontal composition**.

```agda
  _↦_ : Ob → Ob → Type ℓ
  A ↦ B = Precategory.Ob (Hom A B)

  _⇒_ : ∀ {A B} (f g : A ↦ B) → Type ℓ′
  _⇒_ {A} {B} f g = Precategory.Hom (Hom A B) f g

  -- 1-cell composition
  _∘_ : ∀ {A B C} (f : B ↦ C) (g : A ↦ B) → A ↦ C
  f ∘ g = compose .Functor.F₀ (f , g)

  -- vertical 2-cell composition
  _⊗_ : ∀ {A B} {f g h : A ↦ B} → g ⇒ h → f ⇒ g → f ⇒ h
  _⊗_ {A} {B} = Cr._∘_ (Hom A B)

  -- horizontal 2-cell composition
  _◆_ : ∀ {A B C} {f₁ f₂ : B ↦ C} (β : f₁ ⇒ f₂) {g₁ g₂ : A ↦ B} (α : g₁ ⇒ g₂)
      → (f₁ ∘ g₁) ⇒ (f₂ ∘ g₂)
  _◆_ β α = compose .Functor.F₁ (β , α)

  infixr 30 _∘_
  infixr 25 _⊗_

  -- whiskering on the right
  _▶_ : ∀ {A B C} (f : B ↦ C) {a b : A ↦ B} (g : a ⇒ b) → f ∘ a ⇒ f ∘ b
  _▶_ {A} {B} {C} f g = compose .Functor.F₁ (Cr.id (Hom B C) , g)

  -- whiskering on the left
  _◀_ : ∀ {A B C} {a b : B ↦ C} (g : a ⇒ b) (f : A ↦ B) → a ∘ f ⇒ b ∘ f
  _◀_ {A} {B} {C} g f = compose .Functor.F₁ (g , Cr.id (Hom A B))
```

We now move onto the invertible 2-cells witnessing that the chosen
identity map is a left- and right- unit element for the composition
functor, and that composition is associative. In reality, to get a fully
coherent structure, we need these invertible 2-cells to be given as
natural isomorphisms, e.g. $(\id{id} \circ -) \id{Id}$, which witnesses
that the functor "compose with the identity 1-cell on the left" is
naturally isomorphic to the identity functor.

```agda
  field
    unitor-l : ∀ {A B} → Cr._≅_ Cat[ Hom A B , Hom A B ] Id (Bi.Right compose id)
    unitor-r : ∀ {A B} → Cr._≅_ Cat[ Hom A B , Hom A B ] Id (Bi.Left compose id)

    associator
      : ∀ {A B C D}
      → Cr._≅_ Cat[ Hom C D ×ᶜ Hom B C ×ᶜ Hom A B , Hom A D ]
        (compose-assocˡ {H = Hom} compose)
        (compose-assocʳ {H = Hom} compose)
```

It's traditional to refer to the left unitor as $\lambda$, to the right
unitor as $\rho$, and to the associator as $\alpha$, so we set up those
abbreviations here too:

```agda
  λ← : ∀ {A B} (f : A ↦ B) → id ∘ f ⇒ f
  λ← = unitor-l .Cr._≅_.from .η

  λ→ : ∀ {A B} (f : A ↦ B) → f ⇒ id ∘ f
  λ→ = unitor-l .Cr._≅_.to .η

  ρ← : ∀ {A B} (f : A ↦ B) → f ∘ id ⇒ f
  ρ← = unitor-r .Cr._≅_.from .η

  ρ→ : ∀ {A B} (f : A ↦ B) → f ⇒ f ∘ id
  ρ→ = unitor-r .Cr._≅_.to .η

  α→ : ∀ {A B C D} (f : C ↦ D) (g : B ↦ C) (h : A ↦ B)
     → (f ∘ g) ∘ h ⇒ f ∘ (g ∘ h)
  α→ f g h = associator .Cr._≅_.to .η (f , g , h)

  α← : ∀ {A B C D} (f : C ↦ D) (g : B ↦ C) (h : A ↦ B)
     → f ∘ (g ∘ h) ⇒ (f ∘ g) ∘ h
  α← f g h = associator .Cr._≅_.from .η (f , g , h)
```

The final data we need are coherences relating the left and right
unitors (the **triangle identity**, nothing to do with adjunctions), and
one for reducing sequences of associators, the **pentagon identity**. As
for where the name "pentagon" comes from, the path `pentagon`{.Agda}
witnesses commutativity of the diagram

~~~{.quiver .tall-2}
\[\begin{tikzcd}
  && {f(g(hi))} \\
  \\
  {(fg)(hi)} &&&& {f((gh)i)} \\
  \\
  & {((fg)h)i} && {(f(gh))i\text{.}}
  \arrow["{\alpha({f,g,h})\triangleleft i}"', from=5-2, to=5-4]
  \arrow["{\alpha(f,gh, i)}"', from=5-4, to=3-5]
  \arrow["{f\triangleright\alpha(g,h,i)}"'{pos=0.2}, from=3-5, to=1-3]
  \arrow["{\alpha(fg,h,i)}", from=5-2, to=3-1]
  \arrow["{\alpha(f,g,hi)}"{pos=0.2}, from=3-1, to=1-3]
\end{tikzcd}\]
~~~

```agda
  field
    triangle
      : ∀ {A B C} (f : B ↦ C) (g : A ↦ B)
      → (ρ← f ◀ g) ⊗ α← f id g ≡ f ▶ λ← g

    pentagon
      : ∀ {A B C D E} (f : D ↦ E) (g : C ↦ D) (h : B ↦ C) (i : A ↦ B)
      → (α← f g h ◀ i) ⊗ α← f (g ∘ h) i ⊗ (f ▶ α← g h i)
      ≡ α← (f ∘ g) h i ⊗ α← f g (h ∘ i)
```

## The bicategory of categories

Just like the prototypal example of categories is the category of sets,
the prototypal example of bicategory is the bicategory of categories. We
observe that, without a bound of h-level on the spaces of objects
([strict categories]), the collection of categories of a given universe
level does _not_ form a category, but it _does_ form a bicategory.

[strict categories]: Cat.Instances.StrictCat.html

```agda
Cat : ∀ o ℓ → Prebicategory (lsuc o ⊔ lsuc ℓ) (o ⊔ ℓ) (o ⊔ ℓ)
Cat o ℓ = pb where
  open Prebicategory
  open Functor

  pb : Prebicategory _ _ _
  pb .Ob = Precategory o ℓ
  pb .Hom = Cat[_,_]
  pb .id = Id
```

The first thing we must compute is that the functor composition operator
$- \circ -$ extends to a functor composition _functor_, which is
annoying but straightforward.

```agda
  pb .compose .F₀ (F , G) = F F∘ G

  pb .compose {C = C} .F₁ {y = y , _} (n1 , n2) .η x =
    y .F₁ (n2 .η _) C.∘ n1 .η _
    where module C = Precategory C

  pb .compose {C = C} .F₁ {x = F , G} {y = W , X} (n1 , n2) .is-natural _ _ f =
    (W .F₁ (n2 .η _) C.∘ n1 .η _) C.∘ F .F₁ (G .F₁ f) ≡⟨ C.pullr (n1 .is-natural _ _ _) ⟩
    W .F₁ (n2 .η _) C.∘ W .F₁ (G .F₁ f) C.∘ n1 .η _   ≡⟨ C.extendl (W.weave (n2 .is-natural _ _ _)) ⟩
    W .F₁ (X .F₁ f) C.∘ W .F₁ (n2 .η _) C.∘ n1 .η _   ∎
    where module C = Cr C
          module W = Fr W

  pb .compose {C = C} .F-id {x} = Nat-path λ _ → Cr.idr C _ ∙ x .fst .F-id
  pb .compose {C = C} .F-∘ {x} {y} {z} f g = Nat-path λ _ →
    z .fst .F₁ _ C.∘ f .fst .η _ C.∘ g .fst .η _                      ≡⟨ C.pushl (z .fst .F-∘ _ _) ⟩
    z .fst .F₁ _ C.∘ z .fst .F₁ _ C.∘ f .fst .η _ C.∘ g .fst .η _     ≡⟨ C.extend-inner (sym (f .fst .is-natural _ _ _)) ⟩
    z .fst .F₁ _ C.∘ f .fst .η _ C.∘ y .fst .F₁ _ C.∘ g .fst .η _     ≡⟨ solve C ⟩
    (z .fst .F₁ _ C.∘ f .fst .η _) C.∘ (y .fst .F₁ _ C.∘ g .fst .η _) ∎
    where module C = Cr C
```

The unitors and associator are given in components by the identity
2-cells, since componentwise the functor composition $\id{Id} \circ F$
evaporates, leaving only $F$ behind. Unfortunately, this equation is not
definitional, so we can not use the identity natural isomorphism
directly:

```agda
  pb .unitor-r {B = B} =
    make-natural-iso (λ x → NT (λ _ → B.id) λ _ _ f → B.id-comm-sym)
      (λ x → componentwise-invertible→invertible _
              (λ _ → B.make-invertible B.id (B.idl _) (B.idl _)))
      (λ x y f → Nat-path λ _ → B.idr _ ∙ ap (B._∘ _) (y .F-id))
    where module B = Cr B

  pb .unitor-l {B = B} =
    make-natural-iso (λ x → NT (λ _ → B.id) λ _ _ f → B.id-comm-sym)
      (λ x → componentwise-invertible→invertible _
              (λ _ → B.make-invertible B.id (B.idl _) (B.idl _)))
      (λ x y f → Nat-path λ _ → B.idr _ ∙ B.id-comm)
    where module B = Cr B

  pb .associator {A} {B} {C} {D} =
    make-natural-iso (λ x → NT (λ _ → D.id) λ _ _ f → D.id-comm-sym)
      (λ x → componentwise-invertible→invertible _
              (λ _ → D.make-invertible D.id (D.idl _) (D.idl _)))
      λ x y f → Nat-path λ _ → D.idr _ ·· D.pushl (y .fst .F-∘ _ _) ·· D.introl refl
    where module D = Cr D

  pb .triangle {C = C} f g = Nat-path (λ _ → Cr.idr C _)
  pb .pentagon {E = E} f g h i =
    Nat-path λ _ → ap₂ E._∘_
      (E.eliml (ap (f .F₁) (ap (g .F₁) (h .F-id)) ·· ap (f .F₁) (g .F-id) ·· f .F-id))
      (E.elimr (E.eliml (f .F-id)))
    where module E = Cr E
```

# Pseudofunctors

In the same way that the definition of bicategory is obtained by
starting with the definition of category and replacing the $\hom$-sets
by $\hom$-categories (and adding coherence data to make sure the
resulting structure is well-behaved), one can start with the definition
of functor and replace the _function_ between $\hom$-sets by _functors_
between $\hom$-categories. The resulting object is called a
**pseudofunctor** from $\bf{B}$ to $\bf{C}$. Analogously to the triangle
and pentagon identities, weakening the functoriality axioms to specified
_functoriality invertible 2-cells_ means that we have to put in some
coherence axioms for those 2-cells.

```agda
record
  Pseudofunctor (B : Prebicategory o ℓ ℓ′) (C : Prebicategory o₁ ℓ₁ ℓ₁′)
    : Type (o ⊔ o₁ ⊔ ℓ ⊔ ℓ₁ ⊔ ℓ′ ⊔ ℓ₁′) where

  private
    module B = Prebicategory B
    module C = Prebicategory C

  field
    P₀ : B.Ob → C.Ob
    P₁ : ∀ {A B} → Functor (B.Hom A B) (C.Hom (P₀ A) (P₀ B))
```

Functoriality is witnessed by the `compositor`{.Agda} and
`unitor`{.Agda} natural isomorphisms, which (in components) say that
$F_1(f)F_1(g) \cong F_1(fg)$ and $F_1(\id{id}) \cong \id{id}$.

```agda
    compositor : ∀ {A B C} →
      Cr._≅_ Cat[ B.Hom B C ×ᶜ B.Hom A B , C.Hom (P₀ A) (P₀ C) ]
        (C.compose F∘ Cat⟨ P₁ F∘ Fst , P₁ F∘ Snd ⟩)
        (P₁ F∘ B.compose)

    unitor : ∀ {A} →
      Cr._≅_ Cat[ C.Hom (P₀ A) (P₀ A) , C.Hom (P₀ A) (P₀ A) ]
        Id (P₁ F∘ Const B.id)
```

<!--
```agda
  module P₁ {A} {B} = Functor (P₁ {A} {B})

  F₁ : ∀ {a b} → a B.↦ b → P₀ a C.↦ P₀ b
  F₁ = P₁.F₀

  F₂ : ∀ {a b} {f g : a B.↦ b} → f B.⇒ g → F₁ f C.⇒ F₁ g
  F₂ = P₁.F₁

  γ→ : ∀ {a b c} (f : b B.↦ c) (g : a B.↦ b)
     → F₁ f C.∘ F₁ g C.⇒ F₁ (f B.∘ g)
  γ→ f g = compositor .Cr._≅_.to .η (f , g)

  γ← : ∀ {a b c} (f : b B.↦ c) (g : a B.↦ b)
     → F₁ (f B.∘ g) C.⇒ F₁ f C.∘ F₁ g
  γ← f g = compositor .Cr._≅_.from .η (f , g)

  ι→ : ∀ {a} → C.id C.⇒ F₁ B.id
  ι→ {a} = unitor .Cr._≅_.to .η (C.id {P₀ a})

  ι← : ∀ {a} → F₁ B.id C.⇒ C.id
  ι← {a} = unitor .Cr._≅_.from .η (C.id {P₀ a})
```
-->

These are required to satisfy the following three coherence diagrams,
relating the compositor to the associators, and the three unitors
between themselves. We sketch the diagram which `hexagon`{.Agda}
witnesses commutativity for, but leave the `right-unit`{.Agda} and
`left-unit`{.Agda} diagrams unwritten.

~~~{.quiver .tall-2}
\[\begin{tikzcd}
  & {F(hg)Ff} && {F((hg)f)} \\
  \\
  {(FhFg)Ff} &&&& {F(h(gf))} \\
  \\
  & {Fh(FgFf)} && {FhF(gf)}
  \arrow["\alpha", from=3-1, to=5-2]
  \arrow["{\gamma \blacktriangleleft Ff}"', from=3-1, to=1-2]
  \arrow["\gamma"', from=1-2, to=1-4]
  \arrow["F\alpha"', from=1-4, to=3-5]
  \arrow["Fh\blacktriangleright\gamma", from=5-2, to=5-4]
  \arrow["\gamma", from=5-4, to=3-5]
\end{tikzcd}\]
~~~

```agda
  field
    hexagon
      : ∀ {a b c d} (f : c B.↦ d) (g : b B.↦ c) (h : a B.↦ b)
      → F₂ (B.α→ f g h) C.⊗ γ→ (f B.∘ g) h C.⊗ (γ→ f g C.◀ F₁ h)
      ≡ γ→ f (g B.∘ h) C.⊗ (F₁ f C.▶ γ→ g h) C.⊗ C.α→ (F₁ f) (F₁ g) (F₁ h)

    right-unit
      : ∀ {a b} (f : a B.↦ b)
      → F₂ (B.ρ← f) C.⊗ γ→ f B.id C.⊗ (F₁ f C.▶ ι→) ≡ C.ρ← (F₁ f)

    left-unit
      : ∀ {a b} (f : a B.↦ b)
      → F₂ (B.λ← f) C.⊗ γ→ B.id f C.⊗ (ι→ C.◀ F₁ f) ≡ C.λ← (F₁ f)
```
