<!--
```agda
open import Cat.Functor.Naturality
open import Cat.Functor.Bifunctor
open import Cat.Instances.Product
open import Cat.Functor.Compose renaming (_◆_ to _◇_)
open import Cat.Functor.Closed
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as Fr
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Bi.Base where
```

# Prebicategories {defines="bicategory prebicategory"}

<!--
```agda
open _=>_

module _ {o ℓ ℓ'} {O : Type o} (H : O → O → Precategory ℓ ℓ') (C : ∀ {A B C} → Bifunctor (H B C) (H A B) (H A C)) where
  private module C {a b c} = Bifunctor (C {a} {b} {c})
  open Functor

  compose-assocˡ : ∀ {A B C D} → Functor (H C D ×ᶜ H B C ×ᶜ H A B) (H A D)
  compose-assocˡ .F₀ (F , G , H) = C · (C · F · G) · H
  compose-assocˡ .F₁ (f , g , h) = (f C.◆ g) C.◆ h
  compose-assocˡ .F-id = ap₂ C._◆_ C.◆-id refl ∙ C.◆-id
  compose-assocˡ .F-∘ f g = ap₂ C._◆_ C.◆-∘ refl ∙ C.◆-∘

  compose-assocʳ
    : ∀ {A B C D} → Functor (H C D ×ᶜ H B C ×ᶜ H A B) (H A D)
  compose-assocʳ .F₀ (F , G , H) = C · F · (C · G · H)
  compose-assocʳ .F₁ (f , g , h) = f C.◆ (g C.◆ h)
  compose-assocʳ .F-id = ap₂ C._◆_ refl C.◆-id ∙ C.◆-id
  compose-assocʳ .F-∘ f g = ap₂ C._◆_ refl C.◆-∘ ∙ C.◆-∘

  Associator-for : Type _
  Associator-for = ∀ {A B C D} →
    Cr._≅_ Cat[ H C D ×ᶜ H B C ×ᶜ H A B , H A D ]
      compose-assocˡ compose-assocʳ

private variable o ℓ ℓ' o₁ ℓ₁ ℓ₁' : Level
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

~~~{.quiver}
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
record Prebicategory o ℓ ℓ' : Type (lsuc (o ⊔ ℓ ⊔ ℓ')) where
  no-eta-equality
  field
    Ob  : Type o
    Hom : Ob → Ob → Precategory ℓ ℓ'

  module Hom {A} {B} = Precategory (Hom A B) hiding (Ob ; Hom ; _∘_)
```

Zooming out to consider the whole bicategory, we see that each object
has a specified identity 1-cell as in the case for ordinary categories,
but the composition operation, rather than being a function, is a
funct*or*. This, intuitively, makes sense: since we have replaced our
$\hom$-sets with $\hom$-precategories, we should replace our maps of
sets for maps of precategories, i.e., functors.

```agda
  field
    id      : ∀ {A} → ⌞ Hom A A ⌟
    compose : ∀ {A B C} → Bifunctor (Hom B C) (Hom A B) (Hom A C)
```

Before moving on to the isomorphisms witnessing identity and
associativity, we introduce a bunch of notation for the different
classes of maps and all the composition operations. Observe that the
action of the composition functor on homotopies reduces "horizontal"
pasting diagrams like

~~~{.quiver}
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

whence the name **horizontal composition**. This is the common diagonal
of the naturality square for the left action of `compose`{.Agda},
considered as a [[bifunctor]].

<details>
<summary>As discussed there, we define the abbreviations for the
notation native to a bicategory natively through the module
system.</summary>

```agda
  module compose {a b c} = Bifunctor (compose {a} {b} {c}) hiding (_◀_ ; _▶_ ; F₀)
  private
    open module ↦ A B = Precategory (Hom A B)
      public using () renaming (Ob to _↦_)

    open module Hom₁ {A B} = Precategory (Hom A B)
      public using () renaming (Hom to _⇒_ ; _∘_ to infixr 30 _∘_)

    open module compose₀ {A B C} = Bifunctor (compose {A} {B} {C})
      public using (_◀_ ; _▶_ ; _◆_) renaming (F₀ to infixr 25 _⊗_)
```

</details>

We now move onto the invertible 2-cells witnessing that the chosen
identity map is a left- and right- unit element for the composition
functor, and that composition is associative. In reality, to get a fully
coherent structure, we need these invertible 2-cells to be given as
natural isomorphisms, e.g. $(\id \circ -) \cong \id$, which witnesses
that the functor "compose with the identity 1-cell on the left" is
naturally isomorphic to the identity functor.

```agda
  field
    unitor-l : ∀ {A B} → Cr._≅_ Cat[ Hom A B , Hom A B ] Id (Bifunctor.Right compose id)
    unitor-r : ∀ {A B} → Cr._≅_ Cat[ Hom A B , Hom A B ] Id (Bifunctor.Left compose id)

    associator
      : ∀ {A B C D}
      → Cr._≅_ Cat[ Hom C D ×ᶜ Hom B C ×ᶜ Hom A B , Hom A D ]
        (compose-assocˡ Hom compose)
        (compose-assocʳ Hom compose)

  module unitor-l {a b} = Cr._≅_ _ (unitor-l {a} {b})
  module unitor-r {a b} = Cr._≅_ _ (unitor-r {a} {b})
  module associator {a b c d} = Cr._≅_ _ (associator {a} {b} {c} {d})
```

<details>
<summary>It's traditional to refer to the left unitor as $\lambda$, to
the right unitor as $\rho$, and to the associator as $\alpha$, so we set
up those abbreviations here too:
</summary>

```agda
  private
    open module λ← {a b} = _=>_ (unitor-l.from {a} {b})
      public using () renaming (η to λ←)
    open module λ→ {a b} = _=>_ (unitor-l.to   {a} {b})
      public using () renaming (η to λ→)

    open module ρ← {a b} = _=>_ (unitor-r.from {a} {b})
      public using () renaming (η to ρ←)
    open module ρ→ {a b} = _=>_ (unitor-r.to   {a} {b})
      public using () renaming (η to ρ→)

    open module α→ {a b c d} = _=>_ (associator.to {a} {b} {c} {d})
      renaming (η to α→) using () public

    open module α← {a b c d} = _=>_ (associator.from {a} {b} {c} {d})
      renaming (η to α←) using () public

  ρ←nat : ∀ {A B} {f f' : A ↦ B} (β : f ⇒ f')
        → Path ((f ⊗ id) ⇒ f') (ρ← _ ∘ (β ◀ id)) (β ∘ ρ← _)
  ρ←nat {A} {B} {f} {f'} β = ρ←.is-natural f f' β

  λ←nat : ∀ {A B} {f f' : A ↦ B} (β : f ⇒ f')
        → Path ((id ⊗ f) ⇒ f') (λ← _ ∘ (id ▶ β)) (β ∘ λ← _)
  λ←nat {A} {B} {f} {f'} β = λ←.is-natural f f' β

  ρ→nat : ∀ {A B} {f f' : A ↦ B} (β : f ⇒ f')
        → Path (f ⇒ f' ⊗ id) (ρ→ _ ∘ β) ((β ◀ id) ∘ ρ→ _)
  ρ→nat {A} {B} {f} {f'} β = ρ→.is-natural f f' β

  λ→nat : ∀ {A B} {f f' : A ↦ B} (β : f ⇒ f')
        → Path (f ⇒ id ⊗ f') (λ→ _ ∘ β) ((id ▶ β) ∘ λ→ _)
  λ→nat {A} {B} {f} {f'} β = λ→.is-natural f f' β

  α←nat : ∀ {A B C D} {f f' : C ↦ D} {g g' : B ↦ C} {h h' : A ↦ B}
        → (β : f ⇒ f') (γ : g ⇒ g') (δ : h ⇒ h')
        → Path (f ⊗ g ⊗ h ⇒ ((f' ⊗ g') ⊗ h'))
          (α← _ ∘ (β ◆ (γ ◆ δ))) (((β ◆ γ) ◆ δ) ∘ α← _)
  α←nat {A} {B} {C} {D} {f} {f'} {g} {g'} {h} {h'} β γ δ =
    α←.is-natural (f , g , h) (f' , g' , h') (β , γ , δ)

  α→nat : ∀ {A B C D} {f f' : C ↦ D} {g g' : B ↦ C} {h h' : A ↦ B}
        → (β : f ⇒ f') (γ : g ⇒ g') (δ : h ⇒ h')
        → Path ((f ⊗ g) ⊗ h ⇒ (f' ⊗ g' ⊗ h'))
           (α→ _ ∘ ((β ◆ γ) ◆ δ)) ((β ◆ (γ ◆ δ)) ∘ α→ _)
  α→nat {A} {B} {C} {D} {f} {f'} {g} {g'} {h} {h'} β γ δ =
    α→.is-natural (f , g , h) (f' , g' , h') (β , γ , δ)
```

</details>

The final data we need are coherences relating the left and right
unitors (the **triangle identity**, nothing to do with adjunctions), and
one for reducing sequences of associators, the **pentagon identity**. As
for where the name "pentagon" comes from, the path `pentagon`{.Agda}
witnesses commutativity of the diagram

~~~{.quiver}
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
      → (ρ← f ◀ g) ∘ α← (f , id , g) ≡ f ▶ λ← g

    pentagon
      : ∀ {A B C D E} (f : D ↦ E) (g : C ↦ D) (h : B ↦ C) (i : A ↦ B)
      → (α← (f , g , h) ◀ i) ∘ α← (f , g ⊗ h , i) ∘ (f ▶ α← (g , h , i))
      ≡ α← (f ⊗ g , h , i) ∘ α← (f , g , h ⊗ i)
```

Our coherence diagrams for bicategorical data are taken from
[@basicbicats], which contains all the diagrams we have omitted.
However, we do not adopt their (dated) terminology of "homomorphism" and
"strict homomorphism". In contrast with _our_ convention for
1-categories, we refer to bicategories using bold capital letters:
$\bf{B}$, $\bf{C}$.

<!--
```agda
instance
  Underlying-Prebicategory : Underlying (Prebicategory o ℓ ℓ')
  Underlying-Prebicategory = record { ⌞_⌟ = Prebicategory.Ob }

module _ (B : Prebicategory o ℓ ℓ') where
  open Prebicategory B

  postaction : ∀ {a b c} (f : a ↦ b) → Functor (Hom c a) (Hom c b)
  postaction = Bifunctor.Right compose

  preaction : ∀ {a b c} (f : a ↦ b) → Functor (Hom b c) (Hom a c)
  preaction = Bifunctor.Left compose
```
-->

## The bicategory of categories {defines="Cat bicategory-of-categories"}

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
```

<!--
```agda
  assoc : Associator-for Cat[_,_] F∘-functor
  assoc {C = C} {D = D} = to-natural-iso ni where
    module D = Cr D using (id ; idl ; idr ; pushr ; introl ; id-comm-sym)
    ni : make-natural-iso {D = Cat[ _ , _ ]} _ _
    ni .make-natural-iso.eta x = NT (λ _ → D.id) λ _ _ _ → D.id-comm-sym
    ni .make-natural-iso.inv x = NT (λ _ → D.id) λ _ _ _ → D.id-comm-sym
    ni .make-natural-iso.eta∘inv x = ext λ _ → D.idl _
    ni .make-natural-iso.inv∘eta x = ext λ _ → D.idl _
    ni .make-natural-iso.natural (X₀ , X₁ , X₂) _ _ = ext λ _ →
      D.idr _ ∙∙ D.pushr (X₀ .F-∘ _ _) ∙∙ D.introl refl
```
-->

```agda
  pb : Prebicategory _ _ _
  pb .Ob = Precategory o ℓ
  pb .Hom = Cat[_,_]
  pb .id = Id
```

The first thing we must compute is that the functor composition operator
$- \circ -$ extends to a functor composition _functor_, which we have
already done (but off-screen, since its construction is very
straightforward).

```agda
  pb .compose = F∘-functor
```

The unitors and associator are almost, but not quite, given by the
identity 2-cells, since componentwise the functor composition $\id \circ
F$ evaporates, leaving only $F$ behind. Unfortunately, this equation is
not definitional, so we can not use the identity natural isomorphism
directly:

```agda
  pb .unitor-r {B = B} = to-natural-iso ni where
    module B = Cr B using (id ; _∘_ ; idl ; idr ; id-comm-sym ; id-comm)
    ni : make-natural-iso {D = Cat[ _ , _ ]} _ _
    ni .make-natural-iso.eta x = NT (λ _ → B.id) λ _ _ _ → B.id-comm-sym
    ni .make-natural-iso.inv x = NT (λ _ → B.id) λ _ _ _ → B.id-comm-sym
    ni .make-natural-iso.eta∘inv x = ext λ _ → B.idl _
    ni .make-natural-iso.inv∘eta x = ext λ _ → B.idl _
    ni .make-natural-iso.natural x y f = ext λ _ → B.id-comm

  pb .unitor-l {B = B} = to-natural-iso ni where
    module B = Cr B using (id ; idl ; idr ; id-comm ; id-comm-sym)
    ni : make-natural-iso {D = Cat[ _ , _ ]} _ _
    ni .make-natural-iso.eta x = NT (λ _ → B.id) λ _ _ _ → B.id-comm-sym
    ni .make-natural-iso.inv x = NT (λ _ → B.id) λ _ _ _ → B.id-comm-sym
    ni .make-natural-iso.eta∘inv x = ext λ _ → B.idl _
    ni .make-natural-iso.inv∘eta x = ext λ _ → B.idl _
    ni .make-natural-iso.natural x y f = ext λ _ → B.id-comm

  pb .associator = assoc

  pb .triangle {C = C} f g = ext λ _ → C .Cr.idl _ ∙ sym (f .F-id)
  pb .pentagon {E = E} f g h i = ext λ _ → ap₂ E._∘_ refl (E.elimr (f .F-id))
    where module E = Cr E using (_∘_ ; elimr)
```

# Lax functors {defines="lax-functor"}

In the same way that the definition of bicategory is obtained by
starting with the definition of category and replacing the $\hom$-sets
by $\hom$-categories (and adding coherence data to make sure the
resulting structure is well-behaved), one can start with the definition
of functor and replace the _function_ between $\hom$-sets by _functors_
between $\hom$-categories.

However, when talking about general bicategories, we are faced with a
choice: We could generalise the functoriality axioms to natural
isomorphisms, keeping with the fact that equations are invertible, but
we could also drop this invertibility requirement, and work only with
natural _transformations_ $P(\id_A) \to \id_{PA}$. When these
are not invertible, the resulting structure is called a **lax functor**;
When they _are_, we talk about **pseudofunctors** instead.

```agda
record
  Lax-functor (B : Prebicategory o ℓ ℓ') (C : Prebicategory o₁ ℓ₁ ℓ₁')
    : Type (o ⊔ o₁ ⊔ ℓ ⊔ ℓ₁ ⊔ ℓ' ⊔ ℓ₁') where
  no-eta-equality

  private
    module B = Prebicategory B
    module C = Prebicategory C

  field
    P₀ : B.Ob → C.Ob
    P₁ : ∀ {A B} → Functor (B.Hom A B) (C.Hom (P₀ A) (P₀ B))
```

The resulting structure has "directed functoriality", witnessed by the
`compositor`{.Agda} and `unitor`{.Agda} natural transformations, which
have components $F_1(f)F_1(g) \To F_1(fg)$ and $\id \To F_1(\id)$.

```agda
    compositor
      : ∀ {A B C}
      → Uncurry C.compose F∘ (P₁ {B} {C} F× P₁ {A} {B}) => P₁ F∘ Uncurry B.compose

    unitor : ∀ {A} → C.id C.⇒ P₁ .Functor.F₀ (B.id {A = A})
```

<!--
```agda
  open module P₁ {A} {B} = Functor (P₁ {A} {B}) renaming (F₀ to ₁ ; F₁ to ₂) using () public

  ₀ : B.Ob → C.Ob
  ₀ = P₀

  υ→ : ∀ {A} → C.id C.⇒ P₁ .Functor.F₀ (B.id {A = A})
  υ→ = unitor

  private
    open module γ→ {a} {b} {c} = _=>_ (compositor {a} {b} {c}) renaming (η to γ→) using () public

  γ→nat
    : ∀ {A B C} {f f' : B B.↦ C} {g g' : A B.↦ B} (β : f B.⇒ f') (δ : g B.⇒ g')
    → γ→ (f' , g') C.∘ (₂ β C.◆ ₂ δ) ≡ ₂ (β B.◆ δ) C.∘ γ→ (f , g)
  γ→nat {A} {B} {C} {f} {f'} {g} {g'} β δ = γ→.is-natural (f , g) (f' , g') (β , δ)
```
-->

Additionally, we require the following three equations to hold, relating
the compositor transformation to the associators, and the three unitors
between themselves. We sketch the diagram which `hexagon`{.Agda}
witnesses commutativity for, but leave the `right-unit`{.Agda} and
`left-unit`{.Agda} diagrams undrawn (they're boring commutative
squares).

~~~{.quiver}
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
      → ₂ (B.α→ (f , g , h)) C.∘ γ→ (f B.⊗ g , h) C.∘ (γ→ (f , g) C.◀ ₁ h)
      ≡ γ→ (f , g B.⊗ h) C.∘ (₁ f C.▶ γ→ (g , h)) C.∘ C.α→ (₁ f , ₁ g , ₁ h)

    right-unit
      : ∀ {a b} (f : a B.↦ b)
      → ₂ (B.ρ← f) C.∘ γ→ (f , B.id) C.∘ (₁ f C.▶ unitor) ≡ C.ρ← (₁ f)

    left-unit
      : ∀ {a b} (f : a B.↦ b)
      → ₂ (B.λ← f) C.∘ γ→ (B.id , f) C.∘ (unitor C.◀ ₁ f) ≡ C.λ← (₁ f)
```

## Pseudofunctors {defines="pseudofunctor"}

As mentioned above, a lax functor with invertible unitors and compositor
is called a **pseudofunctor**. Every pseudofunctor has an underlying
`lax`{.Agda} functor. Since invertibility is a _property_ of 2-cells
(rather than structure on 2-cells), "being pseudo" is a property of lax
functors, not additional structure on lax functors.

```agda
record
  Pseudofunctor (B : Prebicategory o ℓ ℓ') (C : Prebicategory o₁ ℓ₁ ℓ₁')
    : Type (o ⊔ o₁ ⊔ ℓ ⊔ ℓ₁ ⊔ ℓ' ⊔ ℓ₁') where
  no-eta-equality

  private
    module B = Prebicategory B
    module C = Prebicategory C

  field
    lax : Lax-functor B C

  open Lax-functor lax public

  field
    unitor-inv
      : ∀ {a} → Cr.is-invertible (C.Hom _ _) (υ→ {a})
    compositor-inv
      : ∀ {a b c} (fg : b B.↦ c × a B.↦ b) → Cr.is-invertible (C.Hom _ _) (γ→ fg)
```

<!--
```agda
  private
    open module υ← {a} =
      Cr.is-invertible (C.Hom _ _) (unitor-inv {a})
      renaming (inv to υ←) using () public

    open module γ← {a b c} fg =
      Cr.is-invertible (C.Hom _ _) (compositor-inv {a} {b} {c} fg)
      renaming (inv to γ←) using () public

  γ←nat
    : ∀ {A B C} {f f' : B B.↦ C} {g g' : A B.↦ B} (β : f B.⇒ f') (δ : g B.⇒ g')
    → γ← (f' , g') C.∘ ₂ (β B.◆ δ) ≡ (₂ β C.◆ ₂ δ) C.∘ γ← (f , g)
  γ←nat {A} {B} {C} {f} {f'} {g} {g'} β δ = inverse-is-natural compositor γ←
    (λ fg → γ←.inverses fg .invl) (λ fg → γ←.inverses fg .invr)
    (f , g) (f' , g') (β , δ)
    where open Cr.Inverses
```
-->

# Lax transformations {defines="lax-transformation"}

By dropping the invertibility requirement when generalising natural
transformations to lax functors, we obtain the type of **lax
transformations** between lax functors. If every 2-cell component of the
lax transformation is invertible, we refer to it as a **pseudonatural
transformation**. We omit the word "natural" in "lax natural
transformation" for brevity.

<!--
```agda
module
  _ {B : Prebicategory o ℓ ℓ'} {C : Prebicategory o₁ ℓ₁ ℓ₁'}
    (F : Lax-functor B C) (G : Lax-functor B C)
  where
  private
    module B = Prebicategory B
    module C = Prebicategory C
    module F = Lax-functor F
    module G = Lax-functor G
```
-->

The transformation which witnesses directed naturality for a lax
transformation is called the `naturator`{.Agda}. In components, it
witnesses commutativity of the diagram

~~~{.quiver}
\[\begin{tikzcd}
  {\mathbf{B}(A,B)} && {\mathbf{C}(FA,FB)} \\
  \\
  {\mathbf{C}(GA,GB)} && {\mathbf{C}(FA,GB)\text{,}}
  \arrow["F", from=1-1, to=1-3]
  \arrow["G"', from=1-1, to=3-1]
  \arrow["{\sigma^*}"', from=3-1, to=3-3]
  \arrow["{\sigma_*}", from=1-3, to=3-3]
  \arrow["\nu"{description}, Rightarrow, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

and thus consists of a natural family of 2-cells $G(f)\sigma_a \To
\sigma_bF(f)$.

```agda
  record _=>ₗ_ : Type (o ⊔ ℓ ⊔ ℓ₁ ⊔ ℓ' ⊔ ℓ₁') where
    no-eta-equality
    field
      σ : ∀ A → F.₀ A C.↦ G.₀ A
      naturator
        : ∀ {a b}
        → preaction C (σ b) F∘ G.P₁ => postaction C (σ a) F∘ F.P₁

    private
      open module ν→ {a} {b} = _=>_ (naturator {a} {b}) renaming (η to ν→) using () public

    ν→nat :
      ∀ {A B} {f g : B B.↦ A} (α : f B.⇒ g)
      → ν→ g C.∘ G.₂ α C.◀ σ B ≡ σ A C.▶ F.₂ α C.∘ ν→ f
    ν→nat {A} {B} {f} {g} α = ν→.is-natural f g α
```

The naturator $\nu$ is required to be compatible with the compositor and
unitor natural transformations of its source and target functors, which
boil down to commutativity of the nightmarish diagrams in [@basicbicats,
§1.2].

```agda
    field
      ν-compositor
        : ∀ {a b c} (f : b B.↦ c) (g : a B.↦ b)
        → ν→ (f B.⊗ g) C.∘ (G.γ→ (f , g) C.◀ σ a)
        ≡   (σ c C.▶ F.γ→ (f , g))
        C.∘ C.α→ (σ c , F.₁ f , F.₁ g)
        C.∘ (ν→ f C.◀ F.₁ g)
        C.∘ C.α← (G.₁ f , σ b , F.₁ g)
        C.∘ (G.₁ f C.▶ ν→ g)
        C.∘ C.α→ (G.₁ f , G.₁ g , σ a)

      ν-unitor
        : ∀ {a}
        → ν→ (B.id {a}) C.∘ (G.unitor C.◀ σ a)
        ≡ (σ a C.▶ F.unitor) C.∘ C.ρ→ (σ a) C.∘ C.λ← (σ a)
```

A lax transformation with invertible naturator is called a
**pseudonatural transformation**.

```agda
  record _=>ₚ_ : Type (o ⊔ ℓ ⊔ ℓ₁ ⊔ ℓ' ⊔ ℓ₁') where
    no-eta-equality
    field
      lax : _=>ₗ_

    open _=>ₗ_ lax public

    field
      naturator-inv : ∀ {a b} (f : a B.↦ b) → Cr.is-invertible (C.Hom _ _) (ν→ f)

    private
      open module ν← {a b} f =
        Cr.is-invertible (C.Hom _ _) (naturator-inv {a} {b} f)
        renaming (inv to ν←) using () public

    ν←nat :
      ∀ {A B} {f g : B B.↦ A} (α : f B.⇒ g)
      → ν← g C.∘ σ A C.▶ F.₂ α ≡ G.₂ α C.◀ σ B C.∘ ν← f
    ν←nat {A} {B} {f} {g} α = inverse-is-natural naturator ν←
      (λ f → ν←.inverses f .invl) (λ f → ν←.inverses f .invr) f g α
      where open Cr.Inverses
```

# Modifications {defines="modification"}

When dealing with 1-categorical data (categories, functors, and natural
transformations), the commutativity in 2-cells is witnessed by equations
in a set, which are trivial. When talking about _bicategorical_ data,
however, the naturality of a lax transformation is witnessed by a family
of non-trivial 2-cells. Therefore, it is fruitful to consider
transformations which affect _this_ data: a natural family of 2-cells.
This is called a **modification** between lax (or pseudo)
transformations. Since we are directly dealing with sets (the sets of
2-cells), modifications are the simplest bicategorical widget to define.

<!--
```agda
module
  _ {B : Prebicategory o ℓ ℓ'} {C : Prebicategory o₁ ℓ₁ ℓ₁'}
    {F : Lax-functor B C} {G : Lax-functor B C}
  where

  private
    module B = Prebicategory B
    module C = Prebicategory C
    module F = Lax-functor F
    module G = Lax-functor G

  module _ (σ σ' : F =>ₗ G) where
    private
      module σ = _=>ₗ_ σ
      module σ' = _=>ₗ_ σ'
```
-->

```agda
    record Modification : Type (o ⊔ ℓ ⊔ ℓ₁') where
      no-eta-equality
      field
        Γ : ∀ a → σ.σ a C.⇒ σ'.σ a

        is-natural
          : ∀ {a b} {f : a B.↦ b}
          → σ'.ν→ f C.∘ (G.₁ f C.▶ Γ a)
          ≡ (Γ b C.◀ F.₁ f) C.∘ σ.ν→ f
```

In a diagram, we display a modification as a 3-cell, i.e., a morphism
(modification) between morphisms (lax transformations) between morphisms
(lax functors) between objects (bicategories), and accordingly draw them
with super-heavy arrows, as in the diagram below.  Fortunately we will
not often stumble onto diagrams **of** bicategories, rather studying
diagrams **in** bicategories, which are (mercifully) limited to 2-cells.

~~~{.quiver}
\begin{tikzpicture}
\node (B) at (-1.25, 0) {$\mathbf{B}$};
\node (C) at (1.25, 0) {$\mathbf{C}$};

\draw[->] (B) .. controls(-0.5,1.25) and (0.5, 1.25) .. (C)
  node[midway, preaction={fill, diagrambg}, inner sep=0.3mm] (F) {$F$};

\draw[->] (B) .. controls(-0.5,-1.25) and (0.5, -1.25) .. (C)
  node[midway, preaction={fill, diagrambg}, inner sep=0.3mm] (G) {$G$};

\draw[2cell] (F) .. controls (-0.625, 0.25) and (-0.625, -0.25) .. (G)
  node[midway] (t1) {}
  node[midway, left, outer sep=-0.35mm] {\scriptsize{$\sigma$}}
  ;

\draw[2cell] (F) .. controls (0.625, 0.25) and (0.625, -0.25) .. (G)
  node[midway] (t2) {}
  node[midway, right, outer sep=-0.35mm] {\scriptsize{$\sigma'$}}
  ;

\draw[3cell] (t1) -- (t2) node[midway, above] {\footnotesize{$\Gamma$}};

\end{tikzpicture}
~~~

<!--
```agda
  unquoteDecl H-Level-Modification = declare-record-hlevel 2 H-Level-Modification (quote Modification)

  open Modification
  open _=>ₗ_

  Mod-pathp
    : {α α' β β' : F =>ₗ G}
    → (p : α ≡ α') (q : β ≡ β')
    → {a : Modification α β} {b : Modification α' β'}
    → (∀ x → PathP _ (a .Γ x) (b .Γ x))
    → PathP (λ i → Modification (p i) (q i)) a b
  Mod-pathp p q path i .Γ x                            = path x i
  Mod-pathp p q {a} {b} path i .is-natural {x} {y} {f} =
    is-prop→pathp
      (λ i → C.Hom.Hom-set _ _
        (ν→ (q i) f C.∘ G.₁ f C.▶ path x i) (path y i C.◀ F.₁ f C.∘ ν→ (p i) f))
      (a .is-natural)
      (b .is-natural) i

  _Γᵈ_
    : {α α' β β' : F =>ₗ G} {p : α ≡ α'} {q : β ≡ β'}
    → {a : Modification α β} {b : Modification α' β'}
    → PathP (λ i → Modification (p i) (q i)) a b
    → ∀ x → PathP _ (a .Γ x) (b .Γ x)
  p Γᵈ x = apd (λ i e → e .Γ x) p

  _Γₚ_ : {α β : F =>ₗ G} {a b : Modification α β} → a ≡ b → ∀ x → a .Γ x ≡ b .Γ x
  p Γₚ x = ap (λ e → e .Γ x) p

  infixl 45 _Γₚ_

  instance
    Extensional-modification
      : ∀ {ℓr} {α β : F =>ₗ G}
      → ⦃ sa : {x : B.Ob} → Extensional (α .σ x C.⇒ β .σ x) ℓr ⦄
      → Extensional (Modification α β) (o ⊔ ℓr)
    Extensional-modification ⦃ sa ⦄ .Pathᵉ f g = ∀ i → Pathᵉ sa (f .Γ i) (g .Γ i)
    Extensional-modification ⦃ sa ⦄ .reflᵉ x i = reflᵉ sa (x .Γ i)
    Extensional-modification ⦃ sa ⦄ .idsᵉ .to-path x = Mod-pathp refl refl λ i →
      sa .idsᵉ .to-path (x i)
    Extensional-modification ⦃ sa ⦄ .idsᵉ .to-path-over h =
      is-prop→pathp (λ i → Π-is-hlevel 1 λ _ → Pathᵉ-is-hlevel 1 sa (hlevel 2)) _ _
```
-->
