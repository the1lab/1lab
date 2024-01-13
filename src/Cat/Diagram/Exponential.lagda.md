<!--
```agda
open import Cat.Functor.Adjoint.Hom
open import Cat.Instances.Product
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Functor.Adjoint
open import Cat.Instances.Slice
open import Cat.Prelude

import Cat.Functor.Bifunctor as Bifunctor
import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Exponential
  {o ℓ} (C : Precategory o ℓ) (fp : has-products C) (term : Terminal C) where
```

# Exponential objects {defines="exponential-object"}

In a category $\cC$ with all finite [[products]] (including a [[terminal
object]]!), where by the usual internal logic dictionary we regard a
morphism $f : \Gamma \to A$ as an *$A$-term in context $\Gamma$*, the
notion of **exponential object** captures what it means for an object to
interpret *function types*. An exponential object for $A$ and $B$ is an
object $B^A$ equipped with an **evaluation map**

$$
\rm{ev} : B^A \times A \to B
$$

standing for the essence of function application: if I have a function
$f : A \to B$, and I have an $x : A$, then application gives me an $f(x)
: B$.

<!--
```agda
open Binary-products C fp hiding (unique₂)
open Cat.Reasoning C
open Terminal term
open Functor
open _⊣_

private variable
  A B : Ob
```
-->

Moreover, exponential objects must satisfy a universal property relative
to the product functor: if I have a derivation $m : \Gamma \times A \to
B$, of a $B$-term in a context extended by $A$, then I should be able to
form the "abstraction" $\lambda m : \Gamma \to B^A$.

```agda
record is-exponential (B^A : Ob) (ev : Hom (B^A ⊗₀ A) B) : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    ƛ        : ∀ {Γ} (m : Hom (Γ ⊗₀ A) B) → Hom Γ B^A
    commutes : ∀ {Γ} (m : Hom (Γ ⊗₀ A) B) → ev ∘ ƛ m ⊗₁ id ≡ m
    unique   : ∀ {Γ} {m : Hom (Γ ⊗₀ _) _} m'
             → ev ∘ m' ⊗₁ id ≡ m
             → m' ≡ ƛ m
```

The data above is an unpacked way of saying that the evaluation map
extends to an equivalence between $\hom(\Gamma, B^A)$ and $\hom(\Gamma
\times A, B)$: since being an equivalence is a proposition, once we have
fixed the evaluation map, having abstractions is a property, not extra
structure.

```agda
  unlambda : ∀ {C} (m : Hom C B^A) → Hom (C ⊗₀ A) B
  unlambda m = ev ∘ m ⊗₁ id

  lambda-is-equiv : ∀ {C} → is-equiv (ƛ {C})
  lambda-is-equiv = is-iso→is-equiv λ where
    .is-iso.inv    → unlambda
    .is-iso.rinv x → sym (unique x refl)
    .is-iso.linv x → commutes x
```

<!--
```
  unique₂ : ∀ {C} {m : Hom (C ⊗₀ _) _} m₁ m₂
          → ev ∘ m₁ ⊗₁ id ≡ m
          → ev ∘ m₂ ⊗₁ id ≡ m
          → m₁ ≡ m₂
  unique₂ _ _ p q = unique _ p ∙ sym (unique _ q)

  lambda-ev : ƛ ev ≡ id
  lambda-ev = sym (unique id (sym (intror (×-functor .F-id))))
```
-->

As an aside, let us remark that the evaluation map $B^A \times A \to B$
is sufficient to interpret the more familiar formation rule for function
application,

$$
\frac{\Gamma \vdash f : B^A\quad \Gamma \vdash x : A}
     {\Gamma \vdash f(x) : B}
$$

by relativising to an arbitrary context $\Gamma$ through composition,
and that this indeed interprets the $\beta$-reduction rule:

```agda
  private
    app : ∀ {Γ} (f : Hom Γ B^A) (x : Hom Γ A) → Hom Γ B
    app f x = ev ∘ f ⊗₁ id ∘ ⟨ id , x ⟩

    beta : ∀ {Γ} (f : Hom (Γ ⊗₀ A) B) (x : Hom Γ A)
         → app (ƛ f) x ≡ f ∘ ⟨ id , x ⟩
    beta f x = pulll (commutes _)
```

<!--
```agda
module _ where
  open is-exponential

  is-exponential-is-prop : ∀ {B^A} {ev : Hom (B^A ⊗₀ A) B} → is-prop (is-exponential B^A ev)
  is-exponential-is-prop {B^A = B^A} {ev} x y = q where
    p : Path (∀ {C} m → Hom C B^A) (x .ƛ) (y .ƛ)
    p i {C} m = y .unique (x .ƛ m) (x .commutes m) i

    q : x ≡ y
    q i .ƛ = p i
    q i .commutes m =
      is-prop→pathp (λ i → Hom-set _ _ (ev ∘ p i m ⊗₁ id) m) (x .commutes m) (y .commutes m) i
    q i .unique {m = m} m' q =
      is-prop→pathp (λ i → Hom-set _ _ m' (p i m)) (x .unique m' q) (y .unique m' q) i
```
-->

Putting this data together, we can define an exponential object to be a
pair $(B^A, \rm{ev})$, with a witness that $\rm{ev}$ supports
abstraction.

```agda
  record Exponential (A B : Ob) : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      B^A        : Ob
      ev         : Hom (B^A ⊗₀ A) B
      has-is-exp : is-exponential B^A ev
    open is-exponential has-is-exp public
```

:::{.definition #cartesian-closed}
Since a finite-products category is called [Cartesian monoidal], a
finite-products category where every pair of objects has an exponential
is called **Cartesian closed**, and we abbreviate the phrase "Cartesian
closed category" to "CCC".

[Cartesian monoidal]: Cat.Monoidal.Instances.Cartesian.html

```agda
  record Cartesian-closed : Type (o ⊔ ℓ) where
    no-eta-equality

    field has-exp : ∀ A B → Exponential A B

    module _ {A} {B} where open Exponential (has-exp A B) hiding (B^A) public
    module Exp A B = Exponential (has-exp A B)
```
:::

<!--
```agda
  exponential-unique
    : ∀ {A B B^A B^A'} {ev : Hom (B^A ⊗₀ A) B} {ev' : Hom (B^A' ⊗₀ A) B}
    → is-exponential B^A ev
    → is-exponential B^A' ev'
    → B^A ≅ B^A'
  exponential-unique {ev = ev} {ev'} exp1 exp2 =
    make-iso (exp2 .ƛ ev) (exp1 .ƛ ev')
      (unique₂ exp2 (exp2 .ƛ ev ∘ exp1 .ƛ ev') id
        (  ap (ev' ∘_) (ap₂ _⊗₁_ refl (sym (idl id)) ∙ ×-functor .F-∘ _ _)
        ·· pulll (exp2 .commutes _)
        ·· exp1 .commutes _)
        (elimr (×-functor .F-id)))
      (unique₂ exp1 (exp1 .ƛ ev' ∘ exp2 .ƛ ev) id
        (  ap (ev ∘_) (ap₂ _⊗₁_ refl (sym (idl id)) ∙ ×-functor .F-∘ _ _)
        ·· pulll (exp1 .commutes _)
        ·· exp2 .commutes _)
        (elimr (×-functor .F-id)))

  ƛ-∘
    : ∀ {A B C X A^X B^X} {evA : Hom (A^X ⊗₀ X) A} {evB : Hom (B^X ⊗₀ X) B}
    → {f : Hom A B} {g : Hom C A^X}
    → (exp : is-exponential B^X evB)
    → exp .is-exponential.ƛ (f ∘ evA) ∘ g ≡ exp .is-exponential.ƛ (f ∘ evA ∘ g ⊗₁ id)
  ƛ-∘ exb = is-exponential.unique exb _
    ( ap₂ _∘_ refl (ap₂ _⊗₁_ refl (sym (idl id)) ∙ ×-functor .F-∘ _ _)
    ∙ extendl (is-exponential.commutes exb _))
```
-->

The connection between Cartesian closed categories and the lambda
calculus is fundamental: however, it would take us too far afield of the
basic properties of CCCs to discuss that _in this module_. You can find
extended discussion, and an implementation, in the page on [[simply
typed lambda calculus]].

## Functoriality

In a Cartesian closed category, we can think of the
exponential-assigning operation $(A,B) \mapsto B^A$ as an internalised
analogue of the $\hom$-functor. In the same way that a pair of morphisms
$B \to B'$ and $A \to A'$ would act on the ordinary $\hom$ sets by
composition, they act on _internal_ homs, too, defining a mapping $B^A
\to B'^{A'}$.

<!--
```agda
module _ (cc : Cartesian-closed) where
  open Cartesian-closed cc
```
-->

```agda
  [-,-]₁ : ∀ {a a' b b'} → Hom b b' → Hom a' a → Hom (Exp.B^A a b) (Exp.B^A a' b')
  [-,-]₁ f g = ƛ (f ∘ ev ∘ ⟨ π₁ , g ∘ π₂ ⟩)

  [-,-] : Functor (C ^op ×ᶜ C) C
  [-,-] .F₀ (A , B) = Exp.B^A A B
  [-,-] .F₁ (f , g) = [-,-]₁ g f
```

Through some calculations that are just annoying enough to stun the
unsuspecting reader, we can show that this is indeed a functor $\cC\op
\times \cC \to \cC$. With a bit more effort, we can show that our
defining equivalence between the $\hom$-sets $\Gamma \times A \to B$ and
$\Gamma \to B^A$ satisfies the naturality condition required to to
characterise $-^A$ as the [[right adjoint]] to $- \times A$.

```agda
  [-,-] .F-id =
    ƛ (id ∘ ev ∘ ⟨ π₁ , id ∘ π₂ ⟩) ≡⟨ ap ƛ (idl _ ∙ ap (ev ∘_) (sym (ap₂ ⟨_,_⟩ (idl _) refl))) ⟩
    ƛ (ev ∘ id ⊗₁ id)              ≡˘⟨ unique id refl ⟩
    id                             ∎
  [-,-] .F-∘ (f , g) (f' , g') = sym $ unique _ $
    ev ∘ ⟨ (ƛ (g ∘ ev ∘ ⟨ π₁ , f ∘ π₂ ⟩) ∘ ƛ (g' ∘ ev ∘ ⟨ π₁ , f' ∘ π₂ ⟩)) ∘ π₁ , id ∘ π₂ ⟩ ≡⟨ refl⟩∘⟨ ap₂ _⊗₁_ refl (introl refl) ∙ ×-functor .F-∘ _ _ ⟩
    ev ∘ ƛ (g ∘ ev ∘ ⟨ π₁ , f ∘ π₂ ⟩) ⊗₁ id ∘ ƛ (g' ∘ ev ∘ ⟨ π₁ , f' ∘ π₂ ⟩) ⊗₁ id          ≡⟨ pulll (commutes _) ⟩
    (g ∘ ev ∘ ⟨ π₁ , f ∘ π₂ ⟩) ∘ ƛ (g' ∘ ev ∘ ⟨ π₁ , f' ∘ π₂ ⟩) ⊗₁ id                       ≡⟨ pullr (pullr (ap₂ _∘_ (ap₂ ⟨_,_⟩ (introl refl) refl) refl ∙ sym (Bifunctor.first∘second ×-functor))) ⟩
    g ∘ ev ∘ ƛ (g' ∘ ev ∘ ⟨ π₁ , f' ∘ π₂ ⟩) ⊗₁ id ∘ id ⊗₁ f                                 ≡⟨ refl⟩∘⟨ pulll (commutes _) ⟩
    g ∘ (g' ∘ ev ∘ ⟨ π₁ , f' ∘ π₂ ⟩) ∘ id ⊗₁ f                                              ≡⟨ pulll refl ∙ extendr (pullr (pullr (Product.unique (fp _ _) _ (pulll π₁∘⟨⟩ ·· π₁∘⟨⟩ ·· idl _) (pulll π₂∘⟨⟩ ∙ extendr π₂∘⟨⟩)))) ⟩
    (g ∘ g') ∘ ev ∘ ⟨ π₁ , (f' ∘ f) ∘ π₂ ⟩                                                  ∎

  product⊣exponential : ∀ {A} → Bifunctor.Left ×-functor A ⊣ Bifunctor.Right [-,-] A
  product⊣exponential {A} = hom-iso→adjoints ƛ lambda-is-equiv nat where
    module _ {a b c d} (g : Hom a b) (h : Hom c d) (x : Hom (d ⊗₀ A) a) where
      nat : ƛ (g ∘ x ∘ ⟨ h ∘ π₁ , id ∘ π₂ ⟩) ≡ ƛ (g ∘ ev ∘ ⟨ π₁ , id ∘ π₂ ⟩) ∘ ƛ x ∘ h
      nat = sym $ unique _ $
        ev ∘ (ƛ (g ∘ ev ∘ ⟨ π₁ , id ∘ π₂ ⟩) ∘ ƛ x ∘ h) ⊗₁ id        ≡⟨ refl⟩∘⟨ ap₂ _⊗₁_ refl (introl refl) ∙ ×-functor .F-∘ _ _ ⟩
        ev ∘ ƛ (g ∘ ev ∘ ⟨ π₁ , id ∘ π₂ ⟩) ⊗₁ id ∘ (ƛ x ∘ h) ⊗₁ id  ≡⟨ pulll (commutes _) ⟩
        (g ∘ ⌜ ev ∘ ⟨ π₁ , id ∘ π₂ ⟩ ⌝) ∘ (ƛ x ∘ h) ⊗₁ id           ≡⟨ ap! (elimr (ap₂ ⟨_,_⟩ (introl refl) refl ∙ ×-functor .F-id)) ⟩
        (g ∘ ev) ∘ (ƛ x ∘ h) ⊗₁ id                                  ≡⟨ pullr (ap₂ _∘_ refl (Bifunctor.first∘first ×-functor)) ⟩
        g ∘ ev ∘ ƛ x ⊗₁ id ∘ h ⊗₁ id                                ≡⟨ refl⟩∘⟨ pulll (commutes _) ⟩
        g ∘ x ∘ h ⊗₁ id                                             ∎
```

## From an adjunction

As a converse to the results above, if each product functor $- \times A$
has a right adjoint $-^A$, then $\cC$ is a Cartesian closed category,
with the object $B^A$ serving as the exponential. This means that we can
prove that a category is Cartesian closed by appealing to general facts
about the existence of right adjoints, if any apply.

```agda
product-adjoint→cartesian-closed
  : (-^_ : Ob → Functor C C)
  → (∀ A → Bifunctor.Left ×-functor A ⊣ -^ A)
  → Cartesian-closed
product-adjoint→cartesian-closed A→ adj = cc where
  open Exponential
  open is-exponential

  exp : ∀ A B → Exponential A B
  exp A B .B^A = A→ A .F₀ B
  exp A B .ev = adj A .counit.ε B
  exp A B .has-is-exp .ƛ          = L-adjunct (adj A)
  exp A B .has-is-exp .commutes m = R-L-adjunct (adj A) m
  exp A B .has-is-exp .unique m' x = sym $
    Equiv.injective₂ (_ , R-adjunct-is-equiv (adj A))
      (R-L-adjunct (adj A) _) x

  cc : Cartesian-closed
  cc .Cartesian-closed.has-exp = exp
```

## Exponentiable objects {defines=exponentiable-object}

<!--
```agda
open /-Obj
open /-Hom
open Pullback

module _ B (exp : ∀ A → Exponential B A) where
  private module _ A where open Exponential (exp A) renaming (B^A to -^B₀) hiding (ƛ ; unlambda ; ev) public
  private module _ {A} where open Exponential (exp A) renaming (unlambda to app) using (ev ; ƛ) public
```
-->

We refer to an object $B : \cC$ as exponentia*ble* if, for every other
$A : \cC$, the exponential object $A^B$ exists. This means that we have
a right adjoint $-^B$ to the functor $- \times B$, by the discussion
above. It will, however, be more useful to us to characterise
exponentiability of $B$ by a condition on the slice category $C/B$.

```agda
  -^B : Functor C C
  -^B .F₀ = -^B₀
  -^B .F₁ h = ƛ (h ∘ ev)
  -^B .F-id = ap ƛ (idl ev) ∙ lambda-ev _
  -^B .F-∘ f g = sym $ Exponential.unique (exp _) _
    (  ap₂ _∘_ refl (ap₂ _⊗₁_ refl (introl refl) ∙ ×-functor .F-∘ _ _)
    ·· pulll (Exponential.commutes (exp _) _)
    ·· extendr (Exponential.commutes (exp _) _))
```

Recall the [[constant families]] functor $\Delta_B : \cC \to \cC/B$,
which sends an object $X$ to the product projection $\pi_2 : X \times B
\to B$. Following [@Elephant, A1.5.2], we have the following
characterisation of exponentiability: In a category with pullbacks, an
object $B$ is exponentiable iff. we have a right adjoint functor
$\Delta_B \dashv \Pi_B$.

Suppose $B$ is exponentiable. The value $\Pi_B(f)$ on a family $f : A
\to B$ is defined to be the pullback

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  {\Pi_B(f)} \&\& {A^B} \\
  \\
  1 \&\& {B^B\text{,}}
  \arrow[from=1-1, to=3-1]
  \arrow["{\lambda(\pi_2)}"', from=3-1, to=3-3]
  \arrow["{f^B}", from=1-3, to=3-3]
  \arrow[from=1-1, to=1-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

where the map $f^B : A^B \to B^B$, on the right, is the action of
$(-)^B$ on $f$. An application of the universal properties at hand shows
that we can extend maps $h : X \to Y$ over $B$ to maps $\Pi_B(X) \to
\Pi_B(Y)$. The calculation that this is functorial is routine, so we
omit it from the page.

```agda
  exponentiable→product
    : has-pullbacks C
    → Functor (Slice C B) C
  exponentiable→product pb = f where
    f : Functor (Slice C B) C
    f .F₀ h = pb {B = top} (-^B .F₁ (h .map)) (ƛ π₂) .apex
    f .F₁ {x} {y} h = pb _ _ .universal (sym p) where abstract
      p : ƛ π₂ ∘ !  ≡ -^B .F₁ (y .map) ∘ -^B .F₁ (h .map) ∘ pb {B = top} (-^B .F₁ (x .map)) (ƛ π₂) .p₁
      p = ƛ π₂ ∘ !                                         ≡⟨ ap (ƛ π₂ ∘_) (!-unique _) ⟩
          ƛ π₂ ∘ pb _ _ .p₂                                ≡˘⟨ pb _ _ .square ⟩
          ƛ (x .map ∘ ev) ∘ pb _ _ .p₁                     ≡˘⟨ ap (-^B .F₁) (h .commutes) ⟩∘⟨refl ⟩
          ƛ ((y .map ∘ h .map) ∘ ev) ∘ pb _ _ .p₁          ≡⟨ pushl (-^B .F-∘ _ _) ⟩
          ƛ (y .map ∘ ev) ∘ ƛ (h .map ∘ ev) ∘ pb _ _ .p₁   ∎
```

<!--
```agda
    f .F-id = sym $ pb _ _ .Pullback.unique
      (sym (eliml (-^B .F-id) ∙ intror refl)) (sym (!-unique _))

    f .F-∘ f g = sym $ pb _ _ .Pullback.unique
      (pulll (pb _ _ .p₁∘universal) ·· pullr (pb _ _ .p₁∘universal) ·· pulll (sym (-^B .F-∘ _ _)))
      (sym (!-unique _))

  exponentiable→constant-family⊣product
    : (pb : has-pullbacks C)
    → constant-family fp ⊣ exponentiable→product pb
  exponentiable→constant-family⊣product pb =
    hom-iso-inv→adjoints (rem₁ _ .fst) (rem₁ _ .snd) nat where
    module b = Functor (constant-family fp)
    module Π = Functor (exponentiable→product pb)
```
-->

It remains to prove that this functor is actually a right adjoint to the
constant-families functor $\Delta_B : \cC \to \cC/B$ like we had
claimed. We start with an elementary observation: given maps $f : A \to
B$ and $q : X \to A^B$, asking for

$$
\lambda (f \circ \rm{ev}) \circ q = \lambda(\pi_2) \circ \operatorname{!}
$$

is equivalent to asking for

$$
f \circ \lambda^{-1}(q) = \pi_2\text{,}
$$

which is in turn equivalent to asking that $q$ be a map $\Delta_B(X) \to
f$, over $B$.

```agda
    coh₁ : ∀ {X} (f : /-Obj B) (q : Hom X (-^B₀ (f .domain)))
         → (ƛ (f .map ∘ ev) ∘ q ≡ ƛ π₂ ∘ !)
         ≃ (f .map ∘ app q ≡ π₂)
    coh₁ f h = prop-ext!
      (λ p → Equiv.injective (_ , lambda-is-equiv _) (sym (ƛ-∘ (has-is-exp _)) ·· p ·· done))
      (λ p → ƛ-∘ (has-is-exp _) ·· ap ƛ p ·· sym done)
```

<!--
```
      where
        done : ƛ π₂ ∘ ! ≡ ƛ π₂
        done = Exponential.unique (exp _) _ $
             ap₂ _∘_ refl (ap₂ _⊗₁_ refl (sym (idl id)) ∙ ×-functor .F-∘ _ _)
          ·· pulll (Exponential.commutes (exp _) _)
          ·· (π₂∘⟨⟩ ∙ idl _)

    opaque
      rem₁ : ∀ {X} (f : /-Obj B)
           → Hom X (Π.₀ f) ≃ Slice C B .Precategory.Hom (b.₀ X) f
      rem₁ {X = X} f =
```
-->

This is the last piece that we need to establish an equivalence between
the $\hom$-sets $\hom_\cC(X, \Pi_B(f))$ and $\hom_{\cC/B}(\Delta_B(X),
f)$, and even though it factors through the rather complicated path
displayed below, it definitionally sends $h : \hom_\cC(X, \Pi_B(f))$ to

$$
\lambda^{-1}(p_1\circ h)\text{.}
$$

Having this very simple computational description will greatly simplify
the proof that this meandering equivalence is actually natural --- and
that naturality is all that stands between us and the adjunction
$\Delta_B \dashv \Pi_B$ we've been chasing.

```agda
        Hom X (Π.₀ f)
          ≃⟨ Pullback.pullback-univ (pb _ _) ⟩
        Σ (Hom X (-^B .F₀ (f .domain))) (λ h → Σ (Hom X top) λ h' → ƛ (f .map ∘ ev) ∘ h ≡ ƛ π₂ ∘ h')
          ≃⟨ Σ-ap-snd (λ x → Σ-contr-eqv (has⊤ X)) ⟩
        Σ (Hom X (-^B .F₀ (f .domain))) (λ h → ƛ (f .map ∘ ev) ∘ h ≡ ƛ π₂ ∘ !)
          ≃⟨ Σ-ap (Equiv.inverse (ƛ , lambda-is-equiv _)) (coh₁ f) ⟩
        Σ (Hom (X ⊗₀ B) (f .domain)) (λ h → f .map ∘ h ≡ π₂)
          ≃⟨ Iso→Equiv ((λ x → record { commutes = x .snd }) , iso (λ x → _ , x .commutes) (λ _ → trivial!) (λ _ → trivial!)) ⟩
        Slice C B .Precategory.Hom (b.₀ X) f
          ≃∎

      rem₁-β : ∀ {X} (f : /-Obj B) (h : Hom X (Π.₀ f))
             → Equiv.to (rem₁ f) h .map ≡ app (pb _ _ .p₁ ∘ h)
      rem₁-β f h = refl

    nat : hom-iso-inv-natural {L = constant-family fp} {R = exponentiable→product pb} (rem₁ _ .fst)
    nat g h x = ext $
     rem₁ _ .fst (Π.₁ g ∘ x ∘ h) .map                           ≡⟨ rem₁-β _ _ ⟩
     app (pb _ _ .p₁ ∘ Π.₁ g ∘ x ∘ h)                           ≡⟨ ap app (pulll (pb _ _ .p₁∘universal ∙ ƛ-∘ {f = g .map} {g = pb _ _ .p₁} (has-is-exp _))) ⟩
     app (ƛ (g .map ∘ ev ∘ pb _ _ .p₁ ⊗₁ id) ∘ x ∘ h)           ≡⟨ ap₂ _∘_ refl (ap₂ _⊗₁_ refl (sym (idl id)) ∙ ×-functor .F-∘ _ _) ∙ pulll refl ⟩
     app (ƛ (g .map ∘ ev ∘ pb _ _ .p₁ ⊗₁ id)) ∘ (x ∘ h) ⊗₁ id   ≡⟨ ap₂ _∘_ (Equiv.η (_ , lambda-is-equiv _) _) refl ⟩
     (g .map ∘ ev ∘ pb _ _ .p₁ ⊗₁ id) ∘ (x ∘ h) ⊗₁ id           ≡⟨ pullr (pullr (sym (×-functor .F-∘ _ _) ∙ ap₂ _⊗₁_ (assoc _ _ _) refl ∙ ×-functor .F-∘ _ _)) ⟩
     g .map ∘ ev ∘ (pb _ _ .p₁ ∘ x) ⊗₁ id ∘ h ⊗₁ id             ≡⟨ refl⟩∘⟨ (pulll refl ∙ ap₂ _∘_ refl (ap₂ ⟨_,_⟩ refl (idl _))) ⟩
     g .map ∘ (ev ∘ (pb _ _ .p₁ ∘ x) ⊗₁ id) ∘ b.₁ h .map        ≡⟨ ap₂ _∘_ refl (ap₂ _∘_ (sym (rem₁-β _ _)) refl) ⟩
     g .map ∘ rem₁ _ .fst x .map ∘ b.₁ h .map                   ∎
```
