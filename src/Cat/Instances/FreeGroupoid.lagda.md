<!--
```agda
open import 1Lab.Reflection.Induction

open import Cat.Instances.Discrete
open import Cat.Functor.Base
open import Cat.Groupoid
open import Cat.Morphism using (is-invertible; Inverses; make-invertible)
open import Cat.Prelude

import Cat.Reasoning

open is-invertible
open Inverses
open Functor
```
-->

```agda
module Cat.Instances.FreeGroupoid where
```

# The free groupoid on a category {defines="free-groupoid zigzag"}

Recall the construction of the [[free category]] on a graph; by a similar
construction, we can define the **free groupoid** on a graph, having as objects
the vertices of the graph and as morphisms *finite zigzags* of edges of the graph.

~~~{.quiver .short-05}
\[\begin{tikzcd}
  a && c && e \\
  & b && d
  \arrow[from=1-1, to=2-2]
  \arrow[from=1-3, to=2-2]
  \arrow[from=1-3, to=2-4]
  \arrow[from=1-5, to=2-4]
\end{tikzcd}\]
~~~

Alternatively, we can define the free groupoid on a *precategory* $\cC$, which has
as objects the objects of $\cC$ and as morphisms zigzags of morphisms in $\cC$,
subject to relations induced by the identities and composition of $\cC$. This
can be seen as formally adding inverses to every morphism of $\cC$:
the *localisation* of $\cC$ at the class of all morphisms.

Moreover, we should expect this construction to be the left end of a (bi)adjoint
*triple* around the inclusion of groupoids into categories, the right adjoint
being given by the [[core]] of a category.

We define the type of zigzags in $\cC$ as a higher inductive type of *lists* of
morphisms (or reverse morphisms), with the desired relations built in and a
constructor forcing it to be a set.

```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  open Precategory C

  data Zigzag : Ob → Ob → Type (o ⊔ ℓ) where
    nil    : ∀ {a} → Zigzag a a
    cons   : ∀ {a b c} → Hom a b → Zigzag b c → Zigzag a c
    cons⁻¹ : ∀ {a b c} → Hom b a → Zigzag b c → Zigzag a c

    cons-id : ∀ {a b} {fs : Zigzag a b} → cons id fs ≡ fs
    cons-∘
      : ∀ {a b c d} {f : Hom a b} {g : Hom b c} {hs : Zigzag c d}
      → cons (g ∘ f) hs ≡ cons f (cons g hs)
    cons-cons⁻¹
      : ∀ {a b c} {f : Hom a b} {gs : Zigzag a c}
      → cons f (cons⁻¹ f gs) ≡ gs
    cons⁻¹-cons
      : ∀ {a b c} {f : Hom a b} {gs : Zigzag b c}
      → cons⁻¹ f (cons f gs) ≡ gs

    squash : ∀ {a b} → is-set (Zigzag a b)
```

<!--
```agda
unquoteDecl Zigzag-elim = make-elim-n 2 Zigzag-elim (quote Zigzag)
unquoteDecl Zigzag-elim-prop = make-elim-n 1 Zigzag-elim-prop (quote Zigzag)

instance
  H-Level-Zigzag
    : ∀ {o ℓ} {C : Precategory o ℓ} {a b k}
    → H-Level (Zigzag C a b) (2 + k)
  H-Level-Zigzag = basic-instance 2 squash
```
-->

In order to make a category out of this, we define concatenation of zigzags and
prove that it is associative and unital.

```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Precategory C

  _++_ : ∀ {a b c} → Zigzag C a b → Zigzag C b c → Zigzag C a c
  nil ++ gs = gs
  cons f fs ++ gs = cons f (fs ++ gs)
  cons⁻¹ f fs ++ gs = cons⁻¹ f (fs ++ gs)
  cons-id {fs = fs} i ++ gs = cons-id {fs = fs ++ gs} i
  cons-∘ {f = f} {g} {fs} i ++ gs = cons-∘ {f = f} {g} {fs ++ gs} i
  cons-cons⁻¹ {f = f} {fs} i ++ gs = cons-cons⁻¹ {f = f} {fs ++ gs} i
  cons⁻¹-cons {f = f} {fs} i ++ gs = cons⁻¹-cons {f = f} {fs ++ gs} i
  squash fs gs p q i j ++ hs =
    squash (fs ++ hs) (gs ++ hs) (λ j → p j ++ hs) (λ j → q j ++ hs) i j

  ++-nil : ∀ {a b} (fs : Zigzag C a b) → fs ++ nil ≡ fs
  ++-nil = Zigzag-elim-prop {P = λ fs → fs ++ nil ≡ fs} (λ _ → hlevel 1)
    refl
    (λ f _ rec → ap (cons f) rec)
    (λ f _ rec → ap (cons⁻¹ f) rec)

  ++-assoc
    : ∀ {a b c d} (fs : Zigzag C a b) (gs : Zigzag C b c) (hs : Zigzag C c d)
    → (fs ++ gs) ++ hs ≡ fs ++ (gs ++ hs)
  ++-assoc = Zigzag-elim-prop
    {P = λ fs → ∀ gs hs → (fs ++ gs) ++ hs ≡ fs ++ (gs ++ hs)}
    (λ _ → hlevel 1)
    (λ _ _ → refl)
    (λ f _ rec gs hs → ap (cons f) (rec gs hs))
    (λ f _ rec gs hs → ap (cons⁻¹ f) (rec gs hs))

module _ {o ℓ} (C : Precategory o ℓ) where
  open Precategory

  FreeGroupoid : Precategory o (o ⊔ ℓ)
  FreeGroupoid .Ob = Ob C
  FreeGroupoid .Hom = Zigzag C
  FreeGroupoid .Hom-set _ _ = squash
  FreeGroupoid .id = nil
  FreeGroupoid ._∘_ f g = g ++ f
  FreeGroupoid .idr _ = refl
  FreeGroupoid .idl = ++-nil
  FreeGroupoid .assoc f g h = ++-assoc h g f
```

There is a canonical inclusion of $\cC$ into its free groupoid:

```agda
  FreeGroupoid-unit : Functor C FreeGroupoid
  FreeGroupoid-unit .F₀ a = a
  FreeGroupoid-unit .F₁ f = cons f nil
  FreeGroupoid-unit .F-id = cons-id
  FreeGroupoid-unit .F-∘ _ _ = cons-∘
```

We now prove that `FreeGroupoid`{.Agda} is indeed a [[pregroupoid]].
To do this, we need a way to reverse a zigzag of morphisms while turning
"forwards" morphisms into "backwards" morphisms and vice versa.

Following standard functional programming practice, we first define a "reverse
append" operation that appends the reverse of its first argument to its second
argument, and then define `reverse`{.Agda} using the empty zigzag.

```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C

  cons⁻¹-id : ∀ {a b} (fs : Zigzag C a b) → cons⁻¹ id fs ≡ fs
  cons⁻¹-id fs =
    cons⁻¹ id ⌜ fs ⌝       ≡˘⟨ ap¡ cons-id ⟩
    cons⁻¹ id (cons id fs) ≡⟨ cons⁻¹-cons ⟩
    fs                     ∎

  cons⁻¹-∘
    : ∀ {a b c d} {f : Hom b a} {g : Hom c b} (hs : Zigzag C c d)
    → cons⁻¹ (f ∘ g) hs ≡ cons⁻¹ f (cons⁻¹ g hs)
  cons⁻¹-∘ {f = f} {g} hs =
    cons⁻¹ (f ∘ g) ⌜ hs ⌝                                       ≡˘⟨ ap¡ (ap (cons g) cons-cons⁻¹ ∙ cons-cons⁻¹) ⟩
    cons⁻¹ (f ∘ g) ⌜ cons g (cons f (cons⁻¹ f (cons⁻¹ g hs))) ⌝ ≡˘⟨ ap¡ cons-∘ ⟩
    cons⁻¹ (f ∘ g) (cons (f ∘ g) (cons⁻¹ f (cons⁻¹ g hs)))      ≡⟨ cons⁻¹-cons ⟩
    cons⁻¹ f (cons⁻¹ g hs)                                      ∎

  _r++_ : ∀ {a b c} → Zigzag C b a → Zigzag C b c → Zigzag C a c
  nil r++ gs = gs
  cons f fs r++ gs = fs r++ cons⁻¹ f gs
  cons⁻¹ f fs r++ gs = fs r++ cons f gs
  cons-id {fs = fs} i r++ gs = fs r++ cons⁻¹-id gs i
  cons-∘ {f = f} {g} {fs} i r++ gs = fs r++ cons⁻¹-∘ {f = g} {f} gs i
  cons-cons⁻¹ {f = f} {fs} i r++ gs = fs r++ cons-cons⁻¹ {f = f} {gs} i
  cons⁻¹-cons {f = f} {fs} i r++ gs = fs r++ cons⁻¹-cons {f = f} {gs} i
  squash fs gs p q i j r++ hs =
    squash (fs r++ hs) (gs r++ hs) (λ j → p j r++ hs) (λ j → q j r++ hs) i j

  reverse : ∀ {a b} → Zigzag C a b → Zigzag C b a
  reverse fs = fs r++ nil
```

We need a few more lemmas to show that reversing a zigzag gives a left and
right inverse.

```agda
  r++-assoc
    : ∀ {a b c d} (fs : Zigzag C b a) (gs : Zigzag C b c) (hs : Zigzag C c d)
    → (fs r++ gs) ++ hs ≡ fs r++ (gs ++ hs)
  r++-assoc = Zigzag-elim-prop
    {P = λ fs → ∀ gs hs → (fs r++ gs) ++ hs ≡ fs r++ (gs ++ hs)}
    (λ _ → hlevel 1)
    (λ _ _ → refl)
    (λ f fs rec gs hs → rec _ _)
    (λ f fs rec gs hs → rec _ _)

  r++-assoc'
    : ∀ {a b c d} (fs : Zigzag C b c) (gs : Zigzag C b a) (hs : Zigzag C c d)
    → (fs r++ gs) r++ hs ≡ gs r++ (fs ++ hs)
  r++-assoc' = Zigzag-elim-prop
    {P = λ f → ∀ g h → (f r++ g) r++ h ≡ g r++ (f ++ h)}
    (λ _ → hlevel 1)
    (λ _ _ → refl)
    (λ f fs rec gs hs → rec _ _)
    (λ f fs rec gs hs → rec _ _)

  r++-reverse
    : ∀ {a b c} (fs : Zigzag C b a) (gs : Zigzag C b c)
    → reverse fs ++ gs ≡ fs r++ gs
  r++-reverse fs gs = r++-assoc fs nil gs

  r++-cancel : ∀ {a b} (fs : Zigzag C a b) → fs r++ fs ≡ nil
  r++-cancel = Zigzag-elim-prop
    {P = λ fs → fs r++ fs ≡ nil}
    (λ _ → hlevel 1)
    refl
    (λ f fs rec → ap (fs r++_) cons⁻¹-cons ∙ rec)
    (λ f fs rec → ap (fs r++_) cons-cons⁻¹ ∙ rec)

  reverse-invo : ∀ {a b} (fs : Zigzag C a b) → reverse (reverse fs) ≡ fs
  reverse-invo fs = r++-assoc' fs nil nil ∙ ++-nil fs

  reverse-invl : ∀ {a b} (fs : Zigzag C a b) → reverse fs ++ fs ≡ nil
  reverse-invl fs = r++-reverse fs fs ∙ r++-cancel fs

  reverse-invr : ∀ {a b} (fs : Zigzag C a b) → fs ++ reverse fs ≡ nil
  reverse-invr fs = ap (_++ reverse fs) (sym (reverse-invo fs))
                  ∙ reverse-invl (reverse fs)

  FreeGroupoid-is-groupoid : is-pregroupoid (FreeGroupoid C)
  FreeGroupoid-is-groupoid f .inv = reverse f
  FreeGroupoid-is-groupoid f .inverses .invl = reverse-invl f
  FreeGroupoid-is-groupoid f .inverses .invr = reverse-invr f
```

The free groupoid is characterised by the following universal property:
given any pregroupoid $\cD$, any functor $\cC \to \cD$ factors through the
free groupoid on $\cC$. In this sense, it is the *minimal* groupoid containing
$\cC$.

```agda
  module
    _ {od ℓd} {D : Precategory od ℓd} (D-grpd : is-pregroupoid D)
      (F : Functor C D)
    where
    private
      module D = Cat.Reasoning D

    FreeGroupoid-universal : Functor (FreeGroupoid C) D
    FreeGroupoid-universal .F₀ = F .F₀
    FreeGroupoid-universal .F₁ = Zigzag-elim
      {P = λ {a} {b} _ → D.Hom (F .F₀ a) (F .F₀ b)}
      (λ {a} {b} _ → D.Hom-set (F .F₀ a) (F .F₀ b))
      D.id
      (λ f _ rec → rec D.∘ F .F₁ f)
      (λ f _ rec → rec D.∘ D-grpd (F .F₁ f) .inv)
      (λ _ → D.elimr (F .F-id))
      (λ _ → D.pushr (F .F-∘ _ _))
      (λ _ → D.cancelr (D-grpd (F .F₁ _) .invr))
      (λ _ → D.cancelr (D-grpd (F .F₁ _) .invl))
    FreeGroupoid-universal .F-id = refl
    FreeGroupoid-universal .F-∘ fs gs = Zigzag-elim-prop
      {P = λ gs → ∀ fs
         → FreeGroupoid-universal .F₁ (gs ++ fs)
         ≡ FreeGroupoid-universal .F₁ fs D.∘ FreeGroupoid-universal .F₁ gs}
      (λ _ → hlevel 1)
      (λ _ → sym (D.idr _))
      (λ f fs rec _ → D.pushl (rec _))
      (λ f fs rec _ → D.pushl (rec _))
      gs fs

    FreeGroupoid-factor : F ≡ FreeGroupoid-universal F∘ FreeGroupoid-unit C
    FreeGroupoid-factor = Functor-path (λ _ → refl) (λ _ → sym (D.idl _))

  module _ (C-grpd : is-pregroupoid C) where
    FreeGroupoid-counit : Functor (FreeGroupoid C) C
    FreeGroupoid-counit = FreeGroupoid-universal C-grpd Id
```

With some adjunction yoga, we get the action of the free groupoid functor
on *morphisms*: this takes a functor between categories $\cC$ and $\cD$ to a
functor between their free groupoids.

```agda
FreeGroupoid-map
  : ∀ {oc ℓc od ℓd} {C : Precategory oc ℓc} {D : Precategory od ℓd}
  → Functor C D → Functor (FreeGroupoid C) (FreeGroupoid D)
FreeGroupoid-map F = FreeGroupoid-universal FreeGroupoid-is-groupoid
  (FreeGroupoid-unit _ F∘ F)
```

We also derive a useful induction principle for sets, i.e. [[discrete categories]]:
any function from the objects of $\cC$ into a set that turns morphisms into
equalities also turns zigzags into equalities.

```agda
module _ {o ℓ ℓd} {C : Precategory o ℓ} (D : Set ℓd) where
  open Precategory

  Zigzag-elim-set
    : (f : Ob C → ∣ D ∣)
    → (∀ {x y} → Hom C x y → f x ≡ f y)
    → ∀ {x y} → Zigzag C x y → f x ≡ f y
  Zigzag-elim-set f f-const = FreeGroupoid-universal Disc-is-groupoid
    (Disc-into D f f-const) .F₁
```
