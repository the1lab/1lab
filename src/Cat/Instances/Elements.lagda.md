```agda
open import Cat.Prelude

module Cat.Instances.Elements {o ℓ s} (C : Precategory o ℓ)
  (P : Functor (C ^op) (Sets s)) where
```

<!--
```agda
open import Cat.Reasoning C
open Functor

private
  module P = Functor P
```
-->

# The Category of Elements

The category of elements over some presheaf $P : C^{op} \to Set$ is a
means of unpacking the data of the presheaf. It's objects are pairs
of an object $x$, and a section $s : P x$.

```agda
record Element : Type (o ⊔ s) where
  constructor elem
  field
    ob : Ob
    section : fst $ P.₀ ob

open Element
```

We can think of this as taking an eraser to the data of $P$. If
$P(x) = \{x_0, x_1, x_2\}$, then the category of elements of $P$
will have three objects in place of the one: $(x, x_0)$, $(x, x_1)$,
and $(x, x_2)$. We've erased all the boundaries of each of the sets
associated with $P$, and are left with a big soup of points.

We do something similar for morphisms, and turn function
$P(f) : P(Y) \to P(X)$ into a huge collection of morphisms between
points. We do this by defining a morphism $(x, x_0) \to (y, y_0)$
as a morphism $f : X \to Y$ in $\ca{C}$, as well as a proof that
$P(f)(y_0) = x_0$ This too can be seen as erasing boundaries, just
this time with the data associated with a function. Instead of
having a bunch of data bundled together that describes the action
of $P(f)$ on each point of $P(Y)$, we have a bunch of tiny bits of data
that only describe the action of $P(f)$ on a single point.

```agda
record ElementHom (x y : Element) : Type (ℓ ⊔ s) where
  constructor elem-hom
  no-eta-equality
  field
    hom : Hom (x .ob) (y .ob)
    commute : P.₁ hom (y .section) ≡ x .section

open ElementHom
```

As per usual, we need to prove some helper lemmas that describe the
path space of `ElementHom`{.Agda}

```agda
ElementHom≡ : {x y : Element} {f g : ElementHom x y} → f .hom ≡ g .hom → f ≡ g 
ElementHom≡ p i .hom = p i
ElementHom≡ {x = x} {y = y} {f = f} {g = g} p i .commute =
  isProp→PathP (λ j → snd (P.₀ (x .ob)) (P.₁ (p j) (y .section)) (x .section))
    (f .commute)
    (g .commute) i
```

<!--
```agda
ElementHom-isSet : ∀ (x y : Element) → isSet (ElementHom x y)
ElementHom-isSet x y =
  isHLevel-retract 2 Refold Unfold retract T-isSet
  where
    T : Type _
    T = Σ[ hom ∈ Hom (x .ob) (y .ob) ]
        (P.₁ hom (y .section) ≡ x .section)

    Refold : T → ElementHom x y
    Refold (h , p) = elem-hom h p

    Unfold : ElementHom x y → T
    Unfold f = (f .hom , f .commute)

    retract : ∀ x → Refold (Unfold x) ≡ x
    retract x i .hom = x .hom
    retract x i .commute = x .commute

    T-isSet : isSet T
    T-isSet =
      isHLevelΣ 2 (Hom-set _ _)
                  λ f → isHLevelPath 2 (snd $ P.₀ (x .ob))
```
-->

One interesting fact is that morphisms $f : X \to Y$ in $C$ induce
morphisms in the category of elements for each $py : P(y)$.

```agda
induce : ∀ {x y} → (f : Hom x y) → (py : P.₀ y .fst)
         → ElementHom (elem x (P.₁ f py)) (elem y py)
induce f _ = elem-hom f refl
```

Using all this machinery, we can now define the category of elements of
$P$!

```agda
∫ : Precategory (o ⊔ s) (ℓ ⊔ s)
∫ .Precategory.Ob = Element
∫ .Precategory.Hom = ElementHom
∫ .Precategory.Hom-set = ElementHom-isSet
∫ .Precategory.id {x = x} = elem-hom id  λ i → P.F-id i (x .section)
∫ .Precategory._∘_ {x = x} {y = y} {z = z} f g = elem-hom (f .hom ∘ g .hom) comm
  where
    abstract
      comm : P.₁ (f .hom ∘ g .hom) (z .section) ≡ x .section
      comm = 
        P.₁ (f .hom ∘ g .hom) (z .section)       ≡⟨ happly (P.F-∘ (g .hom) (f .hom)) (z .section) ⟩
        P.₁ (g .hom) (P.₁ (f .hom) (z .section)) ≡⟨ ap (P.F₁ (g .hom)) (f .commute)  ⟩
        P.₁ (g .hom) (y .section)                ≡⟨ g .commute ⟩
        x .section ∎
∫ .Precategory.idr f = ElementHom≡ (idr (f .hom))
∫ .Precategory.idl f = ElementHom≡ (idl (f .hom))
∫ .Precategory.assoc f g h = ElementHom≡ (assoc (f .hom) (g .hom) (h .hom))
```

## Projection

The category of elements is equipped with a canonical projection functor
$\pi_p : \int P \to C$, which just forgets all of the points and
morphism actions.

```agda
πₚ : Functor ∫ C
πₚ .F₀ x = x .ob
πₚ .F₁ f = f .hom
πₚ .F-id = refl
πₚ .F-∘ f g = refl
```

This functor makes it clear that we ought to think of the category
of elements as something defined _over_ $\ca{C}$. For instance, if we
look at the fibre over each $X : \ca{C}$, we get back the set $P(X)$!
