```agda
open import Cat.Prelude

module Cat.Diagram.Idempotent {o h} (C : Precategory o h) where
```

<!--
```agda
open import Cat.Reasoning C
private variable
  A B : Ob
  f : Hom A B
```
-->

# Idempotents

**Idempotents** are the categorical generalisation of projections, in
the sense of linear algebra. Formally, an idempotent $e : A \to A$ is a
map with $e \circ e = e$. Keeping in line with the view that an
idempotent is like a projection, we can ask _what_ it projects onto: We
would then have some subobject $F$ of fixed elements, and a
decomposition of $e$ as

$$
X \to F \mono X
$$

When this is the case, we say that $e$ is a **split idempotent**: We
have some pair of maps $p : X \to F$ (the "projector") and $i : F \to
X$, with $r \circ i = \id{id}$ and $i \circ r = e$.

```agda
is-idempotent : Hom A A → Type _
is-idempotent e = e ∘ e ≡ e

record is-split (e : Hom A A) : Type (o ⊔ h) where
  field
    {F}     : Ob
    project : Hom A F
    inject  : Hom F A

    p∘i : project ∘ inject ≡ id
    i∘p : inject ∘ project ≡ e

is-split→is-idempotent : is-split f → is-idempotent f
is-split→is-idempotent {f = f} spl =
  f ∘ f             ≡˘⟨ ap₂ _∘_ i∘p i∘p ⟩
  (s ∘ r) ∘ (s ∘ r) ≡⟨ cancel-inner p∘i ⟩
  s ∘ r             ≡⟨ i∘p ⟩
  f                 ∎
  where open is-split spl renaming (inject to s ; project to r)
```

It's not the case that idempotents are split in every category. Those
where this is the case are called **idempotent-complete**. Every
category can be embedded, by a [full and faithful] functor, into an
idempotent-complete category; This construction is called the [Karoubi
envelope] of $\ca{C}$.

[full and faithful]: Cat.Functor.Base.html#ff-functors
[Karoubi envelope]: Cat.Instances.Karoubi.html

```agda
is-idempotent-complete : Type _
is-idempotent-complete = ∀ {A} (f : Hom A A) → is-idempotent f → is-split f
```
