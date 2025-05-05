---
description: |
  While isomorphism is not well-behaved as a notion of equivalence, it
  turns out that equipping a map with 2 inverses instead of 1 makes
  *is*. We call these biinvertible maps.
---

<!--
```agda
open import 1Lab.HLevel.Closure
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.Equiv.Biinv where
```

<!--
```agda
private variable
  ℓ : Level
  A B C : Type ℓ
```
-->

# Bi-invertible maps {defines="biinvertible-map"}

Recall the three conditions that make up the notion of [equivalence].

> To be more specific, what we need for a notion of equivalence
$\isequiv(f)$ to be "coherent" is:
>
> - Being an `isomorphism`{.Agda ident=is-iso} implies being an
`equivalence`{.Agda ident=is-equiv} ($\isiso(f) \to
\isequiv(f)$)
>
> - Being an equivalence implies being an isomorphism ($\isequiv(f)
\to \isiso(f)$); Taken together with the first point we may
summarise: "Being an equivalence and being an isomorphism are logically
equivalent."
>
> - Most importantly, being an equivalence _must_ be a proposition.

[equivalence]: 1Lab.Equiv.html#equivalences

The "blessed" definition of equivalence is that of a map with
[[contractible fibres|equivalence]]. However, this definition is highly
abstract, so it begs the question: Is it possible to describe a simpler
notion of equivalence that still satisfies the three conditions? The
answer is yes! Paradoxically, adding _more_ data to `is-iso`{.Agda}
leaves us with a good notion of equivalence.

::: {.popup .keep}
A **left inverse** to a function $f : A \to B$ is a function $g : B \to
A$ equipped with a [[homotopy]] $g \circ f \sim \id$. Symmetrically, a
**right inverse** to $f$ is a function $h : B \to A$ equipped with a
homotopy $f \circ h \sim \id$.

```agda
linv : (A → B) → Type _
linv f = Σ[ g ∈ (_ → _) ] (g ∘ f ≡ id)

rinv : (A → B) → Type _
rinv f = Σ[ h ∈ (_ → _) ] (f ∘ h ≡ id)
```

A map $f$ equipped with a choice of left- and right- inverse is said to
be **biinvertible**. Perhaps surprisingly, `is-biinv`{.Agda} is a [[good
notion of equivalence]].
:::

```agda
is-biinv : (A → B) → Type _
is-biinv f = linv f × rinv f
```

If $f$ is an equivalence, then so are pre- and post- composition with
$f$. This can be proven using [[equivalence induction]], but a more
elementary argument --- directly constructing quasi-inverses ---
suffices, and doesn't use the sledgehammer that is univalence.

The proof is as follows: If $f : A \to B$ has inverse $f\inv : B → A$,
then $(f\inv \circ -)$ and $(- \circ f\inv)$ are inverses to $(f \circ
-)$ and $(- \circ f)$.

```agda
is-equiv→pre-is-equiv  : {f : A → B} → is-equiv f → is-equiv {A = C → A} (f ∘_)
is-equiv→post-is-equiv : {f : A → B} → is-equiv f → is-equiv {A = B → C} (_∘ f)
```

<details>
<summary> The proof is by `is-equiv→is-iso`{.Agda} and
`is-iso→is-equiv`{.Agda}. Nothing too clever. </summary>

```agda
is-equiv→pre-is-equiv {f = f} f-eqv = is-iso→is-equiv isiso where
  f-iso : is-iso f
  f-iso = is-equiv→is-iso f-eqv

  f⁻¹ : _
  f⁻¹ = f-iso .is-iso.inv

  isiso : is-iso (_∘_ f)
  isiso .is-iso.inv f x = f⁻¹ (f x)
  isiso .is-iso.rinv f = funext λ x → f-iso .is-iso.rinv _
  isiso .is-iso.linv f = funext λ x → f-iso .is-iso.linv _

is-equiv→post-is-equiv {f = f} f-eqv = is-iso→is-equiv isiso where
  f-iso : is-iso f
  f-iso = is-equiv→is-iso f-eqv

  f⁻¹ : _
  f⁻¹ = f-iso .is-iso.inv

  isiso : is-iso _
  isiso .is-iso.inv f x = f (f⁻¹ x)
  isiso .is-iso.rinv f = funext λ x → ap f (f-iso .is-iso.linv _)
  isiso .is-iso.linv f = funext λ x → ap f (f-iso .is-iso.rinv _)
```
</details>

With this lemma, it can be shown that if $f$ is an isomorphism, then
`linv(f)`{.Agda ident=linv} and `rinv(f)`{.Agda ident=rinv} are both
contractible.

```agda
is-iso→is-contr-linv : {f : A → B} → is-iso f → is-contr (linv f)
is-iso→is-contr-linv isiso =
  is-equiv→post-is-equiv (is-iso→is-equiv isiso) .is-eqv id

is-iso→is-contr-rinv : {f : A → B} → is-iso f → is-contr (rinv f)
is-iso→is-contr-rinv isiso =
  is-equiv→pre-is-equiv (is-iso→is-equiv isiso) .is-eqv id
```

This is because `linv(f)`{.Agda} is the fibre of $(- \circ f)$ over
`id`{.Agda}, and the fibres of an equivalence are contractible. Dually,
`rinv(f)`{.Agda} is the fibre of $(f \circ -)$ over `id`{.Agda}.

```agda
_ : {f : A → B} → linv f ≡ fibre (_∘ f) id
_ = refl

_ : {f : A → B} → rinv f ≡ fibre (f ∘_) id
_ = refl
```

We show that if a map is biinvertible, then it is invertible. This is
because if a function has two inverses, they coincide:

```agda
is-biinv→is-iso : {f : A → B} → is-biinv f → is-iso f
is-biinv→is-iso {f = f} ((g , g∘f≡id) , h , h∘f≡id) = iso h (happly h∘f≡id) beta
  where
    beta : (x : _) → h (f x) ≡ x
    beta x =
      h (f x)         ≡⟨ happly (sym g∘f≡id) _ ⟩
      g (f (h (f x))) ≡⟨ ap g (happly h∘f≡id _) ⟩
      g (f x)         ≡⟨ happly g∘f≡id _ ⟩
      x               ∎
```

Finally, we can show that being biinvertible is [[proposition]]. Since
propositions are those types which are `contractible if inhabited`{.Agda
ident=is-contr-if-inhabited→is-prop} suffices to show that
`is-biinv`{.Agda} is contractible when it is inhabited:

```agda
is-biinv-is-prop : {f : A → B} → is-prop (is-biinv f)
is-biinv-is-prop {f = f} = is-contr-if-inhabited→is-prop contract where
  contract : is-biinv f → is-contr (is-biinv f)
  contract ibiinv =
    ×-is-hlevel 0 (is-iso→is-contr-linv iiso)
                  (is-iso→is-contr-rinv iiso)
    where
      iiso = is-biinv→is-iso ibiinv
```

Since `is-biinv`{.Agda} is a product of contractibles whenever it is
inhabited, then it is contractible. Finally, we have that $\isiso(f) \to
\operatorname{is-biinv}(f)$: pick the given inverse as both a left- and
right- inverse.

```agda
is-iso→is-biinv : {f : A → B} → is-iso f → is-biinv f
is-iso→is-biinv iiso .fst = iiso .is-iso.inv , funext (iiso .is-iso.linv)
is-iso→is-biinv iiso .snd = iiso .is-iso.inv , funext (iiso .is-iso.rinv)
```
