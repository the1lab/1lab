---
description: |
  While isomorphism is not well-behaved as a notion of equivalence, it
  turns out that equipping a map with 2 inverses instead of 1 makes
  *is*. We call these biinvertible maps.
---

```agda
open import 1Lab.HLevel.Retracts
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Equiv.Biinv where
```

<!--
```
private variable
  ℓ : Level
  A B C : Type ℓ
```
-->

# Bi-invertible maps

Recall the three conditions that make up the notion of [equivalence].

> To be more specific, what we need for a notion of equivalence
$\mathrm{isEquiv}(f)$ to be "coherent" is:
>
> - Being an `isomorphism`{.Agda ident=isIso} implies being an
`equivalence`{.Agda ident=isEquiv} ($\mathrm{isIso}(f) \to
\mathrm{isEquiv}(f)$)
>
> - Being an equivalence implies being an isomorphism
($\mathrm{isEquiv}(f) \to \mathrm{isIso}(f)$); Taken together with the
first point we may summarise: "Being an equivalence and being an
isomorphism are logically equivalent."
>
> - Most importantly, being an equivalence _must_ be a proposition.

[equivalence]: 1Lab.Equiv.html#equivalences

The "blessed" definition of equivalence is that of a map with
[contractible fibres]. However, this definition is highly abstract, so
it begs the question: Is it possible to describe a simpler notion of
equivalence that still satisfies the three conditions? The answer is
yes! Paradoxically, adding _more_ data to `isIso`{.Agda} leaves us with
a good notion of equivalence.

[contractible fibres]: agda://1Lab.Equiv#isEquiv

A **left inverse** to a function $f : A \to B$ is a function $g : B \to
A$ equipped with a [homotopy] $g \circ f \sim \mathrm{id}$. Symmetrically,
a **right inverse** to $f$ is a function $h : B \to A$ equipped with a
homotopy $f \circ h \sim \mathrm{id}$.

[homotopy]: agda://1Lab.Path#funext

```agda
linv : (A → B) → Type _
linv f = Σ[ g ∈ (_ → _) ] (g ∘ f ≡ id)

rinv : (A → B) → Type _
rinv f = Σ[ h ∈ (_ → _) ] (f ∘ h ≡ id)
```

A map $f$ equipped with a choice of left- and right- inverse is said to
be **biinvertible**. Perhaps surprisingly, `isBiinv`{.Agda} is a [good
notion of equivalence].

[good notion of equivalence]: 1Lab.Equiv.html#equivalences

```agda
isBiinv : (A → B) → Type _
isBiinv f = linv f × rinv f
```

If $f$ is an equivalence, then so are pre- and post- composition with
$f$. This can be proven using [equivalence induction], but a more
elementary argument --- directly constructing quasi-inverses ---
suffices, and doesn't use the sledgehammer that is univalence.

[equivalence induction]: agda://1Lab.Univalence#EquivJ

The proof is as follows: If $f : A \to B$ has inverse $f^{-1} : B → A$,
then $(f^{-1} \circ -)$ and $(- \circ f^{-1})$ are inverses to $(f \circ
-)$ and $(- \circ f)$.

```agda
isEquiv→isEquiv-precomp  : {f : A → B} → isEquiv f → isEquiv {A = C → A} (f ∘_)
isEquiv→isEquiv-postcomp : {f : A → B} → isEquiv f → isEquiv {A = B → C} (_∘ f)
```

<details>
<summary> The proof is by `isEquiv→isIso`{.Agda} and
`isIso→isEquiv`{.Agda}. Nothing too clever. </summary>
```
isEquiv→isEquiv-precomp {f = f} f-eqv = isIso→isEquiv isiso where
  f-iso : isIso f
  f-iso = isEquiv→isIso f-eqv

  f⁻¹ : _
  f⁻¹ = f-iso .isIso.inv

  isiso : isIso (_∘_ f)
  isiso .isIso.inv f x = f⁻¹ (f x)
  isiso .isIso.rinv f = funext λ x → f-iso .isIso.rinv _
  isiso .isIso.linv f = funext λ x → f-iso .isIso.linv _

isEquiv→isEquiv-postcomp {f = f} f-eqv = isIso→isEquiv isiso where
  f-iso : isIso f
  f-iso = isEquiv→isIso f-eqv

  f⁻¹ : _
  f⁻¹ = f-iso .isIso.inv

  isiso : isIso _
  isiso .isIso.inv f x = f (f⁻¹ x)
  isiso .isIso.rinv f = funext λ x → ap f (f-iso .isIso.linv _)
  isiso .isIso.linv f = funext λ x → ap f (f-iso .isIso.rinv _)
```
</details>

With this lemma, it can be shown that if $f$ is an isomorphism, then
`linv(f)`{.Agda ident=linv} and `rinv(f)`{.Agda ident=rinv} are both
contractible.

```agda
isIso→isContr-linv : {f : A → B} → isIso f → isContr (linv f)
isIso→isContr-linv isiso =
  isEquiv→isEquiv-postcomp (isIso→isEquiv isiso) .isEqv id

isIso→isContr-rinv : {f : A → B} → isIso f → isContr (rinv f)
isIso→isContr-rinv isiso =
  isEquiv→isEquiv-precomp (isIso→isEquiv isiso) .isEqv id
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
isBiinv→isIso : {f : A → B} → isBiinv f → isIso f
isBiinv→isIso {f = f} ((g , g∘f≡id) , h , h∘f≡id) = iso h (happly h∘f≡id) beta
  where
    beta : (x : _) → h (f x) ≡ x
    beta x = 
      h (f x)         ≡⟨ happly (sym g∘f≡id) _ ⟩
      g (f (h (f x))) ≡⟨ ap g (happly h∘f≡id _) ⟩
      g (f x)         ≡⟨ happly g∘f≡id _ ⟩
      x               ∎
```

Finally, we can show that being biinvertible is [a proposition]. Since
propositions are those types which are [contractible if inhabited]
suffices to show that `isBiinv` is contractible when it is inhabited:

[a proposition]: agda://1Lab.HLevel#isProp
[contractible if inhabited]: agda://1Lab.HLevel#inhContr→isProp

```agda
isProp-isBiinv : {f : A → B} → isProp (isBiinv f)
isProp-isBiinv {f = f} = inhContr→isProp contract where
  contract : isBiinv f → isContr (isBiinv f)
  contract ibiinv =
    isHLevel× 0 (isIso→isContr-linv iiso)
                (isIso→isContr-rinv iiso)
    where
      iiso = isBiinv→isIso ibiinv
```

Since `isBiinv`{.Agda} is a product of contractibles whenever it is
inhabited, then it is contractible. Finally, we have that
$\mathrm{isIso}(f) \to \mathrm{isBiinv}(f)$: pick the given inverse as
both a left- and right- inverse.

```agda
isIso→isBiinv : {f : A → B} → isIso f → isBiinv f
isIso→isBiinv iiso .fst = iiso .isIso.inv , funext (iiso .isIso.linv)
isIso→isBiinv iiso .snd = iiso .isIso.inv , funext (iiso .isIso.rinv)
```
