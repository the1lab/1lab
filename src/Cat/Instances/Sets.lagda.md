```agda
open import Cat.Prelude

module Cat.Instances.Sets where
```

# The category of Sets

We prove that the category of Sets is [univalent]. Recall that this
means that, fixing a set $A$, the type $\sum_{(B : \set)} (A \cong B)$
is contractible. We first exhibit a contraction directly, using
`ua`{.Agda}, and then provide an alternative proof in terms of
[univalence for $n$-types].

[univalent]: Cat.Univalent.html
[univalence for $n$-types]: 1Lab.HLevel.Universe.html

## Direct proof

The direct proof is surprisingly straightforward, in particular because
the heavy lifting is done by a plethora of existing lemmas:
`Iso→Equiv`{.Agda} to turn an isomorphism into an equivalence,
`path→ua-pathp`{.Agda} to reduce dependent paths over `ua`{.Agda} to
non-dependent paths, `≅-pathp`{.Agda} to characterise dependent paths in
`_≅_`{.Agda}, etc.

```agda
module _ {ℓ} where
  import Cat.Reasoning (Sets ℓ) as Sets
```

We must first rearrange `_≅_`{.Agda} to `_≃_`{.Agda}, for which we can
use `Iso→Equiv`{.Agda}. We must then show that an isomorphism in the
category of Sets is the same thing as an isomorphism of types; But the
only difference between these types can be patched by
`happly`{.Agda}/`funext`{.Agda}.

```agda
  iso→equiv : {A B : Set ℓ} → A Sets.≅ B → ∣ A ∣ ≃ ∣ B ∣
  iso→equiv x = Iso→Equiv (x.to , iso x.from (happly x.invl) (happly x.invr))
    where module x = Sets._≅_ x
```

We then fix a set $A$ and show that the type of "sets equipped with an
isomorphism to $A$" is contractible. For the center of contraction, as
is usual, we pick $A$ itself and the identity isomorphism.

```agda
  Sets-is-category : is-category (Sets ℓ)
  Sets-is-category A = isc where
    isc : is-contr (Σ[ B ∈ Set ℓ ] (A Sets.≅ B))
    isc .centre = A , Sets.id-iso
```

We must then show that, given some other set $B$ and an isomorphism $i :
A \cong B$, we can continuously deform $A$ into $B$ and, in the process,
deform $i$ into the identity. But this follows from `paths in sigma
types`{.Agda ident=Σ-pathp}, the rearranging of isomorphisms defined
above, and `n-ua`{.Agda}.

```agda
    isc .paths (B , isom) =
      Σ-pathp (n-ua A≃B)
        (Sets.≅-pathp refl _
          (λ i x → path→ua-pathp A≃B {x = x} {y = isom.to x} refl i))
      where
        module isom = Sets._≅_ isom

        A≃B : ∣ A ∣ ≃ ∣ B ∣
        A≃B = iso→equiv isom
```

## Indirect proof

While the proof above is fairly simple, we _can_ give a different
formulation, which might be more intuitive. Let's start by showing that
the rearrangement `iso→equiv`{.Agda} is an equivalence:

```agda
  equiv→iso : {A B : Set ℓ} → ∣ A ∣ ≃ ∣ B ∣ → A Sets.≅ B
  equiv→iso (f , f-eqv) =
    Sets.make-iso f (equiv→inverse f-eqv)
      (funext (equiv→section f-eqv))
      (funext (equiv→retraction f-eqv))

  equiv≃iso : {A B : Set ℓ} → (A Sets.≅ B) ≃ (∣ A ∣ ≃ ∣ B ∣)
  equiv≃iso {A} {B} = Iso→Equiv (iso→equiv , iso equiv→iso p q)
    where
      p : is-right-inverse (equiv→iso {A} {B}) iso→equiv
      p x = Σ-prop-path is-equiv-is-prop refl

      q : is-left-inverse (equiv→iso {A} {B}) iso→equiv
      q x = Sets.≅-pathp refl refl refl
```

We then use [univalence for $n$-types] to directly establish that $(A
\equiv B) \simeq (A \cong B)$:

```
  is-category′-Sets : ∀ {A B : Set ℓ} → (A ≡ B) ≃ (A Sets.≅ B)
  is-category′-Sets {A} {B} =
    (A ≡ B)         ≃⟨ n-univalence e⁻¹ ⟩
    (∣ A ∣ ≃ ∣ B ∣) ≃⟨ equiv≃iso e⁻¹ ⟩
    (A Sets.≅ B)    ≃∎
```
