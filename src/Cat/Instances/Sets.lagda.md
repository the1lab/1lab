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
`Path→uaPathP`{.Agda} to reduce dependent paths over `ua`{.Agda} to
non-dependent paths, `≅-PathP`{.Agda} to characterise dependent paths in
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
  iso→equiv : {A B : Set ℓ} → A Sets.≅ B → A .fst ≃ B .fst
  iso→equiv x = Iso→Equiv (x.to , iso x.from (happly x.invˡ) (happly x.invʳ))
    where module x = Sets._≅_ x
```

We then fix a set $A$ and show that the type of "sets equipped with an
isomorphism to $A$" is contractible. For the center of contraction, as
is usual, we pick $A$ itself and the identity isomorphism.

```agda
  isCategory-Sets : isCategory (Sets ℓ)
  isCategory-Sets A = isc where
    isc : isContr (Σ[ B ∈ Set ℓ ] (A Sets.≅ B))
    isc .centre = A , Sets.idIso
```

We must then show that, given some other set $B$ and an isomorphism $i :
A \cong B$, we can continuously deform $A$ into $B$ and, in the process,
deform $i$ into the identity. But this follows from `paths in sigma
types`{.Agda ident=Σ-PathP}, the rearranging of isomorphisms defined
above, and `ua`{.Agda}.

```agda
    isc .paths (B , isom) = 
      Σ-PathP (Σ≡Prop (λ _ → isProp-isHLevel 2) (ua A≃B))
        (Sets.≅-PathP refl _ 
          (λ i x → Path→uaPathP A≃B {x = x} {y = isom.to x} refl i) 
          (ua→ λ a → sym (happly isom.invʳ a)))
      where
        module isom = Sets._≅_ isom

        A≃B : A .fst ≃ B .fst
        A≃B = iso→equiv isom
```

## Indirect proof

While the proof above is fairly simple, we _can_ give a different
formulation, which might be more intuitive. Let's start by showing that
the rearrangement `iso→equiv`{.Agda} is an equivalence:

```agda
  equiv→iso : {A B : Set ℓ} → A .fst ≃ B .fst → A Sets.≅ B
  equiv→iso (f , f-eqv) = 
    Sets.makeIso f (equiv→inverse f-eqv) 
      (funext (equiv→section f-eqv)) 
      (funext (equiv→retraction f-eqv))

  equiv≃iso : {A B : Set ℓ} → (A Sets.≅ B) ≃ (A .fst ≃ B .fst)
  equiv≃iso {A} {B} = Iso→Equiv (iso→equiv , iso equiv→iso p q)
    where
      p : isRightInverse (equiv→iso {A} {B}) iso→equiv
      p x = Σ≡Prop isProp-isEquiv refl

      q : isLeftInverse (equiv→iso {A} {B}) iso→equiv
      q x = Sets.≅-PathP refl refl refl refl
```

We then use [univalence for $n$-types] to directly establish that $(A
\equiv B) \simeq (A \cong B)$:

```
  isCategory′-Sets : ∀ {A B : Set ℓ} → (A ≡ B) ≃ (A Sets.≅ B)
  isCategory′-Sets {A} {B} = 
    (A ≡ B)           ≃⟨ nType-univalence {n = 2} ⟩
    (A .fst ≃ B .fst) ≃⟨ equiv≃iso e⁻¹ ⟩
    (A Sets.≅ B)      ≃∎
```