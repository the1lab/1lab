<!--
```agda
open import 1Lab.Reflection.Marker

open import Cat.Prelude
```
-->

```agda
module Cat.Instances.Sets where
```

# The category of Sets

We prove that the category of Sets is [[univalent|univalent category]].
Recall that this means that, fixing a set $A$, the type $\sum_{(B :
\set)} (A \cong B)$ is contractible. We first exhibit a contraction
directly, using `ua`{.Agda}, and then provide an alternative proof in
terms of [univalence for $n$-types].

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
  iso→equiv x .fst = x .Sets.to
  iso→equiv x .snd = is-iso→is-equiv $ iso x.from (happly x.invl) (happly x.invr)
    where module x = Sets._≅_ x
```

Using univalence for $n$-types, function extensionality and the
computation rule for univalence, it is almost trivial to show that
categorical isomorphisms of sets are an [[identity system]].

```agda
  Sets-is-category : is-category (Sets ℓ)
  Sets-is-category .to-path i = n-ua (iso→equiv i)
  Sets-is-category .to-path-over p = Sets.≅-pathp refl _ $
    funextP λ a → path→ua-pathp _ refl
```

## Indirect proof

While the proof above is fairly simple, we _can_ give a different
formulation, which might be more intuitive. Let's start by showing that
the rearrangement `iso→equiv`{.Agda} is an equivalence:

```agda
  equiv→iso : {A B : Set ℓ} → ∣ A ∣ ≃ ∣ B ∣ → A Sets.≅ B
  equiv→iso (f , f-eqv) =
    Sets.make-iso f (equiv→inverse f-eqv)
      (funext (equiv→counit f-eqv))
      (funext (equiv→unit f-eqv))

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

```agda
  is-category'-Sets : ∀ {A B : Set ℓ} → (A ≡ B) ≃ (A Sets.≅ B)
  is-category'-Sets {A} {B} =
    (A ≡ B)         ≃⟨ n-univalence e⁻¹ ⟩
    (∣ A ∣ ≃ ∣ B ∣) ≃⟨ equiv≃iso e⁻¹ ⟩
    (A Sets.≅ B)    ≃∎
```

## Sets^op is also a category

```agda
  import Cat.Reasoning (Sets ℓ ^op) as Sets^op
```

First we show that isomorphism is invariant under `^op`{.Agda}.

```agda
  iso-op-invariant : ∀ {A B : Set ℓ} → (A Sets^op.≅ B) ≃ (A Sets.≅ B)
  iso-op-invariant {A} {B} = Iso→Equiv the-iso
    where
      open import Cat.Morphism
      open Inverses
      the-iso : Iso (A Sets^op.≅ B) (A Sets.≅ B) 
      the-iso .fst i .to = i .from
      the-iso .fst i .from = i .to
      the-iso .fst i .inverses .invl = i .invl
      the-iso .fst i .inverses .invr = i .invr
      the-iso .snd .is-iso.inv i .to = i .from
      the-iso .snd .is-iso.inv i .from = i .to
      the-iso .snd .is-iso.inv i .inverses .invl = i .invl
      the-iso .snd .is-iso.inv i .inverses .invr = i .invr
      the-iso .snd .is-iso.rinv _ = refl
      the-iso .snd .is-iso.linv _ = refl
```

This fact lets us re-use the `to-path`{.Agda} component of `Sets-is-category`{.Agda}. Some calculation gives us `to-path-over`{.Agda}.

```agda
  Sets^op-is-category : is-category (Sets ℓ ^op)
  Sets^op-is-category .to-path = Sets-is-category .to-path ⊙ transport (ua iso-op-invariant)
  Sets^op-is-category .to-path-over {a} {b} p = Sets^op.≅-pathp refl _ $ funext-dep λ {x₀} {x₁} q →
    x₀                                                    ≡˘⟨ ap (_$ x₀) p.invr ⟩ 
    p.to ⌜ p.from x₀ ⌝                                    ≡˘⟨ ap¡ Regularity.reduce! ⟩ 
    p.to ⌜ transport refl $ p.from $ transport refl x₀ ⌝  ≡⟨ ap! (λ i → unglue (∂ i) (q i)) ⟩
    p.to x₁                                               ∎
    where module p = Sets^op._≅_ p
```  
