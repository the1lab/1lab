```
open import 1Lab.Prelude

open import Algebra.Group

module Algebra.Group.Cayley {ℓ} (G : Group ℓ) where

open Group-on (G .snd) renaming (underlying-set to G-set)
```

# Cayley's Theorem

Cayley's theorem says that any group $G$ admits a representation as a
subgroup of a [symmetric group], specifically the symmetric group acting
on the underlying set of $G$.

[symmetric group]: Algebra.Group.html#symmetric-groups

To start with, we note that any element $x$ of $G$ determines a
bijection on the underlying set of $G$, by multiplication with $x$ on
the left. The inverse of this bijection is given by multiplication with
$x^{-1}$, and the proof that these are in fact inverse functions are
given by the group laws:

```agda
Cayley : G .fst → G .fst ≃ G .fst
Cayley x = Iso→Equiv bij where
  bij : Iso _ _
  bij .fst y = x ⋆ y
  bij .snd .is-iso.inv y = x ⁻¹ ⋆ y
  bij .snd .is-iso.rinv y =
    x ⋆ (x ⁻¹ ⋆ y) ≡⟨ cancell inverser ⟩
    y              ∎
  bij .snd .is-iso.linv y =
    x ⁻¹ ⋆ (x ⋆ y) ≡⟨ cancell inversel ⟩
    y              ∎
```

We then show that this map is a group homomorphism from $G$ to
$\id{Sym}(G)$:

```agda
Cayley-is-hom : Group-hom G (Sym G-set) Cayley
Cayley-is-hom .Group-hom.pres-⋆ x y = Σ-prop-path is-equiv-is-prop (funext lemma) where
  lemma : (e : G .fst) → (x ⋆ y) ⋆ e ≡ x ⋆ (y ⋆ e)
  lemma e = sym associative
```

Finally, we show that this map is injective; Thus, $G$ embeds as a
subgroup of $\id{Sym}(G)$ (the image of `Cayley`{.Agda}).

```agda
Cayley-injective : injective Cayley
Cayley-injective {x} {y} eqvs-equal =
  x                   ≡⟨ sym idr ⟩
  x ⋆ unit            ≡⟨⟩
  Cayley x .fst unit  ≡⟨ happly (ap fst eqvs-equal) unit ⟩
  Cayley y .fst unit  ≡⟨⟩
  y ⋆ unit            ≡⟨ idr ⟩
  y                   ∎
```
