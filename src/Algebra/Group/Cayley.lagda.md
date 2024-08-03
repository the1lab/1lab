<!--
```
open import 1Lab.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Group
```
-->

```agda
module Algebra.Group.Cayley {ℓ} (G : Group ℓ) where

open Group-on (G .snd) renaming (underlying-set to G-set)
```

# Cayley's theorem {defines="cayleys-theorem"}

Cayley's theorem says that any group $G$ admits a representation as a
subgroup of a [symmetric group], specifically the symmetric group acting
on the underlying set of $G$.

[symmetric group]: Algebra.Group.html#symmetric-groups

First, recall that we get a family of equivalences $G \simeq G$ by multiplication
on the left, the [[principal action]] of $G$ on itself:

```agda
Cayley : ⌞ G ⌟ → ⌞ G ⌟ ≃ ⌞ G ⌟
Cayley x = (λ y → x ⋆ y) , ⋆-equivl x
```

We then show that this map is a group homomorphism from $G$ to
$\rm{Sym}(G)$:

```agda
Cayley-is-hom : is-group-hom (G .snd) (Sym G-set) Cayley
Cayley-is-hom .is-group-hom.pres-⋆ x y = ext λ e → sym associative
```

Finally, we show that this map is injective; Thus, $G$ embeds as a
subgroup of $\rm{Sym}(G)$ (the image of `Cayley`{.Agda}).

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
