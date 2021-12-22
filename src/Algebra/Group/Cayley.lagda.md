```
open import Algebra.Group

open import 1Lab.Prelude

module Algebra.Group.Cayley {ℓ} (G : Group ℓ) where

open GroupOn (G .snd) renaming (underlying-set to G-set)
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

```
Cayley : G .fst → G .fst ≃ G .fst
Cayley x = Iso→Equiv bij where
  bij : Iso _ _
  bij .fst y = x ⋆ y
  bij .snd .isIso.inv y = inverse x ⋆ y
  bij .snd .isIso.rinv y =
    x ⋆ (inverse x ⋆ y) ≡⟨ associative ⟩
    (x ⋆ inverse x) ⋆ y ≡⟨ ap₂ _⋆_ inverseʳ refl ⟩
    unit ⋆ y            ≡⟨ idˡ ⟩
    y                   ∎
  bij .snd .isIso.linv y =
    inverse x ⋆ (x ⋆ y) ≡⟨ associative ⟩
    (inverse x ⋆ x) ⋆ y ≡⟨ ap₂ _⋆_ inverseˡ refl ⟩
    unit ⋆ y            ≡⟨ idˡ ⟩
    y                   ∎
```

We then show that this map is a group homomorphism from $G$ to
$\mathrm{Sym}(G)$:

```
Cayley-isHom : isGroupHom G (Sym G-set) Cayley
Cayley-isHom .isGroupHom.pres-⋆ x y = Σ≡Prop isProp-isEquiv (funext lemma) where
  lemma : (e : G .fst) → (x ⋆ y) ⋆ e ≡ x ⋆ (y ⋆ e)
  lemma e = sym associative
```

Finally, we show that this map is injective; Thus, $G$ embeds as a
subgroup of $\mathrm{Sym}(G)$ (the image of `Cayley`{.Agda}).

```
Cayley-injective : injective Cayley
Cayley-injective {x} {y} eqvs-equal =
  x                   ≡⟨ sym idʳ ⟩
  x ⋆ unit            ≡⟨⟩ 
  Cayley x .fst unit  ≡⟨ happly (ap fst eqvs-equal) unit ⟩
  Cayley y .fst unit  ≡⟨⟩
  y ⋆ unit            ≡⟨ idʳ ⟩
  y                   ∎
```