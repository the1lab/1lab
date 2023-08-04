<!--
```agda
open import Cat.Allegory.Base
open import Cat.Prelude

import Cat.Allegory.Reasoning
```
-->

```agda
module Cat.Allegory.Morphism {o ℓ ℓ'} (A : Allegory o ℓ ℓ') where
```

<!--
```agda
open Cat.Allegory.Reasoning A public

private variable
  w x y z : Ob
  a b c f g h : Hom x y
```
-->

# Morphisms in an Allegory

This module defines a couple of important classes of morphisms that can
be found in an allegory.

# Reflexive Morphisms

A morphism $f : X \to X$ in an allegory is **reflexive** if $id \le f$.

```agda
is-reflexive : Hom x x → Type _
is-reflexive f = id ≤ f
```

The composition of two reflexive morphisms is reflexive, and the
identity morphism is trivially reflexive.

```agda
reflexive-id : is-reflexive (id {x})
reflexive-id = ≤-refl

reflexive-∘ : is-reflexive f → is-reflexive g → is-reflexive (f ∘ g)
reflexive-∘ {f = f} {g = g} f-refl g-refl =
  id      =⟨ sym (idl _) ⟩
  id ∘ id ≤⟨ f-refl ◆ g-refl ⟩
  f ∘ g ≤∎
```

The intersection of reflexive morphisms is reflexive.

```agda
reflexive-∩ : is-reflexive f → is-reflexive g → is-reflexive (f ∩ g)
reflexive-∩ f-refl g-refl = ∩-univ f-refl g-refl
```

The dual of a reflexive morphism is also reflexive.

```agda
reflexive-dual : is-reflexive f → is-reflexive (f †)
reflexive-dual {f = f} f-refl =
  dual-≤ᵣ A $
  id † =⟨ dual-id A ⟩
  id   ≤⟨ f-refl ⟩
  f    ≤∎
```

# Symmetric Morphisms

A morphism $f : X \to X$ is **symmetric** if $f \le f^o$.

```agda
is-symmetric : Hom x x → Type _
is-symmetric f = f ≤ f †
```

The identity morphism is trivially symmetric.

```agda
symmetric-id : is-symmetric (id {x})
symmetric-id {x = x} = subst (id {x} ≤_) (sym $ dual-id A) (≤-refl {f = id {x}})
```


The composition of symmetric morphisms $f$ and $g$ is symmetric if
$g \circ f \le f \circ g$.

```agda
symmetric-∘
  : is-symmetric f → is-symmetric g
  → g ∘ f ≤ f ∘ g
  → is-symmetric (f ∘ g)
symmetric-∘ {f = f} {g = g} f-sym g-sym w =
  f ∘ g     ≤⟨ f-sym ◆ g-sym ⟩
  f † ∘ g † =⟨ sym dual-∘ ⟩
  (g ∘ f) † ≤⟨ dual-≤ w ⟩
  (f ∘ g) † ≤∎
```

The dual of a symmetric morphisms is symmetric.

```agda
symmetric-dual : is-symmetric f → is-symmetric (f †)
symmetric-dual {f = f} f-sym = dual-≤ᵣ A $
  f † † =⟨ dual f ⟩
  f     ≤⟨ f-sym ⟩
  f †   ≤∎
```

The intersection of symmetric morphisms is symmetric.

```agda
symmetric-∩ : is-symmetric f → is-symmetric g → is-symmetric (f ∩ g)
symmetric-∩ {f = f} {g = g} f-sym g-sym =
  f ∩ g     ≤⟨ ∩-pres f-sym g-sym ⟩
  f † ∩ g † =⟨ sym $ dual-∩ A ⟩
  (f ∩ g) † ≤∎
```

If $f$ is symmetric, then it is equal to it's dual.

```agda
symmetric→self-dual
  : is-symmetric f → f ≡ f †
symmetric→self-dual f-sym =
  ≤-antisym f-sym (dual-≤ₗ A f-sym)
```

# Transitive Morphisms

A morphism $f : X \to X$ is **transitive** if $f \circ f \le f$.

```agda
is-transitive : Hom x x → Type _
is-transitive f = f ∘ f ≤ f
```

The identity morphism is transitive.

```agda
transitive-id : is-transitive (id {x})
transitive-id = ≤-eliml ≤-refl
```

The composition of two transitive morphisms $f$ and $g$ is transitive
if $g \circ f \le f \circ g$.

```agda
transitive-∘
  : is-transitive f → is-transitive g
  → g ∘ f ≤ f ∘ g
  → is-transitive (f ∘ g)
transitive-∘ {f = f} {g = g} f-trans g-trans w =
  (f ∘ g) ∘ (f ∘ g) ≤⟨ ≤-extend-inner w ⟩
  (f ∘ f) ∘ (g ∘ g)   ≤⟨ f-trans ◆ g-trans ⟩
  f ∘ g             ≤∎
```

A useful little lemma is that if $f$ is transitive, then
$(f \cap g) \circ (f \cap h) = f$.

```agda
transitive-∩l : is-transitive f → (f ∩ g) ∘ (f ∩ h) ≤ f
transitive-∩l f-trans = ≤-trans (∩-le-l ◆ ∩-le-l) f-trans

transitive-∩r : is-transitive h → (f ∩ h) ∘ (g ∩ h) ≤ h
transitive-∩r h-trans = ≤-trans (∩-le-r ◆ ∩-le-r) h-trans
```

We can use these lemmas to show that the intersection of transitive
morphisms is transitive.

```agda
transitive-∩
  : is-transitive f → is-transitive g → is-transitive (f ∩ g)
transitive-∩ {f = f} {g = g} f-trans g-trans =
  ∩-univ (transitive-∩l f-trans) (transitive-∩r g-trans)
```

If $f$ is transitive, then so is it's dual.

```agda
transitive-dual : is-transitive f → is-transitive (f †)
transitive-dual {f = f} f-trans =
  f † ∘ f † =⟨ sym dual-∘ ⟩
  (f ∘ f) † ≤⟨ dual-≤ f-trans ⟩
  f †       ≤∎
```

# Cotransitive Morphisms

A morphism $f : X \to X$ is **cotransitive** if $f \le f \circ f$.

::: warning
**Warning**: There is another notion of cotransitive relation, which
stipulates that for all $x, y, z$, if $R(x,z)$, then either $R(x,y)$
or $R(y,z)$. This is a poor choice of a name, as it is **not** a
transitive relation in $\Rel^{co}$.
:::

```agda
is-cotransitive : Hom x x → Type _
is-cotransitive f = f ≤ f ∘ f
```

The identity morphism is cotransitive.

```agda
cotransitive-id : is-cotransitive (id {x})
cotransitive-id = ≤-introl ≤-refl
```

The composition of two cotransitive morphisms $f$ and $g$ is cotransitive
if $f \circ g \le g \circ f$.

```agda
cotransitive-∘
  : is-cotransitive f → is-cotransitive g
  → f ∘ g ≤ g ∘ f
  → is-cotransitive (f ∘ g)
cotransitive-∘ {f = f} {g = g} f-cotrans g-cotrans w =
  f ∘ g             ≤⟨ f-cotrans ◆ g-cotrans ⟩
  (f ∘ f) ∘ (g ∘ g) ≤⟨ ≤-extend-inner w ⟩
  (f ∘ g) ∘ (f ∘ g) ≤∎
```

If the intersection of $f$ and $g$ is cotransitive, then
$f \cap g \le f \circ g$.

```agda
cotransitive-∩-∘
  : is-cotransitive (f ∩ g)
  → f ∩ g ≤ f ∘ g 
cotransitive-∩-∘ {f = f} {g = g} f∩g-cotrans =
  f ∩ g             ≤⟨ f∩g-cotrans ⟩
  (f ∩ g) ∘ (f ∩ g) ≤⟨ ∩-le-l ◆ ∩-le-r ⟩
  f ∘ g ≤∎
```

If $f$ is reflexive, then it is cotransitive.

```agda
reflexive→cotransitive
  : is-reflexive f → is-cotransitive f
reflexive→cotransitive {f = f} f-refl =
  f      =⟨ sym (idl f) ⟩
  id ∘ f ≤⟨ f-refl ◀ f ⟩
  f ∘ f ≤∎
```

If $f$ is transitive and symmetric, then it is cotransitive.

```agda
transitive+symmetric→cotransitive
  : is-transitive f → is-symmetric f → is-cotransitive f
transitive+symmetric→cotransitive {f = f} f-trans f-sym =
  f           ≤⟨ ≤-conj f ⟩
  f ∘ f † ∘ f ≤⟨ f ▶ dual-≤ₗ A f-sym ◀ f ⟩
  f ∘ f ∘ f   ≤⟨ f ▶ f-trans ⟩
  f ∘ f       ≤∎
```

# Coreflexive Morphisms

```agda
is-coreflexive : Hom x x → Type _
is-coreflexive f = f ≤ id
```

The composition of two coreflexive morphisms is coreflexive, and the
identity morphism is trivially coreflexive.

```agda
coreflexive-∘ : is-coreflexive f → is-coreflexive g → is-coreflexive (f ∘ g)
coreflexive-∘ {f = f} {g = g} f-corefl g-corefl =
  f ∘ g   ≤⟨ f-corefl ◆ g-corefl ⟩
  id ∘ id =⟨ idl _ ⟩
  id      ≤∎

coreflexive-id : is-coreflexive (id {x})
coreflexive-id = ≤-refl
```

Coreflexive morphisms are closed under intersection.

```agda
coreflexive-∩
  : ∀ {x} {f g : Hom x x}
  → is-coreflexive f → is-coreflexive g → is-coreflexive (f ∩ g)
coreflexive-∩ {f = f} {g = g} f-corefl g-corefl =
  f ∩ g   ≤⟨ ∩-pres f-corefl g-corefl ⟩
  id ∩ id =⟨ ∩-idempotent ⟩
  id      ≤∎
```

Coreflexive morphisms are closed under duals.

```agda
coreflexive-dual : is-coreflexive f → is-coreflexive (f †) 
coreflexive-dual {f = f} f-corefl = dual-≤ₗ A $
  f    ≤⟨ f-corefl ⟩
  id   =⟨ sym $ dual-id A ⟩
  id † ≤∎
```

If $f$ is coreflexive, then it is transitive, cotransitive, and symmetric.

```agda
coreflexive→transitive
  : is-coreflexive f → is-transitive f
coreflexive→transitive {f = f} f-corefl =
  f ∘ f  ≤⟨ f-corefl ◀ f ⟩
  id ∘ f =⟨ idl _ ⟩
  f      ≤∎

coreflexive→cotransitive
  : is-coreflexive f → is-cotransitive f
coreflexive→cotransitive {f = f} f-corefl =
  f           ≤⟨ ≤-conj f ⟩
  f ∘ f † ∘ f ≤⟨ f ▶ ≤-eliml (coreflexive-dual f-corefl) ⟩
  f ∘ f       ≤∎

coreflexive→symmetric
  : is-coreflexive f → is-symmetric f
coreflexive→symmetric {f = f} f-corefl =
  f             ≤⟨ ≤-conj f ⟩
  f ∘ f † ∘ f   ≤⟨ f-corefl ◆ ≤-refl ◆ f-corefl ⟩
  id ∘ f † ∘ id =⟨ idl _ ∙ idr _ ⟩
  f † ≤∎
```
Furthermore, composition of coreflexive morphisms is equivalent to
intersection.

```agda
coreflexive-∘-∩
  : ∀ {x} {f g : Hom x x}
  → is-coreflexive f → is-coreflexive g
  → f ∘ g ≡ f ∩ g
coreflexive-∘-∩ {f = f} {g = g} f-corefl g-corefl =
  ≤-antisym ≤-to ≤-from
  where
    ≤-to : f ∘ g ≤ f ∩ g
    ≤-to = ∩-univ (≤-elimr g-corefl) (≤-eliml f-corefl)

    ≤-from : f ∩ g ≤ f ∘ g
    ≤-from =
      cotransitive-∩-∘ $
      coreflexive→cotransitive $
      coreflexive-∩ f-corefl g-corefl
```
