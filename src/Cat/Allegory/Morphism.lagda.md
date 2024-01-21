<!--
```agda
open import Cat.Allegory.Base
open import Cat.Prelude

import Cat.Allegory.Reasoning
import Cat.Diagram.Idempotent
```
-->

```agda
module Cat.Allegory.Morphism {o ℓ ℓ'} (A : Allegory o ℓ ℓ') where
```

<!--
```agda
open Cat.Allegory.Reasoning A public
open Cat.Diagram.Idempotent cat public

private variable
  w x y z : Ob
  a b c f g h : Hom x y
```
-->

# Morphisms in an allegory

This module defines a couple of important classes of morphisms that can
be found in an allegory.

# Reflexive morphisms

A morphism $f : X \to X$ in an allegory is **reflexive** if $\id \le f$.

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

If $f \le g$ and $f$ is reflexive, then $g$ is reflexive.

```agda
reflexive-≤ : f ≤ g → is-reflexive f → is-reflexive g
reflexive-≤ w f-refl = ≤-trans f-refl w
```

If $f$ is reflexive, then $\id \le f \cap f^o$.

```agda
reflexive→diagonal
  : is-reflexive f → id ≤ f ∩ f †
reflexive→diagonal f-refl = ∩-univ f-refl (reflexive-dual f-refl)
```


# Symmetric morphisms

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
$gf \le fg$.

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

The dual of a symmetric morphism is symmetric.

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

If $f$ is symmetric, then it is equal to its dual.

```agda
symmetric→self-dual
  : is-symmetric f → f ≡ f †
symmetric→self-dual f-sym =
  ≤-antisym f-sym (dual-≤ₗ A f-sym)
```

# Transitive morphisms

A morphism $f : X \to X$ is **transitive** if $ff \le f$.

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
if $gf \le fg$.

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
$(f \cap g)(f \cap h) \le f$.

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

If $f$ is transitive, then so is its dual.

```agda
transitive-dual : is-transitive f → is-transitive (f †)
transitive-dual {f = f} f-trans =
  f † ∘ f † =⟨ sym dual-∘ ⟩
  (f ∘ f) † ≤⟨ dual-≤ f-trans ⟩
  f †       ≤∎
```

# Cotransitive morphisms

A morphism $f : X \to X$ is **cotransitive** if $f \le ff$.

::: warning
There is another notion of cotransitive relation, which stipulates that
for all $x, y, z$, if $R(x,z)$, then either $R(x,y)$ or $R(y,z)$. This
is a poor choice of a name, as it is **not** a transitive relation in
$\Rel^{co}$.

Other sources call cotransitive morphisms "symmetric idempotents",
though we avoid this terminology, as cotranstive morphisms are not
symmetric.
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
if $fg \le gf$.

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
$f \cap g \le fg$.

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

# Coreflexive morphisms

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

If $f \le g$ and $g$ is coreflexive, then $f$ is coreflexive.

```agda
coreflexive-≤ : f ≤ g → is-coreflexive g → is-coreflexive f
coreflexive-≤ w g-corefl = ≤-trans w g-corefl
```

If $f$ is coreflexive, then it is transitive, cotransitive, and symmetric.
Coreflexive morphisms are also anti-symmetric, see `coreflexive→antisymmetric`{.Agda}.

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

As coreflexive morphisms are both transitive ($ff \le f$) and
cotransitive ($f \le ff$), they are idempotent.

```agda
coreflexive→idempotent : is-coreflexive f → is-idempotent f
coreflexive→idempotent f-corefl =
  ≤-antisym (coreflexive→transitive f-corefl) (coreflexive→cotransitive f-corefl)
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

This has a useful corollary: coreflexive morphisms always commute!

```agda
coreflexive-comm
  : ∀ {x} {f g : Hom x x}
  → is-coreflexive f → is-coreflexive g
  → f ∘ g ≡ g ∘ f
coreflexive-comm f-corefl g-corefl =
  coreflexive-∘-∩ f-corefl g-corefl
  ·· ∩-comm
  ·· sym (coreflexive-∘-∩ g-corefl f-corefl)
```

# Functional morphisms

A morphism $f$ is **functional** when $ff^o \le \id$. In $\Rel$, these
are the relations $R \mono X \times Y$ such that every $x$ is related to
at most one $y$. To see this, note that $RR^o(y,y')$ is defined as
$\exists (x : X). R(x,y) \times R(x,y')$. Therefore,
$RR^o(y,y') \subseteq y = y'$ means that if there exists any $x$ such that
$R(x,y)$ and $R(x,y')$, then $y$ and $y'$ must be equal. Put more plainly,
every $x$ is related to at most one $y$!

```agda
is-functional : Hom x y → Type _
is-functional f = f ∘ f † ≤ id
```

First, a useful lemma: coreflexive morphisms are always functional.

```agda
coreflexive→functional : is-coreflexive f → is-functional f
coreflexive→functional f-corefl =
  coreflexive-∘ f-corefl (coreflexive-dual f-corefl)
```

This immediately implies that the identity morphism is functional.

```agda
functional-id : is-functional (id {x})
functional-id = coreflexive→functional coreflexive-id
```

Functional morphisms are closed under composition and intersection.

```agda
functional-∘ : is-functional f → is-functional g → is-functional (f ∘ g)
functional-∘ {f = f} {g = g} f-func g-func =
  (f ∘ g) ∘ (f ∘ g) † ≤⟨ †-cancel-inner g-func ⟩
  f ∘ f †             ≤⟨ f-func ⟩
  id                  ≤∎

functional-∩ : is-functional f → is-functional g → is-functional (f ∩ g)
functional-∩ {f = f} {g = g} f-func g-func =
  (f ∩ g) ∘ (f ∩ g) †                       =⟨ ap ((f ∩ g) ∘_) (dual-∩ A) ⟩
  (f ∩ g) ∘ (f † ∩ g †)                     ≤⟨ ∩-distrib ⟩
  (f ∘ f † ∩ g ∘ f †) ∩ (f ∘ g † ∩ g ∘ g †) ≤⟨ ∩-pres ∩-le-l ∩-le-r ⟩
  f ∘ f † ∩ g ∘ g †                         ≤⟨ ∩-pres f-func g-func ⟩
  id ∩ id                                   =⟨ ∩-idempotent ⟩
  id                                        ≤∎
```

# Entire morphisms

A morphism is **entire** when $\id \le f^of$. In $\Rel$, these are the
relations $R \mono X \times Y$ where each $x$ must be related to at least
one $y$. To see this, recall that $R^oR(x,x')$ is defined as
$\exists (y : Y). R(x,y) \times R(x',y)$. If $x = x' \subseteq R^oR(x,x')$,
then we can reduce this statement down to $\forall (x : X). \exists (y : Y). R(x,y)$.


```agda
is-entire : Hom x y → Type _
is-entire f = id ≤ f † ∘ f
```

Reflexive morphisms are always entire.

```agda
reflexive→entire : is-reflexive f → is-entire f
reflexive→entire f-refl =
  reflexive-∘ (reflexive-dual f-refl) f-refl
```

From this, we can deduce that the identity morphism is entire.

```agda
entire-id : is-entire (id {x})
entire-id = reflexive→entire reflexive-id
```

Entire morphisms are closed under composition.

```agda
entire-∘ : is-entire f → is-entire g → is-entire (f ∘ g)
entire-∘ {f = f} {g = g} f-entire g-entire =
  id                  ≤⟨ g-entire ⟩
  g † ∘ g             ≤⟨ g † ▶ ≤-introl f-entire ⟩
  g † ∘ (f † ∘ f) ∘ g =⟨ extendl (pulll (sym dual-∘)) ⟩
  (f ∘ g) † ∘ (f ∘ g) ≤∎
```

# Domains

The domain of a morphism $f : X \to Y$ is defined as
$\id \cap (f^of)$, denoted $\rm{dom}(f)$.
In $\Rel$, the domain of a relation $R : X \times Y \to \Omega$ is a
relation $X \times X \to \Omega$ that relates two elements $x, x' : X$
whenever $x = x'$, and $R(x,y)$ for some $y$.

```agda
domain : Hom x y → Hom x x
domain f = id ∩ f † ∘ f
```

The domain of a morphism is always coreflexive.

```agda
domain-coreflexive : ∀ (f : Hom x y) → is-coreflexive (domain f)
domain-coreflexive f = ∩-le-l
```

<!--
```agda
domain-elimr : f ∘ domain g ≤ f
domain-elimr = ≤-elimr (domain-coreflexive _)

domain-eliml : domain f ∘ g ≤ g
domain-eliml = ≤-eliml (domain-coreflexive _)

domain-idempotent : is-idempotent (domain f)
domain-idempotent = coreflexive→idempotent (domain-coreflexive _)

domain-dual : domain f † ≡ domain f
domain-dual = sym (symmetric→self-dual (coreflexive→symmetric (domain-coreflexive _)))

domain-comm : domain f ∘ domain g ≡ domain g ∘ domain f
domain-comm = coreflexive-comm (domain-coreflexive _) (domain-coreflexive _)
```
-->

Furthermore, the domain enjoys the following universal property:
Let $f : X \to Y$ and $g : X \to X$ such that $g$ is coreflexive.
Then $\rm{dom}(f) \le g$ if and only if $f \le fg$.

```agda
domain-universalr : is-coreflexive g → domain f ≤ g → f ≤ f ∘ g
domain-universalr {g = g} {f = f} g-corefl w =
  f                  ≤⟨ ∩-univ (≤-intror ≤-refl) ≤-refl ⟩
  (f ∘ id) ∩ f       ≤⟨ modular id f f ⟩
  f ∘ (id ∩ f † ∘ f) ≤⟨ f ▶ w ⟩
  f ∘ g              ≤∎

domain-universall : is-coreflexive g → f ≤ f ∘ g → domain f ≤ g
domain-universall {g = g} {f = f} g-corefl w =
  id ∩ (f † ∘ f)           ≤⟨ ∩-pres-r (≤-pushr w) ⟩
  id ∩ ((f † ∘ f) ∘ g)     =⟨ ∩-comm ⟩
  ((f † ∘ f) ∘ g) ∩ id     ≤⟨ modular' g (f † ∘ f) id ⟩
  (f † ∘ f ∩ id ∘ g †) ∘ g ≤⟨ ≤-trans ∩-le-r (≤-eliml ≤-refl) ◀ g ⟩
  g † ∘ g                  ≤⟨ ≤-eliml (coreflexive-dual g-corefl) ⟩
  g                        ≤∎
```

This has a nice corollary: $f\rm{dom}(f) = f$.

```agda
domain-absorb : ∀ (f : Hom x y) → f ∘ domain f ≡ f
domain-absorb f =
  ≤-antisym
    domain-elimr
    (domain-universalr (domain-coreflexive f) ≤-refl)
```

We can nicely characterize the domain of an intersection.

```agda
domain-∩ : domain (f ∩ g) ≡ id ∩ f † ∘ g
domain-∩ {f = f} {g = g} = ≤-antisym ≤-to ≤-from where
  ≤-to : domain (f ∩ g) ≤ id ∩ f † ∘ g
  ≤-to =
    ∩-univ
      (domain-coreflexive (f ∩ g))
      (≤-trans ∩-le-r (dual-≤ ∩-le-l ◆ ∩-le-r))

  ≤-from : id ∩ f † ∘ g ≤ domain (f ∩ g)
  ≤-from =
    id ∩ f † ∘ g                               ≤⟨ ∩-univ ∩-le-l (∩-univ (∩-univ ∩-le-r ∩-le-l) ∩-le-l ) ⟩
    id ∩ (f † ∘ g ∩ id) ∩ id                   ≤⟨ ∩-pres-r (∩-pres-l (modular g (f †) id)) ⟩
    id ∩ (f † ∘ (g ∩ ⌜ f † † ∘ id ⌝)) ∩ id     =⟨ ap! (idr _ ∙ dual f) ⟩
    id ∩ (f † ∘ (g ∩ f)) ∩ id                  ≤⟨ ∩-pres-r (modular' (g ∩ f) (f †) id) ⟩
    id ∩ (f † ∩ ⌜ id ∘ (g ∩ f) † ⌝) ∘ (g ∩ f)  =⟨ ap! (idl _) ⟩
    id ∩ (f † ∩ ⌜ g ∩ f ⌝ †) ∘ ⌜ g ∩ f ⌝       =⟨ ap! ∩-comm ⟩
    id ∩ (f † ∩ (f ∩ g) †) ∘ (f ∩ g)           ≤⟨ ∩-pres-r (∩-le-r ◀ (f ∩ g)) ⟩
    id ∩ (f ∩ g) † ∘ (f ∩ g)                   ≤∎
```

Furthermore, the domain of $fg$ is contained in the domain of $g$.

```agda
domain-∘ : domain (f ∘ g) ≤ domain g
domain-∘ {f = f} {g = g} =
  domain-universall (domain-coreflexive g) $
  ≤-pushr (domain-universalr (domain-coreflexive g) ≤-refl)
```

If $f \le g$, then $\rm{dom}(f) \le \rm{dom}(g)$.

```agda
domain-≤ : f ≤ g → domain f ≤ domain g
domain-≤ w = ∩-pres-r (dual-≤ w ◆ w)
```

The domain of the identity morphism is simply the identity morphism.

```agda
domain-id : domain (id {x}) ≡ id
domain-id = ≤-antisym ∩-le-l (∩-univ ≤-refl (≤-introl symmetric-id))
```

Characterizing composition of domains is somewhat more difficult,
though it is possible. Namely, we shall show the following:

$$\rm{dom}(f\rm{dom}(g)) = \rm{dom}(f)\rm{dom}(g)$$

```agda
domain-smashr
  : ∀ (f : Hom x z) (g : Hom x y)
  → domain (f ∘ domain g) ≡ domain f ∘ domain g
domain-smashr f g = ≤-antisym ≤-to ≤-from where
```

We begin by noting that the composition $\rm{dom}(f)\rm{dom}(g)$
is coreflexive.

```agda
  fg-corefl : is-coreflexive (domain f ∘ domain g)
  fg-corefl = coreflexive-∘ (domain-coreflexive f) (domain-coreflexive g)
```

To show the forward direction, we can apply the universal property of
domains to transform the goal into

$$f\rm{dom}(g) \le (f\rm{dom}(g))(\rm{dom}(f)\rm{dom}(g))$$

We can then solve this goal by repeatedly appealing to the fact that
domains are coreflexive.

```agda
  ≤-to : domain (f ∘ domain g) ≤ domain f ∘ domain g
  ≤-to =
    domain-universall fg-corefl $
    f ∘ domain g                           =˘⟨ ap₂ _∘_ (domain-absorb f) domain-idempotent ⟩
    (f ∘ domain f) ∘ (domain g ∘ domain g) =⟨ extendl (extendr domain-comm) ⟩
    (f ∘ domain g) ∘ (domain f ∘ domain g) ≤∎
```

To show the reverse direction, we apply the universal property of the
intersection, reducing the goal to

$$\rm{dom}(f)\rm{dom}(g) \le (f\rm{dom}(g))^of\rm{dom}(g)$$

We then solve the goal by an extended series of appeals to the
coreflexivity of domains.

```agda
  ≤-from : domain f ∘ domain g ≤ domain (f ∘ domain g)
  ≤-from = ∩-univ fg-corefl $
    domain f ∘ domain g               =˘⟨ ap (domain f ∘_) domain-idempotent ⟩
    domain f ∘ domain g ∘ domain g    =⟨ extendl domain-comm ⟩
    domain g ∘ domain f ∘ domain g    =⟨ ap (_∘ domain f ∘ domain g) (sym domain-dual) ⟩
    domain g † ∘ domain f ∘ domain g  ≤⟨ domain g † ▶ ∩-le-r ◀ domain g ⟩
    domain g † ∘ (f † ∘ f) ∘ domain g =⟨ extendl (pulll (sym dual-∘)) ⟩
    (f ∘ domain g) † ∘ f ∘ domain g   ≤∎
```

We can also characterize postcomposition by a domain, though this
is restricted to an inequality in the general case.

```agda
domain-swapl
  : ∀ (f : Hom y z) (g : Hom x y)
  → domain f ∘ g ≤ g ∘ domain (f ∘ g)
domain-swapl f g =
  (id ∩ (f † ∘ f)) ∘ g             ≤⟨ ∩-distribr ⟩
  (id ∘ g ∩ (f † ∘ f) ∘ g)         =⟨ ap₂ _∩_ id-comm-sym (sym (assoc (f †) f g)) ⟩
  (g ∘ id ∩ f † ∘ f ∘ g)           ≤⟨ modular id g (f † ∘ f ∘ g) ⟩
  g ∘ (id ∩ ⌜ g † ∘ f † ∘ f ∘ g ⌝) =⟨ ap! (pulll (sym dual-∘)) ⟩
  g ∘ (id ∩ (f ∘ g) † ∘ (f ∘ g))   ≤∎
```

We can strengthen this to an equality when $g$ is functional.

```agda
domain-swap
  : ∀ (f : Hom y z) (g : Hom x y)
  → is-functional g
  → domain f ∘ g ≡ g ∘ domain (f ∘ g)
domain-swap f g w =
  ≤-antisym (domain-swapl f g) $
  g ∘ (id ∩ (f ∘ g) † ∘ (f ∘ g))   ≤⟨ ∩-distribl ⟩
  g ∘ id ∩ g ∘ (f ∘ g) † ∘ (f ∘ g) ≤⟨ ∩-pres-r (≤-extendl (†-pulll w)) ⟩
  g ∘ id ∩ id ∘ f † ∘ f ∘ g        =⟨ ap₂ _∩_ id-comm (idl _) ⟩
  id ∘ g ∩ f † ∘ f ∘ g             ≤⟨ modular' g id (f † ∘ f ∘ g) ⟩
  (id ∩ (f † ∘ f ∘ g) ∘ g †) ∘ g   ≤⟨ ∩-pres-r (≤-pullr (≤-cancelr w)) ◀ g ⟩
  (id ∩ f † ∘ f) ∘ g ≤∎
```

We also note that domains are always functional.

```agda
domain-functional : (f : Hom x y) → is-functional (domain f)
domain-functional f = coreflexive→functional (domain-coreflexive f)
```

The domain of an entire morphism is the identity.

```agda
domain-entire : is-entire f → domain f ≡ id
domain-entire f-entire =
  ≤-antisym
    (domain-coreflexive _)
    (∩-univ ≤-refl f-entire)
```

# Antisymmetric morphisms

A morphism is **anti-symmetric** if $f \cap f^o \le \id$.

```agda
is-antisymmetric : Hom x x → Type _
is-antisymmetric f = f ∩ f † ≤ id
```

Identity morphisms are anti-symmetric.

```agda
antisymmetric-id
  : is-antisymmetric (id {x})
antisymmetric-id =
  id ∩ ⌜ id † ⌝ =⟨ ap! (dual-id A) ⟩
  id ∩ id       =⟨ ∩-idempotent ⟩
  id            ≤∎
```

If $f \le g$ and $g$ is anti-symmetric, then $f$ is anti-symmetric.

```agda
antisymmetric-≤
  : f ≤ g → is-antisymmetric g → is-antisymmetric f
antisymmetric-≤ {f = f} {g = g} w g-antisym =
  f ∩ f † ≤⟨ ∩-pres w (dual-≤ w) ⟩
  g ∩ g † ≤⟨ g-antisym ⟩
  id      ≤∎
```

If $f$ is anti-symmetric and reflexive, then $f \cap f^o = \id$.

```agda
reflexive+antisymmetric→diagonal
  : is-reflexive f → is-antisymmetric f → f ∩ f † ≡ id
reflexive+antisymmetric→diagonal f-refl f-antisym =
  ≤-antisym f-antisym (reflexive→diagonal f-refl)
```

If $f$ is coreflexive, then it is anti-symmetric.

```agda
coreflexive→antisymmetric : is-coreflexive f → is-antisymmetric f
coreflexive→antisymmetric {f = f} f-corefl =
  f ∩ f † ≤⟨ ∩-pres f-corefl (coreflexive-dual f-corefl) ⟩
  id ∩ id =⟨ ∩-idempotent ⟩
  id ≤∎
```
