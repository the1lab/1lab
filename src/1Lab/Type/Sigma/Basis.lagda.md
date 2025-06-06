---
description: |
  Σ-bases.
---
<!--
```agda
open import 1Lab.Path.IdentitySystem
open import 1Lab.Function.Embedding
open import 1Lab.HLevel.Closure
open import 1Lab.Type.Sigma
open import 1Lab.Type.Pi
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
```
-->
```agda
module 1Lab.Type.Sigma.Basis where
```

# Σ-bases of types

Like most type formers, $\Sigma$ types have a [[universal property|universal-property-of-sigma-types]]:
for every pair of functions $f : X \to A$, $g : (x : A) \to B~ (f x)$,
there is a unique universal map $\langle f , g \rangle : X \to \Sigma~ A~ B$
that commutes with first and second projections. In other words, a $\Sigma$
type is the universal type equipped with a pair of projections $\pi_1 : \Sigma~ A ~ B \to A$,
$\pi_2 : (ab : \Sigma~ A~ B) \to B~ (\pi_1~ ab)$.

This means that "being a $\Sigma$ type" is a **property** of a type $X$
equipped with a pair of functions $p_1 : X \to A$, $p_2 : (x : X) \to B~ (p_1~ x)$.
This leads us to the following notion.

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  T A A' X X' Y Y' Z Z' : Type ℓ
  B P Q : A → Type ℓ
  p₁ : X → A
  p₂ : (x : X) → B (p₁ x)
```
-->

:::{.definition #is-sigma-basis}
A pair of functions $p_1 : X \to A$, $p_2 : (x : X) \to B~ (p_1~ x)$
**form a $\Sigma$-basis** of $X$ when the induced map $\langle p_1, p_2 \rangle : X \to \Sigma~ A~ B$
is an [[equivalence]].
:::

```agda
record is-Σ-basis
  {ℓa ℓb ℓx}
  (X : Type ℓx)
  (A : Type ℓa) (B : A → Type ℓb)
  (p₁ : X → A) (p₂ : (x : X) → B (p₁ x))
  : Type (ℓa ⊔ ℓb ⊔ ℓx) where
  field
    ⟨⟩-equiv : is-equiv {B = Σ A B} ⟨ p₁ , p₂ ⟩
```

The intuition behind the name "basis" is that a choice of $\Sigma$-basis
of $X$ allows us to write elements of $X$ as a sum of elements of $B(a)$.

```agda
  basis : X ≃ Σ A B
  basis = _ , ⟨⟩-equiv

  module basis = Equiv basis
```

:::{.definition #sigma-basis}
Likewise, an **$(A,B)$ $\Sigma$-basis** of $X$ consists of a pair of
maps $p_1 : X \to A, p_2 : (x : X) \to B~ (p_1~ x)$ that form
a $\Sigma$-basis of $X$.
:::


```agda
record Σ-basis
  {ℓa ℓb ℓx}
  (X : Type ℓx)
  (A : Type ℓa) (B : A → Type ℓb)
  : Type (ℓa ⊔ ℓb ⊔ ℓx) where
  field
    proj₁ : X → A
    proj₂ : (x : X) → B (proj₁ x)
    has-basis : is-Σ-basis X A B proj₁ proj₂

  open is-Σ-basis has-basis public
```

Note that we could have equivalently defined $\Sigma$-bases in terms
of a single map $X \to \Sigma~ A~ B$.

```agda
is-equiv→is-Σ-basis
  : ∀ {f : X → Σ A B}
  → is-equiv f
  → is-Σ-basis X A B (fst ∘ f) (snd ∘ f)
is-equiv→is-Σ-basis eqv .is-Σ-basis.⟨⟩-equiv .is-eqv ab = eqv .is-eqv ab

Equiv→Σ-basis
  : X ≃ Σ A B
  → Σ-basis X A B
Equiv→Σ-basis f .Σ-basis.proj₁ x = fst (Equiv.to f x)
Equiv→Σ-basis f .Σ-basis.proj₂ x = snd (Equiv.to f x)
Equiv→Σ-basis f .Σ-basis.has-basis = is-equiv→is-Σ-basis (f .snd)
```

<!--
```agda
is-iso→is-Σ-basis
  : {p₁ : X → A} {p₂ : (x : X) → B (p₁ x)}
  → is-iso {B = Σ A B} ⟨ p₁ , p₂ ⟩
  → is-Σ-basis X A B p₁ p₂
is-iso→is-Σ-basis isom .is-Σ-basis.⟨⟩-equiv = is-iso→is-equiv isom

is-Σ-basis→Σ-basis
  : {p₁ : X → A} {p₂ : (x : X) → B (p₁ x)}
  → is-Σ-basis X A B p₁ p₂
  → Σ-basis X A B
is-Σ-basis→Σ-basis p₁-p₂-basis = record { has-basis = p₁-p₂-basis }
{-# INLINE is-Σ-basis→Σ-basis #-}

Iso→Σ-basis
  : Iso X (Σ A B)
  → Σ-basis X A B
Iso→Σ-basis f = Equiv→Σ-basis (Iso→Equiv f)
{-# INLINE Iso→Σ-basis #-}
```
-->


## Examples of Σ-bases

<!--
```agda
module _ where
  open is-Σ-basis
```
-->

The first and second projections out of $\Sigma~ A~ B$ form an $(A,B)$
$\Sigma$-basis.

```agda
  fst-snd-is-Σ-basis : is-Σ-basis (Σ A B) A B fst snd
  fst-snd-is-Σ-basis .⟨⟩-equiv = id-equiv
```

More interestingly, if $p_1 : X \to A, p_2 : (x : X) \to B~ (p_1~ x)$
form a $\Sigma$-basis of $X$, then $\rm{ap}~ p_1$
and $\rm{ap}~ p_2$ form a $\Sigma$-basis for the path space of $X$.

```agda
  ap-is-Σ-basis
    : {p₁ : X → A} {p₂ : (x : X) → B (p₁ x)}
    → ∀ {x y : X}
    → is-Σ-basis X A B p₁ p₂
    → is-Σ-basis (x ≡ y) (p₁ x ≡ p₁ y) (λ p → PathP (λ i → B (p i)) (p₂ x) (p₂ y))
        (ap p₁)
        (ap p₂)
```

The proof is a nice equivalence chase. Our ultimate goal is to show that
$$\langle \rm{ap}~ p_1, \rm{ap}~ p_2 \rangle : \Path{X}{x}{y} \to \Path{\Sigma~ A~ B}{p_1~ x , p_2~ x}{p_1~ y, p_2~ y}$$
is an equivalence. However, we know that paths in $\Sigma$ types are
equivalent to pairs of paths, so we can use 2-for-3 for equivalences
to reduce the problem to showing that
$$\rm{ap}~ \langle p_1 , p_2 \rangle : \Path{X}{x}{y} \to \Sigma~ (p : \Path{A}{p_1~ x}{p_1~ y})~ \PathP{\lambda i~ B~ (p~ i)}{p_2~ x}{p_2~ y}$$
is an equivalence. This just is another way of asking that $\langle p_1 , p_2 \rangle$
is an [[embedding]], and every equivalence is an embedding!

```agda
  ap-is-Σ-basis {p₁ = p₁} {p₂ = p₂} {x = x} {y = y} ΣX .⟨⟩-equiv =
    is-equiv ⟨ ap p₁ , ap p₂ ⟩ ←⟨ equiv-cancell (Σ-pathp≃ .snd) ⟩
    is-equiv (ap ⟨ p₁ , p₂ ⟩)  ←⟨ equiv→cancellable ⟩
    is-equiv ⟨ p₁ , p₂ ⟩       ←⟨ ΣX .⟨⟩-equiv ⟩∎
```

We can also lift $\Sigma$-bases to function types: if
$p_1 : Y \to A, p_2 : (y : Y) \to B~ (p_1~ y)$ form a $\Sigma$-basis for $Y$,
then $p_1 \circ (-) : (X \to Y) \to (X \to Y)$ and $p_2 \circ (-) : (f : X \to Y) \to (X \to B~ (f~ x))$
form a $\Sigma$-basis for $X \to Y$.

```agda
  postcompose-is-Σ-basis
    : {p₁ : Y → A} {p₂ : (y : Y) → B (p₁ y)}
    → is-Σ-basis Y A B p₁ p₂
    → is-Σ-basis (X → Y) (X → A) (λ f → (x : X) → B (f x)) (p₁ ∘_) (p₂ ∘_)
```

This follows a similar line of reasoning as the previous proof.
We start by using 2-for-3 for equivalences to distribute the postcomposition
out of the universal map. Next, precomposition by an equivalence is
itself an equivalence, so it suffices to show that $\langle p_1 , p_2 \rangle$
is an equivalence, which is exactly our hypothesis.

```agda
  postcompose-is-Σ-basis {Y = Y} {A = A} {B = B} {X = X} {p₁ = p₁} {p₂ = p₂} ΣY .⟨⟩-equiv =
    is-equiv ⟨ p₁ ∘_ , p₂ ∘_ ⟩ ←⟨ equiv-cancell (inverse-is-equiv (Σ-Π-distrib .snd)) ⟩
    is-equiv (⟨ p₁ , p₂ ⟩ ∘_)  ←⟨ precompose-is-equiv ⟩
    is-equiv ⟨ p₁ , p₂ ⟩       ←⟨ ΣY .⟨⟩-equiv ⟩∎
```


## Combining Σ-bases

The following series of lemmas describe various ways we can combine
$\Sigma$-bases.

<!--
```agda
module _
  {ℓx ℓp ℓa ℓb ℓc ℓd}
  {X : Type ℓx} {P : X → Type ℓp}
  {A : Type ℓa} {B : A → Type ℓb}
  {C : (a : A) → Type ℓc} {D : (a : A) → B a → C a → Type ℓd}
  where
  open Σ-basis
```
-->

If $X : \ty$ has a $(A, B)$ $\Sigma$-basis, and $P : X \to \ty$
has a $(C~ (p_1~ x), D~ (p_1~ x))$ $\Sigma$-basis for every $x : X$, then
$\Sigma X P$ can be equipped with a $(a, c) : \Sigma A C, B~a \times D~ a~ c$ $\Sigma$
basis.

```agda
  Σ-basis-swap₂
    : (ΣX : Σ-basis X A B)
    → (ΣP : ∀ x → Σ-basis (P x) (C (ΣX .proj₁ x)) (D (ΣX .proj₁ x) (ΣX .proj₂ x)))
    → Σ-basis (Σ X P) (Σ A C) (λ ac → Σ[ b ∈ B (ac .fst) ] D (ac .fst) b (ac .snd))
```

The key here is that the $\Sigma$ basis of $P~ x$ is only allowed depend on the
first component of the $\Sigma$-basis of $X$, so we can commute the $B~ a$
and $C~ a$ components of the iterated $\Sigma$ type we get after expanding
out $\Sigma X P$.

```agda
  Σ-basis-swap₂ ΣX ΣP =
    Equiv→Σ-basis $
      Σ X P                                        ≃⟨ Σ-ap (basis ΣX) (λ x → basis (ΣP x)) ⟩
      Σ[ (a , b) ∈ Σ A B ] Σ[ c ∈ C a ] D a b c    ≃˘⟨ Σ-assoc ⟩
      Σ[ a ∈ A ] Σ[ b ∈ B a ] Σ[ c ∈ C a ] D a b c ≃⟨ Σ-ap-snd (λ a → Σ-swap₂) ⟩
      Σ[ a ∈ A ] Σ[ c ∈ C a ] Σ[ b ∈ B a ] D a b c ≃⟨ Σ-assoc ⟩
      Σ[ (a , c) ∈ Σ A C ] Σ[ b ∈ B a ] D a b c    ≃∎
```

<!--
```agda
module _
  {ℓx ℓa ℓb ℓy ℓc ℓd ℓz ℓe ℓf}
  {X : Type ℓx} {A : Type ℓa} {B : A → Type ℓb}
  {Y : Type ℓy} {C : Type ℓc} {D : C → Type ℓd}
  {Z : Y → Type ℓz} {E : (c : C) → Type ℓe} {F : (c : C) → D c → E c → Type ℓf}
  where
  open Σ-basis
```
-->

Our previous lemma gives us a useful technique for constructing $\Sigma$-bases.
To show that $X$ has a $(Y,Z)$ $\Sigma$-basis, it suffices to show that:

- $X$ has a $(A, B)$ basis; and
- $Y$ has a $(C ,E)$ basis; and
- For every $y : Y$, $Z~ y$ has a $(d : D~ (p_1~ y), F~ (p_1~ y)~ d~ (p_2~y ))$ basis; and
- $A$ has a $(C, D)$ basis; and finally
- for every $a : A$, $B~ a$ has a $(e : E~ a, F~ (p_1~ a)~ (p_2~ a)~ e)$.

This is particularly useful for constructing $\Sigma$-bases of record
types whose first and second components are also record types: the first
three $\Sigma$ bases for $X$, $Y$, and $Z$ let us give decompositions of
record types into $\Sigma$ types, and the final two $\Sigma$ bases let
us re-arrange the components of those decompositions back into place.

```agda
  Σ-basis-shuffle
     : (ΣX : Σ-basis X A B)
     → (ΣY : Σ-basis Y C E)
     → (ΣZ : ∀ {y} → Σ-basis (Z y) (D (ΣY .proj₁ y)) (λ d → F (ΣY .proj₁ y) d (ΣY .proj₂ y)))
     → (ΣA : Σ-basis A C D)
     → (ΣB : ∀ {a} → Σ-basis (B a) (E (ΣA .proj₁ a)) λ e → F (ΣA .proj₁ a) (ΣA .proj₂ a) e)
     → Σ-basis X Y Z
  Σ-basis-shuffle ΣX ΣY ΣZ ΣA ΣB =
    Equiv→Σ-basis $
      X                                         ≃⟨ basis ΣX ⟩
      Σ A B                                     ≃⟨ basis (Σ-basis-swap₂ ΣA (λ a → ΣB)) ⟩
      Σ[ (c , e) ∈ Σ C E ] Σ[ d ∈ D c ] F c d e ≃˘⟨ Σ-ap (basis ΣY) (λ _ → basis ΣZ) ⟩
      Σ Y Z                                     ≃∎
```

<!--
```agda
-- Bundled forms of is-Σ-basis results.
module _ where
  open Σ-basis

  Path-Σ-basis
    : {x y : X}
    → (ΣX : Σ-basis X A B)
    → Σ-basis (x ≡ y)
        (ΣX .proj₁ x ≡ ΣX .proj₁ y)
        (λ p → PathP (λ i → B (p i)) (ΣX .proj₂ x) (ΣX .proj₂ y))
  Path-Σ-basis ΣX = is-Σ-basis→Σ-basis (ap-is-Σ-basis (ΣX .has-basis))
  {-# INLINE Path-Σ-basis #-}
```
-->

## Σ-bases and identity systems

Every $\Sigma$-basis for a type induces an identity system on $X$.

```agda
is-Σ-basis→identity-system
  : {p₁ : X → A} {p₂ : (x : X) → B (p₁ x)}
  → is-Σ-basis X A B p₁ p₂
  → is-identity-system
      (λ x y → Σ[ p ∈ p₁ x ≡ p₁ y ] PathP (λ i → B (p i)) (p₂ x) (p₂ y))
      (λ x → refl , refl)
is-Σ-basis→identity-system {p₁ = p₁} {p₂ = p₂} ΣX =
  equiv-path→identity-system $
  (⟨ ap p₁ , ap p₂ ⟩ , ap-is-Σ-basis ΣX .is-Σ-basis.⟨⟩-equiv) e⁻¹
```

## Reasoning

```agda
module _ {ℓx ℓa ℓb} {X : Type ℓx} {A : Type ℓa} {B : A → Type ℓb} where
  open Σ-basis

  record Σ-basis-path (ΣX : Σ-basis X A B) {a a' : A} (b : B a) (b' : B a') : Type ℓx where
    no-eta-equality
    field
      path : basis.from ΣX (a , b) ≡ basis.from ΣX (a' , b')

    base : a ≡ a'
    base = ap fst $ Equiv.injective (basis ΣX e⁻¹) path

    over : PathP (λ i → B (base i)) b b'
    over = ap snd $ Equiv.injective (basis ΣX e⁻¹) path

  open Σ-basis-path

  via-Σ-basis
    : {a a' : A} {b : B a} {b' : B a'}
    → (ΣX : Σ-basis X A B)
    → (p : Σ-basis-path ΣX b b')
    → PathP (λ i → B (base p i)) b b'
  via-Σ-basis ΣX p = over p

  Σ-basis-path-step
    : {ΣX : Σ-basis X A B}
    → ∀ {a a' a''} {b' : B a'} {b'' : B a''}
    → (b : B a)
    → Σ-basis-path ΣX b' b''
    → basis.from ΣX (a , b) ≡ basis.from ΣX (a' , b')
    → Σ-basis-path ΣX b b''
  Σ-basis-path-step {ΣX = ΣX} b q p .Σ-basis-path.path = p ∙ q .path

  _∎Σ : ∀ {ΣX : Σ-basis X A B} {a : A} (b : B a) → Σ-basis-path ΣX b b
  b ∎Σ = record { path = refl }

  syntax Σ-basis-path-step b q p = b ≡Σ⟨ p ⟩ q

  infixr 2 Σ-basis-path-step
  infix 3 _∎Σ
```
