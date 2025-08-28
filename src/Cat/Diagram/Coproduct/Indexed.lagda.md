<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Pullback
open import Cat.Diagram.Initial
open import Cat.Diagram.Zero
open import Cat.Univalent
open import Cat.Prelude

open import Data.Dec
```
-->

```agda
module Cat.Diagram.Coproduct.Indexed {o ℓ} (C : Precategory o ℓ) where
```

# Indexed coproducts {defines="indexed-coproduct"}

Indexed coproducts are the [dual] notion to [[indexed products]], so see
there for motivation and exposition.

[dual]: Cat.Base.html#opposites

<!--
```agda
open import Cat.Reasoning C as C
private variable
  o' ℓ' : Level
  Idx : Type ℓ'
  A B S : C.Ob
```
-->

```agda
record is-indexed-coproduct (F : Idx → C.Ob) (ι : ∀ i → C.Hom (F i) S)
  : Type (o ⊔ ℓ ⊔ level-of Idx) where
  no-eta-equality
  field
    match   : ∀ {Y} → (∀ i → C.Hom (F i) Y) → C.Hom S Y
    commute : ∀ {i} {Y} {f : ∀ i → C.Hom (F i) Y} → match f C.∘ ι i ≡ f i
    unique  : ∀ {Y} {h : C.Hom S Y} (f : ∀ i → C.Hom (F i) Y)
            → (∀ i → h C.∘ ι i ≡ f i)
            → h ≡ match f

  eta : ∀ {Y} (h : C.Hom S Y) → h ≡ match (λ i → h C.∘ ι i)
  eta h = unique _ λ _ → refl

  unique₂ : ∀ {Y} {g h : C.Hom S Y} → (∀ i → g C.∘ ι i ≡ h C.∘ ι i) → g ≡ h
  unique₂ {g = g} {h} eq = eta g ∙ ap match (funext eq) ∙ sym (eta h)

  hom-iso : ∀ {Y} → C.Hom S Y ≃ (∀ i → C.Hom (F i) Y)
  hom-iso = (λ z i → z C.∘ ι i) , is-iso→is-equiv λ where
    .is-iso.from   → match
    .is-iso.rinv x → funext λ i → commute
    .is-iso.linv x → sym (unique _ λ _ → refl)
```

A category $\cC$ **admits indexed coproducts** (of level $\ell$) if,
for any type $I : \ty\ \ell$ and family $F : I \to \cC$, there is an
indexed coproduct of $F$.

```agda
record Indexed-coproduct (F : Idx → C.Ob) : Type (o ⊔ ℓ ⊔ level-of Idx) where
  no-eta-equality
  field
    {ΣF}      : C.Ob
    ι         : ∀ i → C.Hom (F i) ΣF
    has-is-ic : is-indexed-coproduct F ι
  open is-indexed-coproduct has-is-ic public
```

<!--
```agda
Indexed-coproduct-≃
  : ∀ {ℓ ℓ'} {I : Type ℓ} {J : Type ℓ'} → (e : I ≃ J)
  → {F : I → C.Ob} → Indexed-coproduct (F ⊙ Equiv.from e) → Indexed-coproduct F
Indexed-coproduct-≃ e {F} p = λ where
  .ΣF → p .ΣF
  .ι j → p .ι (e.to j) C.∘ C.from (path→iso (ap F (e.η _)))
  .has-is-ic .match f → p .match (f ⊙ e.from)
  .has-is-ic .commute {f = f} →
    C.pulll (p .commute) ∙ from-pathp-to (C ^op) _ (ap f (e.η _))
  .has-is-ic .unique f comm → p .unique _ λ j →
      ap (_ C.∘_) (sym (from-pathp-to (C ^op) _ (ap (p .ι) (e.ε j)))
                  ∙ ap (λ z → p .ι _ C.∘ C.from (path→iso (ap F z))) (e.zag j))
    ∙ comm (e.from j)
    where
      open Indexed-coproduct
      open is-indexed-coproduct
      module e = Equiv e

Lift-Indexed-coproduct
  : ∀ {ℓ} ℓ' → {I : Type ℓ} → {F : I → C.Ob}
  → Indexed-coproduct {Idx = Lift ℓ' I} (F ⊙ lower)
  → Indexed-coproduct F
Lift-Indexed-coproduct _ = Indexed-coproduct-≃ (Lift-≃ e⁻¹)

is-indexed-coproduct-is-prop
  : ∀ {ℓ'} {Idx : Type ℓ'}
  → {F : Idx → C.Ob} {ΣF : C.Ob} {ι : ∀ idx → C.Hom (F idx) ΣF}
  → is-prop (is-indexed-coproduct F ι)
is-indexed-coproduct-is-prop {Idx = Idx} {F} {ΣF} {ι} P Q = path where
  open is-indexed-coproduct

  p : ∀ {X} → (f : ∀ i → C.Hom (F i) X) → P .match f ≡ Q .match f
  p f = Q .unique f (λ i → P .commute)

  path : P ≡ Q
  path i .match f = p f i
  path i .commute {i = idx} {f = f} =
    is-prop→pathp (λ i → C.Hom-set _ _ (p f i C.∘ ι idx) (f idx))
      (P .commute)
      (Q .commute) i
  path i .unique {h = h} f q =
    is-prop→pathp (λ i → C.Hom-set _ _ h (p f i))
      (P .unique f q)
      (Q .unique f q) i

module _ {ℓ'} {Idx : Type ℓ'} {F : Idx → C.Ob} {P P' : Indexed-coproduct F} where
  private
    module P = Indexed-coproduct P
    module P' = Indexed-coproduct P'

  Indexed-coproduct-path
    : (p : P.ΣF ≡ P'.ΣF)
    → (∀ idx → PathP (λ i → C.Hom (F idx) (p i)) (P.ι idx) (P'.ι idx))
    → P ≡ P'
  Indexed-coproduct-path p q i .Indexed-coproduct.ΣF = p i
  Indexed-coproduct-path p q i .Indexed-coproduct.ι idx = q idx i
  Indexed-coproduct-path p q i .Indexed-coproduct.has-is-ic =
    is-prop→pathp (λ i → is-indexed-coproduct-is-prop {ΣF = p i} {ι = λ idx → q idx i})
      P.has-is-ic
      P'.has-is-ic i
```
-->

## Uniqueness

As universal constructions, indexed coproducts are unique up to isomorphism.
The proof follows the usual pattern: we use the universal morphisms to
construct morphisms in both directions, and uniqueness ensures that these
maps form an isomorphism.

```agda
is-indexed-coproduct→iso
  : ∀ {ℓ'} {Idx : Type ℓ'} {F : Idx → C.Ob}
  → {ΣF ΣF' : C.Ob}
  → {ι : ∀ i → C.Hom (F i) ΣF} {ι' : ∀ i → C.Hom (F i) ΣF'}
  → is-indexed-coproduct F ι
  → is-indexed-coproduct F ι'
  → ΣF C.≅ ΣF'
is-indexed-coproduct→iso {ι = ι} {ι' = ι'} ΣF-coprod ΣF'-coprod =
  C.make-iso (ΣF.match ι') (ΣF'.match ι)
    (ΣF'.unique₂ (λ i → C.pullr ΣF'.commute ∙ ΣF.commute ∙ sym (C.idl _)))
    (ΣF.unique₂ (λ i → C.pullr ΣF.commute ∙ ΣF'.commute ∙ sym (C.idl _)))
  where
    module ΣF = is-indexed-coproduct ΣF-coprod
    module ΣF' = is-indexed-coproduct ΣF'-coprod
```

<!--
```agda
Indexed-coproduct→iso
  : ∀ {ℓ'} {Idx : Type ℓ'} {F : Idx → C.Ob}
  → (P P' : Indexed-coproduct F)
  → Indexed-coproduct.ΣF P C.≅ Indexed-coproduct.ΣF P'
Indexed-coproduct→iso P P' =
  is-indexed-coproduct→iso
    (Indexed-coproduct.has-is-ic P)
    (Indexed-coproduct.has-is-ic P')
```
-->

## Properties

Let $X : \Sigma A B \to \cC$ be a family of objects in $\cC$. If the
the indexed coproducts $\Sigma_{a, b : \Sigma A B} X_{a,b}$ and
$\Sigma_{a : A} \Sigma_{b : B(a)} X_{a, b}$ exists, then they are isomorphic.

The formal statement of this is a bit of a mouthful, but all of these
arguments are just required to ensure that the various coproducts actually
exist.

```agda
is-indexed-coproduct-assoc
  : ∀ {κ κ'} {A : Type κ} {B : A → Type κ'}
  → {X : Σ A B → C.Ob}
  → {ΣᵃᵇX : C.Ob} {ΣᵃΣᵇX : C.Ob} {ΣᵇX : A → C.Ob}
  → {ιᵃᵇ : (ab : Σ A B) → C.Hom (X ab) ΣᵃᵇX}
  → {ιᵃ : ∀ a → C.Hom (ΣᵇX a) ΣᵃΣᵇX}
  → {ιᵇ : ∀ a → (b : B a) → C.Hom (X (a , b)) (ΣᵇX a)}
  → is-indexed-coproduct X ιᵃᵇ
  → is-indexed-coproduct ΣᵇX ιᵃ
  → (∀ a → is-indexed-coproduct (λ b → X (a , b)) (ιᵇ a))
  → ΣᵃᵇX C.≅ ΣᵃΣᵇX
```

Luckily, the proof of this fact is easier than the statement! Indexed
coproducts are unique up to isomorphism, so it suffices to show that
$\Sigma_{a : A} \Sigma_{b : B(a)} X_{a, b}$ is an indexed product
over $X$, which follows almost immediately from our hypotheses.

```agda
is-indexed-coproduct-assoc {A = A} {B} {X} {ΣᵃΣᵇX = ΣᵃΣᵇX} {ιᵃ = ιᵃ} {ιᵇ} Σᵃᵇ ΣᵃΣᵇ Σᵇ =
  is-indexed-coproduct→iso Σᵃᵇ Σᵃᵇ'
  where
    open is-indexed-coproduct

    ιᵃᵇ' : ∀ (ab : Σ A B) → C.Hom (X ab) ΣᵃΣᵇX
    ιᵃᵇ' (a , b) = ιᵃ a C.∘ ιᵇ a b

    Σᵃᵇ' : is-indexed-coproduct X ιᵃᵇ'
    Σᵃᵇ' .match f = ΣᵃΣᵇ .match λ a → Σᵇ a .match λ b → f (a , b)
    Σᵃᵇ' .commute = C.pulll (ΣᵃΣᵇ .commute) ∙ Σᵇ _ .commute
    Σᵃᵇ' .unique {h = h} f p =
      ΣᵃΣᵇ .unique _ λ a →
      Σᵇ _ .unique _ λ b →
      sym (C.assoc _ _ _) ∙ p (a , b)
```

# Categories with all indexed coproducts

```agda
has-coproducts-indexed-by : ∀ {ℓ} (I : Type ℓ) → Type _
has-coproducts-indexed-by I = ∀ (F : I → C.Ob) → Indexed-coproduct F

has-indexed-coproducts : ∀ ℓ → Type _
has-indexed-coproducts ℓ = ∀ {I : Type ℓ} → has-coproducts-indexed-by I

module Indexed-coproducts-by
  {κ : Level} {Idx : Type κ}
  (has-ic : has-coproducts-indexed-by Idx)
  where
  module ∐ (F : Idx → C.Ob) = Indexed-coproduct (has-ic F)

  open ∐ renaming (commute to ι-commute; unique to match-unique) public


module Indexed-coproducts
  {κ : Level}
  (has-ic : has-indexed-coproducts κ)
  where
  module ∐ {Idx : Type κ} (F : Idx → C.Ob) = Indexed-coproduct (has-ic F)

  open ∐ renaming (commute to ι-commute; unique to match-unique) public
```


# Disjoint coproducts

An indexed coproduct $\sum F$ is said to be **disjoint** if every one of
its inclusions $F_i \to \sum F$ is [[monic]], and, for unequal $i \ne j$,
the square below is a pullback with initial apex. Since the maps $F_i
\to \sum F \ot F_j$ are monic, the pullback below computes the
_intersection_ of $F_i$ and $F_j$ as subobjects of $\sum F$, hence the
name _disjoint coproduct_: If $\bot$ is an initial object, then $F_i
\cap F_j = \emptyset$.

[monic]: Cat.Morphism.html#monos

~~~{.quiver}
\[\begin{tikzcd}
  \bot && {F_i} \\
  \\
  {F_j} && {\sum F}
  \arrow[from=1-1, to=1-3]
  \arrow[from=1-3, to=3-3]
  \arrow[from=3-1, to=3-3]
  \arrow[from=1-1, to=3-1]
\end{tikzcd}\]
~~~

```agda
record is-disjoint-coproduct (F : Idx → C.Ob) (ι : ∀ i → C.Hom (F i) S)
  : Type (o ⊔ ℓ ⊔ level-of Idx) where
  field
    has-is-ic            : is-indexed-coproduct F ι
    injections-are-monic : ∀ i → C.is-monic (ι i)
    summands-intersect   : ∀ i j → Pullback C (ι i) (ι j)
    different-images-are-disjoint
      : ∀ i j → ¬ i ≡ j → is-initial C (summands-intersect i j .Pullback.apex)
```

## Initial objects are disjoint

We prove that if $\bot$ is an initial object, then it is also an indexed
coproduct --- for any family $\bot \to \cC$ --- and furthermore, it
is a disjoint coproduct.

```agda
is-initial→is-disjoint-coproduct
  : ∀ {∅} {F : ⊥ → C.Ob} {i : ∀ i → C.Hom (F i) ∅}
  → is-initial C ∅
  → is-disjoint-coproduct F i
is-initial→is-disjoint-coproduct {F = F} {i = i} init = is-disjoint where
  open is-indexed-coproduct
  is-coprod : is-indexed-coproduct F i
  is-coprod .match _ = init _ .centre
  is-coprod .commute {i = i} = absurd i
  is-coprod .unique {h = h} f p i = init _ .paths h (~ i)

  open is-disjoint-coproduct
  is-disjoint : is-disjoint-coproduct F i
  is-disjoint .has-is-ic = is-coprod
  is-disjoint .injections-are-monic i = absurd i
  is-disjoint .summands-intersect i j = absurd i
  is-disjoint .different-images-are-disjoint i j p = absurd i
```

## Coproducts and zero objects

Let $\cC$ be a category with a [[zero object]], and let $\coprod_{i : I} P_i$
be a coproduct. If $I$ is a [[discrete]] type, then every coproduct
inclusion $\iota_{i} : \cC(P_i, \coprod_{i : I} P_i)$ has a [[retract]].

<!--
```agda
module _
  {κ} {Idx : Type κ}
  {P : Idx → C.Ob} {∐P : C.Ob} {ι : ∀ i → C.Hom (P i) ∐P}
  (coprod : is-indexed-coproduct P ι)
  where
  open is-indexed-coproduct coprod
```
-->

First, a useful lemma. Suppose that we have a coproduct $\coprod_{i : I} P_i$
indexed by a discrete type, and a map $t_i : \cC(P_i, X)$ for some $i : I$.
If there exists maps $f_j : \cC(P_j, X)$ for every $j \neq i$, then we can
obtain a map $\cC(\coprod_{i : I} P_i, X)$.


```agda
  detect
    : ∀ {X} ⦃ Idx-Discrete : Discrete Idx ⦄
    → (i : Idx) → C.Hom (P i) X
    → (∀ (j : Idx) → ¬ i ≡ j → C.Hom (P j) X)
    → C.Hom ∐P X
```

The key idea here is to check if $i = j$ when invoking the universal
property of $\coprod_{i : I} P_i$; if $i = j$ we use $t_i$,
otherwise we use $f_j$.

```agda
  detect {X = X} ⦃ Idx-Discrete ⦄ i tᵢ fⱼ = match probe
    module detect where
      probe : ∀ (j : Idx) → C.Hom (P j) X
      probe j with i ≡? j
      ... | yes i=j = subst _ i=j tᵢ
      ... | no ¬i=j = fⱼ j ¬i=j

      probe-yes : probe i ≡ tᵢ
      probe-yes rewrite ≡?-yes i = transport-refl _

      probe-no : ∀ j → (¬i=j : i ≠ j) → probe j ≡ fⱼ j ¬i=j
      probe-no j ¬i=j rewrite ≡?-no ¬i=j = refl
```

Moreover, we observe that our newly created map interacts nicely
with the inclusions into the coproduct.

```agda
  detect-yes
    : ∀ {X} ⦃ Idx-Discrete : Discrete Idx ⦄
    → {i : Idx} → {tᵢ : C.Hom (P i) X}
    → {fⱼ : ∀ (j : Idx) → ¬ i ≡ j → C.Hom (P j) X}
    → detect i tᵢ fⱼ C.∘ ι i ≡ tᵢ
  detect-yes = commute ∙ detect.probe-yes _ _ _

  detect-no
    : ∀ {X} ⦃ Idx-Discrete : Discrete Idx ⦄
    → {i : Idx} → {tᵢ : C.Hom (P i) X}
    → {fⱼ : ∀ (j : Idx) → ¬ i ≡ j → C.Hom (P j) X}
    → ∀ j → (¬i=j : ¬ i ≡ j) → detect i tᵢ fⱼ C.∘ ι j ≡ fⱼ j ¬i=j
  detect-no j ¬i=j = commute ∙ detect.probe-no _ _ _ j ¬i=j
```

Refocusing our attention back to our original claim, suppose that
$\cC$ has a zero object. This means that there is a canonical choice
of morphism between any two objects, so we can apply our previous
lemma to obtain a retract $\cC(\coprod_{I} P_i, P_i)$.

```agda
  zero→ι-has-retract
    : ∀ ⦃ Idx-Discrete : Discrete Idx ⦄
    → Zero C
    → ∀ i → C.has-retract (ι i)
  zero→ι-has-retract z i =
    C.make-retract (detect i C.id (λ _ _ → zero→)) detect-yes
    where open Zero z
```
