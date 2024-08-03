<!--
```agda
open import 1Lab.Path.Reasoning
open import 1Lab.Prelude

open import Data.Set.Truncation

open import Homotopy.Truncation
```
-->

```agda
module Homotopy.Connectedness where
```

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A B : Type ℓ
  P : A → Type ℓ
  x y : A
```
-->

# Connectedness {defines="connected connectedness connectivity simply-connected"}

We say that a type is **$n$-connected** if its $n$-[[truncation]] is
[[contractible]].

While being $n$-[[truncated]] expresses that all homotopy groups above
$n$ are trivial, being $n$-connected means that all homotopy groups
*below* $n$ are trivial.  A type that is both $n$-truncated and
$n$-connected is contractible.

We give definitions in terms of the [[propositional truncation]] and
[[set truncation]] for the lower levels, and then defer to the general
"hubs and spokes" truncation.  Note that our indices are offset by 2,
just like [[h-levels]].

```agda
is-n-connected : ∀ {ℓ} → Type ℓ → Nat → Type _
is-n-connected A zero = Lift _ ⊤
is-n-connected A (suc zero) = ∥ A ∥
is-n-connected A (suc (suc zero)) = is-contr ∥ A ∥₀
is-n-connected A n@(suc (suc (suc _))) = is-contr (n-Tr A n)
```

Being $n$-connected is a proposition:

```agda
is-n-connected-is-prop : (n : Nat) → is-prop (is-n-connected A n)
is-n-connected-is-prop 0 _ _ = refl
is-n-connected-is-prop 1     = is-prop-∥-∥
is-n-connected-is-prop 2     = is-contr-is-prop
is-n-connected-is-prop (suc (suc (suc n))) = is-contr-is-prop
```

For short, we say that a type is **connected** if it is $0$-connected, and
**simply connected** if it is $1$-connected:

```agda
is-connected : ∀ {ℓ} → Type ℓ → Type _
is-connected A = is-n-connected A 2

is-simply-connected : ∀ {ℓ} → Type ℓ → Type _
is-simply-connected A = is-n-connected A 3
```

:::{.definition #connected-map}
Furthermore, we say that a map is $n$-connected if all of its [[fibres]] are
$n$-connected.

```agda
is-n-connected-map : (A → B) → Nat → Type _
is-n-connected-map f n = ∀ x → is-n-connected (fibre f x) n
```
:::

## Pointed connected types

In the case of [[pointed types]], there is an equivalent definition of
being connected that is sometimes easier to work with: a pointed type is
connected if every point is merely equal to the base point.

```agda
is-connected∙ : ∀ {ℓ} → Type∙ ℓ → Type _
is-connected∙ (X , pt) = (x : X) → ∥ x ≡ pt ∥

module _ {ℓ} {X@(_ , pt) : Type∙ ℓ} where
  is-connected∙→is-connected : is-connected∙ X → is-connected ⌞ X ⌟
  is-connected∙→is-connected c .centre = inc pt
  is-connected∙→is-connected c .paths = elim! λ x → case c x of λ
    pt=x → ap inc (sym pt=x)

  is-connected→is-connected∙ : is-connected ⌞ X ⌟ → is-connected∙ X
  is-connected→is-connected∙ c x =
    ∥-∥₀-path.to (is-contr→is-prop c (inc x) (inc pt))
```

This alternative definition lets us formulate a nice elimination
principle for pointed connected types: any family of propositions $P$
that holds on the base point holds everywhere.

In particular, since `being a proposition is a proposition`{.Agda
ident=is-prop-is-prop}, we only need to check that $P(\point{})$ is a
proposition.

```agda
connected∙-elim-prop
  : ∀ {ℓ ℓ'} {X : Type∙ ℓ} {P : ⌞ X ⌟ → Type ℓ'}
  → is-connected∙ X
  → is-prop (P (X .snd))
  → P (X .snd)
  → ∀ x → P x
connected∙-elim-prop {X = X} {P} conn prop pb x =
  ∥-∥-rec propx (λ e → subst P (sym e) pb) (conn x)
  where abstract
    propx : is-prop (P x)
    propx = ∥-∥-rec is-prop-is-prop (λ e → subst (is-prop ∘ P) (sym e) prop) (conn x)
```

We can similarly define an elimination principle into sets.

```agda
module connected∙-elim-set
  {ℓ ℓ'} {X : Type∙ ℓ} {P : ⌞ X ⌟ → Type ℓ'}
  (conn : is-connected∙ X)
  (set : is-set (P (X .snd)))
  (pb : P (X .snd))
  (loops : ∀ (p : X .snd ≡ X .snd) → PathP (λ i → P (p i)) pb pb)
  where opaque

  elim : ∀ x → P x
  elim x = work (conn x)
    module elim where
      setx : is-set (P x)
      setx = ∥-∥-rec (is-hlevel-is-prop 2) (λ e → subst (is-set ∘ P) (sym e) set) (conn x)

      work : ∥ x ≡ X .snd ∥ → P x
      work = ∥-∥-rec-set setx
        (λ p → subst P (sym p) pb)
        (λ p q i → subst P (sym (∙-filler'' (sym p) q i)) (loops (sym p ∙ q) i))

  elim-β-point : elim (X .snd) ≡ pb
  elim-β-point = subst (λ c → elim.work (X .snd) c ≡ pb)
    (squash (inc refl) (conn (X .snd)))
    (transport-refl pb)
```

Examples of pointed connected types include the [[circle]] and the
[[delooping]] of a group.

## Closure properties

As a property of types, $n$-connectedness enjoys closure properties very
similar to those of $n$-truncatedness; and we establish them in much the
same way, by proving that $n$-connectedness is preserved by retractions.

However, the definition of `is-n-connected`{.Agda}, which uses the
explicit constructions of truncations for the base cases, is slightly
annoying to work when $n$ is arbitrary: that's the trade-off for it
being easy to work with when $n$ is a known, and usually small, number.
Therefore, we prove the following lemma by the recursion, establishing
that the notion of connectedness could very well have been defined using
the general $n$-truncation uniformly.

```agda
is-n-connected-Tr : ∀ {ℓ} {A : Type ℓ} n → is-n-connected A (suc n) → is-contr (n-Tr A (suc n))
is-n-connected-Tr zero a-conn = ∥-∥-out! do
  pt ← a-conn
  pure $ contr (inc pt) (λ x → n-Tr-is-hlevel 0 _ _)
is-n-connected-Tr (suc zero) a-conn =
  retract→is-hlevel 0
    (∥-∥₀-rec (n-Tr-is-hlevel 1) inc)
    (n-Tr-rec squash inc)
    (n-Tr-elim _ (λ _ → is-prop→is-set (n-Tr-is-hlevel 1 _ _)) λ _ → refl)
    a-conn
is-n-connected-Tr (suc (suc n)) a-conn = a-conn
```

<!--
```agda
is-n-connected-Tr-is-equiv : ∀ {ℓ} {A : Type ℓ} n → is-equiv (is-n-connected-Tr {A = A} n)
is-n-connected-Tr-is-equiv {A = A} n = prop-ext (is-n-connected-is-prop _) (hlevel 1) _ (from n) .snd where
  from : ∀ n → is-contr (n-Tr A (suc n)) → is-n-connected A (suc n)
  from zero c = n-Tr-rec! inc (c .centre)
  from (suc zero) = retract→is-hlevel 0 (n-Tr-rec! inc)
    (∥-∥₀-rec (n-Tr-is-hlevel 1) inc)
    (∥-∥₀-elim (λ _ → is-prop→is-set (squash _ _)) λ _ → refl)
  from (suc (suc n)) x = x

module n-connected {ℓ} {A : Type ℓ} (n : Nat) =
  Equiv (_ , is-n-connected-Tr-is-equiv {A = A} n)
```
-->

The first closure property we'll prove is very applicable: it says that
any retract of an $n$-connected type is again $n$-connected. Intuitively
this is because any retraction $f : A \to B$ can be extended to a
retraction $\| A \|_n \to \| B \|_n$, and contractible types are closed
under retractions.

```agda
retract→is-n-connected
  : (n : Nat) (f : A → B) (g : B → A)
  → is-left-inverse f g → is-n-connected A n → is-n-connected B n
retract→is-n-connected 0 = _
retract→is-n-connected 1 f g h a-conn = f <$> a-conn
retract→is-n-connected (suc (suc n)) f g h a-conn =
  n-connected.from (suc n) $ retract→is-contr
    (rec! (inc ∘ f))
    (rec! (inc ∘ g))
    (elim! λ x → ap n-Tr.inc (h x))
    (is-n-connected-Tr (suc n) a-conn)
```

Since the truncation operator $\| - \|_n$ also preserves products, a
remarkably similar argument shows that if $A$ and $B$ are $n$-connected,
then so is $A \times B$.

```agda
×-is-n-connected
  : ∀ n → is-n-connected A n → is-n-connected B n → is-n-connected (A × B) n
×-is-n-connected 0 = _
×-is-n-connected (suc n) a-conn b-conn = n-connected.from n $ Equiv→is-hlevel 0
  n-Tr-product (×-is-hlevel 0 (n-connected.to n a-conn) (n-connected.to n b-conn))
```

We can generalise this to $\Sigma$-types: if $A$ is $n$-connected and
$B$ is an $A$-indexed family of $n$-connected types, then we have
$\|\Sigma_{a : A} B(a)\|_n \simeq \|\Sigma_{a : A} \|B(a)\|_n\|_n
\simeq \|A\|_n \simeq 1$.

```agda
Σ-is-n-connected
  : ∀ n → is-n-connected A n → (∀ a → is-n-connected (P a) n) → is-n-connected (Σ A P) n
Σ-is-n-connected 0 = _
Σ-is-n-connected (suc n) a-conn b-conn = n-connected.from n $ Equiv→is-hlevel 0
  (n-Tr-Σ ∙e n-Tr-≃ (Σ-contract λ _ → n-connected.to n (b-conn _)))
  (n-connected.to n a-conn)
```

Finally, we show the dual of two properties of truncations: if $A$ is
$(1+n)$-connected, then each path space $x \equiv_A y$ is $n$-connected;
And if $A$ is $(2+n)$-connected, then it is also $(1+n$) connected. This
latter property lets us count _down_ in precisely the same way that
`is-hlevel-suc`{.Agda} lets us count _up_.

<!--
```agda
_ = is-hlevel-suc
```
-->

```agda
Path-is-connected : ∀ n → is-n-connected A (suc n) → is-n-connected (Path A x y) n
Path-is-connected 0 = _
Path-is-connected {x = x} (suc n) conn = n-connected.from n (contr (ps _ _) $
  n-Tr-elim! _
    (J (λ y p → ps x y ≡ inc p) (Equiv.injective (Equiv.inverse n-Tr-path-equiv)
      (is-contr→is-set (is-n-connected-Tr _ conn) _ _ _ _))))
  where
    ps : ∀ x y → n-Tr (x ≡ y) (suc n)
    ps x y = Equiv.to n-Tr-path-equiv (is-contr→is-prop (is-n-connected-Tr _ conn) _ _)

is-connected-suc
  : ∀ {ℓ} {A : Type ℓ} n
  → is-n-connected A (suc n) → is-n-connected A n
is-connected-suc {A = A} zero _ = _
is-connected-suc {A = A} (suc n) w = n-connected.from n $ elim!
    (λ x → contr (inc x) (elim! (rem₁ n w x)))
    (is-n-connected-Tr (suc n) w .centre)
  where
    rem₁ : ∀ n → is-n-connected A (2 + n) → ∀ x y → Path (n-Tr A (suc n)) (inc x) (inc y)
    rem₁ zero a-conn x y = n-Tr-is-hlevel 0 _ _
    rem₁ (suc n) a-conn x y = Equiv.from n-Tr-path-equiv
      (n-Tr-rec (is-hlevel-suc _ (n-Tr-is-hlevel n)) inc
        (is-n-connected-Tr _ (Path-is-connected (2 + n) a-conn) .centre))

is-connected-+
  : ∀ {ℓ} {A : Type ℓ} (n k : Nat)
  → is-n-connected A (k + n) → is-n-connected A n
is-connected-+ n zero w = w
is-connected-+ n (suc k) w = is-connected-+ n k (is-connected-suc _ w)
```

## In terms of propositional truncations {defines="connectedness-via-propositional-truncation"}

There is an alternative definition of connectedness that avoids talking about
arbitrary truncations, and is thus sometimes easier to work with.
Generalising the special cases for $n = -1$ (a type is $(-1)$-connected if and
only if it is inhabited) and $n = 0$ (a type is $0$-connected if and only if
it is inhabited and all points are merely equal), we can prove that a type
is $n$-connected if and only if it is inhabited and all its path spaces
are $(n-1)$-connected.

We can use this to give a definition of connectedness that only makes use
of *propositional* truncations, with the base case being that all types are
$(n-2)$-connected:

```agda
is-n-connected-∥-∥ : ∀ {ℓ} → Type ℓ → Nat → Type ℓ
is-n-connected-∥-∥ A zero = Lift _ ⊤
is-n-connected-∥-∥ A (suc n) =
  ∥ A ∥ × ∀ (a b : A) → is-n-connected-∥-∥ (a ≡ b) n

is-n-connected-∥-∥-is-prop : ∀ n → is-prop (is-n-connected-∥-∥ A n)
is-n-connected-∥-∥-is-prop zero = hlevel 1
is-n-connected-∥-∥-is-prop (suc n) = ×-is-hlevel 1 (hlevel 1)
  (Π-is-hlevel² 1 λ _ _ → is-n-connected-∥-∥-is-prop n)
```

We show that this is equivalent to the $n$-truncation of a type being contractible,
hence in turn to our first definition.

```agda
is-contr-n-Tr→∥-∥
  : ∀ n → is-contr (n-Tr A (suc n)) → is-n-connected-∥-∥ A (suc n)
is-contr-n-Tr→∥-∥ zero h .fst = n-Tr-rec! inc (h .centre)
is-contr-n-Tr→∥-∥ zero h .snd = _
is-contr-n-Tr→∥-∥ (suc n) h .fst = n-Tr-rec! inc (h .centre)
is-contr-n-Tr→∥-∥ (suc n) h .snd a b = is-contr-n-Tr→∥-∥ n
  (Equiv→is-hlevel 0 (n-Tr-path-equiv e⁻¹) (Path-is-hlevel 0 h))

∥-∥→is-contr-n-Tr
  : ∀ n → is-n-connected-∥-∥ A (suc n) → is-contr (n-Tr A (suc n))
∥-∥→is-contr-n-Tr zero (a , _) = is-prop∙→is-contr (hlevel 1) (rec! inc a)
∥-∥→is-contr-n-Tr (suc n) (a , h) = case a of λ a →
  is-prop∙→is-contr
    (elim! λ a b → Equiv.from n-Tr-path-equiv (∥-∥→is-contr-n-Tr n (h a b) .centre))
    (inc a)

is-n-connected→∥-∥
  : ∀ n → is-n-connected A n → is-n-connected-∥-∥ A n
is-n-connected→∥-∥ zero _ = _
is-n-connected→∥-∥ (suc n) h = is-contr-n-Tr→∥-∥ n (n-connected.to n h)

∥-∥→is-n-connected
  : ∀ n → is-n-connected-∥-∥ A n → is-n-connected A n
∥-∥→is-n-connected zero _ = _
∥-∥→is-n-connected (suc n) h = n-connected.from n (∥-∥→is-contr-n-Tr n h)

is-n-connected≃∥-∥
  : ∀ n → is-n-connected A n ≃ is-n-connected-∥-∥ A n
is-n-connected≃∥-∥ {A = A} n = prop-ext
  (is-n-connected-is-prop {A = A} n) (is-n-connected-∥-∥-is-prop n)
  (is-n-connected→∥-∥ n) (∥-∥→is-n-connected n)

module n-connected-∥-∥ {ℓ} {A : Type ℓ} (n : Nat) =
  Equiv (is-n-connected≃∥-∥ {A = A} n)
```

## In relation to truncatedness

The following lemmas define $n$-connectedness of a type $A$ by how it
can map into the $n$-*truncated* types. We then expand this idea to
cover the $n$-connected maps, too. At the level of types, the "relative"
characterisation of $n$-connectedness says that, if $A$ is $n$-connected
and $B$ is $n$-truncated, then the function $\rm{const} : B \to (A \to
B)$ is an equivalence.

The intuitive idea behind this theorem is as follows: we have assumed
that $A$ has no interesting information below dimension $n$, and that
$B$ has no interesting information in the dimensions $n$ and above.
Therefore, the functions $A \to B$ can't be interesting, since they're
mapping boring data into boring data.

The proof is a direct application of the definition of $n$-connectedness
and the universal property of truncations: $A \to B$ is equivalent to
$\| A \|_n \to B$, but this is equivalent to $B$ since $\| A \|_n$ is
contractible.

```agda
is-n-connected→n-type-const
  : ∀ n → is-hlevel B (suc n) → is-n-connected A (suc n)
  → is-equiv {B = A → B} (λ b a → b)
is-n-connected→n-type-const {B = B} {A = A} n B-hl A-conn =
  subst is-equiv (λ i x z → transp (λ i → B) i x) $ snd $
  B                      ≃⟨ Π-contr-eqv (is-n-connected-Tr n A-conn) e⁻¹ ⟩
  (n-Tr A (suc n) → B)   ≃⟨ n-Tr-univ n B-hl ⟩
  (A → B)                ≃∎
```

This direction of the theorem is actually half of an equivalence. In the
other direction, since $\| A \|_n$ is $n$-truncated by definition, we
suppose that $\rm{const} : \| A \|_n \to (A \to \| A \|_n)$ is an
equivalence. From the constructor $\operatorname{inc} : A \to \| A \|_n$
we obtain a point $p : \| A \|_n$, and, for all $a$, we have

$$
p = \operatorname{const}(p)(a) = \operatorname{inc}(a)
$$.

But by induction on truncation, this says precisely that any $a : \| A
\|_n$ is equal to $p$; so $p$ is a centre of contraction, and $A$ is
$n$-connected.

```agda
n-type-const→is-n-connected
  : ∀ {ℓ} {A : Type ℓ} n
  → (∀ {B : Type ℓ} → is-hlevel B (suc n) → is-equiv {B = A → B} (λ b a → b))
  → is-n-connected A (suc n)
n-type-const→is-n-connected {A = A} n eqv =
  n-connected.from n $ contr (rem.from inc) $ n-Tr-elim _
    (λ h → Path-is-hlevel (suc n) (n-Tr-is-hlevel n)) (rem.ε inc $ₚ_)
  where module rem = Equiv (_ , eqv {n-Tr A (suc n)} (hlevel _))
```

We can now generalise this to work with an $n$-connected map $f : A \to
B$ and a family $P$ of $n$-types over $B$: in this setting,
precomposition with $f$ is an equivalence

$$
(\Pi_{a : A} P(fa)) \to (\Pi_{b : B} P(b))
$$.

This is somewhat analogous to generalising from a recursion principle to
an elimination principle. When we were limited to talking about types,
we could extend points $b : B$ to functions $A \to B$, but no dependency
was possible. With the extra generality, we think of $f$ as including a
space of "constructors", and the equivalence says that exhibiting $P$ at
these constructors is equivalent to exhibiting it for the whole type.

```agda
relative-n-type-const
  : (P : B → Type ℓ'') (f : A → B)
  → ∀ n → is-n-connected-map f n
  → (∀ x → is-hlevel (P x) n)
  → is-equiv {A = (∀ b → P b)} {B = (∀ a → P (f a))} (_∘ f)
```

<!--
```
relative-n-type-const {B = B} {A = A} P f (suc (suc k)) n-conn phl =
  subst is-equiv (funext λ g → funext λ a → transport-refl _) (rem₁ .snd)
  where
  n = suc k
  open is-iso

  shuffle : ((b : B) → fibre f b → P b) ≃ ((a : A) → P (f a))
  rem₁ : ((b : B) → P b) ≃ ((a : A) → P (f a))
```
-->

Despite the generality, the proof is just a calculation: observing that
we have the following chain of equivalences suffices.

```agda
  rem₁ =
    ((b : B) → P b)                             ≃⟨ Π-cod≃ (λ x → Π-contr-eqv {B = λ _ → P x} (is-n-connected-Tr _ (n-conn x)) e⁻¹) ⟩
    ((b : B) → n-Tr (fibre f b) (suc n) → P b)  ≃⟨ Π-cod≃ (λ x → n-Tr-univ n (phl _)) ⟩
    ((b : B) → fibre f b → P b)                 ≃⟨ shuffle ⟩
    ((a : A) → P (f a))                         ≃∎
```

<details>
<summary>There's also the `shuffle`{.Agda} isomorphism that eliminates
the `fibre`{.Agda} argument using path induction, but its construction
is mechanical.
</summary>

```agda
  shuffle = Iso→Equiv λ where
    .fst      g a         → g (f a) (a , refl)
    .snd .inv g b (a , p) → subst P p (g a)
    .snd .rinv g → funext λ a → transport-refl _
    .snd .linv g → funext λ b → funext λ { (a , p) →
      J (λ b p → subst P p (g (f a) (a , refl)) ≡ g b (a , p))
        (transport-refl _) p }
```

</details>

<!--
```
relative-n-type-const {B = B} {A = A} P f 0 n-conn phl =
  is-contr→is-equiv (Π-is-hlevel 0 phl) (Π-is-hlevel 0 λ _ → phl _)

relative-n-type-const {B = B} {A = A} P f 1 n-conn phl =
  prop-ext (Π-is-hlevel 1 phl) (Π-is-hlevel 1 λ _ → phl _)
    _ (λ g b → ∥-∥-rec (phl b) (λ (a , p) → subst P p (g a)) (n-conn b))
    .snd
```
-->

We can specialise this to get a literal elimination principle: If $P$ is
a family of $n$-types over an $(1+n)$-connected pointed type $(A, a_0)$,
then $P$ holds everywhere if $P(a_0)$ holds. Moreover, this has the
expected computation rule.

```agda
module _ n (P : A → Type ℓ) (tr : ∀ x → is-hlevel (P x) n)
           {a₀ : A} (pa₀ : P a₀)
           (a-conn : is-n-connected A (suc n))
  where

  connected-elimination-principle : fibre (λ z x → z a₀) (λ _ → pa₀)
  connected-elimination-principle = relative-n-type-const {A = ⊤} P (λ _ → a₀) n
    (λ x → retract→is-n-connected n (λ p → tt , p) snd (λ _ → refl)
      (Path-is-connected n a-conn))
    tr .is-eqv (λ _ → pa₀) .centre

  opaque
    connected-elim : ∀ x → P x
    connected-elim = connected-elimination-principle .fst

    connected-elim-β : connected-elim a₀ ≡ pa₀
    connected-elim-β = connected-elimination-principle .snd $ₚ tt
```

Using these elimination principles, we can prove that a pointed type
$(A,a_0)$ is $(1+n)$-connected if and only if the inclusion of $a_0$ is
$n$-connected when considered as a map $\top \to A$.

```agda
is-n-connected-point
  : ∀ {ℓ} {A : Type ℓ} (a₀ : A) n
  → is-n-connected-map {A = ⊤} (λ _ → a₀) n
  → is-n-connected A (suc n)
is-n-connected-point {A = A} a₀ n pt-conn = done where
  rem : ∀ {B : Type ℓ} → is-hlevel B (suc n) → ∀ (f : A → B) a → f a₀ ≡ f a
  rem b-hl f = equiv→inverse
    (relative-n-type-const (λ a → f a₀ ≡ f a) _ n pt-conn λ x → Path-is-hlevel' n b-hl _ _)
    (λ _ → refl)

  done : is-n-connected A (suc n)
  done = n-type-const→is-n-connected n λ hl → is-iso→is-equiv $
    iso (λ f → f a₀) (λ f → funext λ a → rem hl f a) λ _ → refl

point-is-n-connected
  : ∀ {ℓ} {A : Type ℓ} (a₀ : A) n
  → is-n-connected A (2 + n)
  → is-n-connected-map {A = ⊤} (λ _ → a₀) (suc n)
point-is-n-connected a₀ n a-conn =
  connected-elim (suc n) (λ x → is-n-connected (⊤ × (a₀ ≡ x)) (suc n))
    (λ x → is-prop→is-hlevel-suc (is-n-connected-is-prop (suc n)))
    (retract→is-n-connected (suc n) (tt ,_) snd (λ _ → refl)
      (Path-is-connected {y = a₀} (suc n) a-conn))
    a-conn
```

<!--
```agda
relative-n-type-const-plus
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} (P : B → Type ℓ'')
  → (f : A → B)
  → ∀ n k
  → is-n-connected-map f n
  → (∀ x → is-hlevel (P x) (k + n))
  → ∀ it → is-hlevel (fibre {A = ((b : B) → P b)} {B = (a : A) → P (f a)} (_∘ f) it) k

relative-n-type-const-plus P f n zero f-conn P-hl it = relative-n-type-const P f n f-conn P-hl .is-eqv it
relative-n-type-const-plus {A = A} {B = B} P f n (suc k) f-conn P-hl it = done where
  T = fibre {A = ((b : B) → P b)} {B = (a : A) → P (f a)} (_∘ f) it

  module _ (gp@(g , p) hq@(h , q) : T) where
    Q : B → Type _
    Q b = g b ≡ h b

    S = fibre {A = (∀ b → Q b)} {B = (∀ a → Q (f a))} (_∘ f) λ a → happly (p ∙ sym q) a

    rem₃ : ∀ {ℓ} {A : Type ℓ} {x y : A} (p q : x ≡ y) → (p ≡ q) ≡ (refl ≡ p ∙ sym q)
    rem₃ {x = x} p q = J (λ y q → (p : x ≡ y) → (p ≡ q) ≡ (refl ≡ p ∙ sym q))
      (λ p → sym (ap (refl ≡_) (∙-idr p) ∙ Iso→Path (sym , iso sym (λ _ → refl) (λ _ → refl)))) q p

    abstract
      remark
        : ∀ {h} (α : g ≡ h) {q : h ∘ f ≡ it}
        → (PathP (λ i → α i ∘ f ≡ it) p q)
        ≃ (happly α ∘ f ≡ happly (p ∙ sym q))
      remark α = J
        (λ h α → {q : h ∘ f ≡ it} → PathP (λ i →  α i ∘ f ≡ it) p q ≃ (happly α ∘ f ≡ happly (p ∙ sym q)))
        (path→equiv (rem₃ _ _) ∙e (_ , embedding→cancellable {f = happly} λ x →
          is-contr→is-prop (is-iso→is-equiv
            (iso funext (λ _ → refl) (λ _ → refl)) .is-eqv x)))
        α

    to : Path T gp hq → S
    to α = happly (ap fst α) , remark (ap fst α) .fst (ap snd α)

    from : S → Path T gp hq
    from (a , b) = ap₂ _,_ (funext a) (Equiv.from (remark (funext a)) b)

    linv : is-left-inverse from to
    linv x = ap₂ (ap₂ _,_) refl (Equiv.η (remark _) _)

  done = Path-is-hlevel→is-hlevel k $ λ x y →
    retract→is-hlevel k (from _ _) (to _ _) (linv _ _) $
      relative-n-type-const-plus (Q x y) f n k f-conn
        (λ x → Path-is-hlevel' (k + n) (P-hl x) _ _) _
```
-->
