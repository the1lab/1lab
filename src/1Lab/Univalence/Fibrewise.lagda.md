<!--
```agda
open import 1Lab.Reflection.Univalence
open import 1Lab.Equiv.Fibrewise
open import 1Lab.Path.Cartesian
open import 1Lab.Type.Sigma
open import 1Lab.Univalence
open import 1Lab.Type.Pi
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.Univalence.Fibrewise where
```

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A B X Y : Type ℓ
  P Q : A → Type ℓ'
```
-->

# Univalence for type families

Any [[equivalence]] $e : A \simeq B$ lets us compare type families $P
\liesover A$ and $Q \liesover Q$, by forming the type of [[fibrewise
equivalences|equivalence over]] $e$ between $P$ and $Q$. A useful
univalence-type result in this setting would be to show that equivalent
type families are actually identical (over the path induced by $e$),
and, indeed, we can prove this:

<!--
```agda
private module _ where private
  _ = comp
```
-->

```agda
  ua-over : (e : A ≃ B) (e' : P ≃[ e ] Q) → PathP (λ i → ua e i → Type _) P Q
  ua-over e e' = ua→ λ a → ua (e' a (e .fst a) refl)
```

The trouble with this definition arises when we want to consider paths
over it, since then we need to consider the precise definition of
`ua→`{.Agda} in terms of `comp`{.Agda}. Still, we can put together a
function for showing that sections of $P \liesover A$ and $Q \liesover
B$ are identical:

```agda
  ua-over-pathp
    : (e : A ≃ B) (e' : P ≃[ e ] Q) {f : ∀ x → P x} {g : ∀ x → Q x}
    → ((a : A) → e' a _ refl .fst (f a) ≡ g (e .fst a))
    → PathP (λ i → (x : ua e i) → ua-over e e' i x) f g
  ua-over-pathp e e' {f} {g} p = funext-dep λ {x₀} {x₁} q i →
    comp (λ j → ua→.filler {e = e} {λ _ _ → Type _} (λ a → ua (e' a (e .fst a) refl)) i j (q i)) (∂ i) λ where
      k (k = i0) → g (unglue (q i))
      k (i = i0) → attach (∂ k) (λ { (k = i0) → _ ; (k = i1) → _ }) (inS (p x₀ (~ k)))
      k (i = i1) → g x₁
```

For practical formalisation, we prefer to define `ua-over`{.Agda}
directly as a [[glue type]]. In particular, in a context with $i : \bI$
and $x : \rm{ua}(e,i)$, the type $Q(\operatorname{unglue} x)$ is
equivalent to both $P x$ (through the assumed equivalence over $e$) and
$Q x$ (by the identity equivalence).

```agda
module _ {A B : Type ℓ} {P : A → Type ℓ'} {Q : B → Type ℓ'} (e : A ≃ B) (e' : P ≃[ e ] Q) where
  ua-over : PathP (λ i → ua e i → Type ℓ') P Q
  ua-over i x = Glue (Q (unglue x)) λ where
    (i = i0) → P x , e' x _ refl
    (i = i1) → Q x , id≃
```

We can then use the constructor for `Glue`{.Agda} types to put together
a proof that a section of $P$ is identical to a section of $B$ when it
commutes with the given equivalences.

```agda
  ua-over-pathp
    : {f : ∀ x → P x} {g : ∀ x → Q x}
    → ((a : A) → e' a _ refl .fst (f a) ≡ g (e .fst a))
    → PathP (λ i → (x : ua e i) → ua-over i x) f g
  ua-over-pathp {g = g} h i x = attach (∂ i) (λ { (i = i0) → _ ; (i = i1) → _ }) (inS
    (hcomp (∂ i) λ where
      k (k = i0) → g (unglue x)
      k (i = i0) → h x (~ k)
      k (i = i1) → g x))
```

We can also *destruct* a `Glue`{.Agda} type, which gives us a converse
to the above.

```agda
  pathp-ua-over
    : {f : ∀ x → P x} {g : ∀ x → Q x}
    → PathP (λ i → (x : ua e i) → ua-over i x) f g
    → ∀ x → e' x _ refl .fst (f x) ≡ g (e .fst x)
  pathp-ua-over p x i = unglue (p i (ua-inc e x i))
```
