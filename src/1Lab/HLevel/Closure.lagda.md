---
description: |
  We establish that h-levels are closed under retractions, and use this
  to establish many closure properties of h-levels. Then we table
  these closure properties using Agda's instance resolution mechanism,
  automating "boring" h-level obligations.
---
<!--
```agda
{-# OPTIONS --no-projection-like #-}
open import 1Lab.Path.Groupoid
open import 1Lab.Type.Sigma
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.HLevel.Closure where
```

# Closure of h-levels

<!--
```agda
private variable
  ℓ ℓ' : Level
  A B C : Type ℓ
  F G : A → Type ℓ
```
-->

When showing that a given type $T$ is a [[homotopy $n$-type]], it's
often possible to reason *syntactically* about the type formers which
were used in the construction of $T$. This is fundamentally because the
$n$-types are *closed under* a variety of type-forming operations, and
*that* fact boils down to the fact that, in a homotopy type theory, the
structure of identity types tends to be "self-similar" --- for example,
paths between pairs are pairs of paths.

## Split surjections and retractions

The fundamental result that we will piggy-back to derive the closure of
$n$-types under various operations is that [[contractible]] types are
closed under *split surjections*. Unfolding this, it says that if we
have a map $f : A \to B$ and a section $\forall_{b : B} f^*(b)$
assigning [[fibres]] of $f$ over each $b : B$, then $B$ is contractible
whenever $A$ is.

The proof is a short calculation:

```agda
split-surjection→is-contr
  : (f : A → B) (s : (b : B) → fibre f b)
  → is-contr A → is-contr B
split-surjection→is-contr f s c .centre  = f (c .centre)
split-surjection→is-contr f s c .paths x =
  f (c .centre) ≡⟨ ap f (c .paths _) ⟩
  f (s x .fst)  ≡⟨ s x .snd ⟩
  x             ∎
```

Usually, the data of a split surjection is unpacked to talk about
*retractions* instead. That is, instead of talking about a section of
$f$'s fibres, we unpack the components to mention the inverse map $g : B
\to A$ and the proof that $f(gx) = x$.

```agda
retract→is-contr
  : (f : A → B) (g : B → A)
  → is-left-inverse f g → is-contr A → is-contr B
retract→is-contr f g h isC .centre = f (isC .centre)
retract→is-contr f g h isC .paths x =
  f (isC .centre) ≡⟨ ap f (isC .paths _) ⟩
  f (g x)         ≡⟨ h _ ⟩
  x               ∎
```

Recalling that our hierarchy of $n$-types has two base cases, if we are
to show that *all* h-levels are closed under retractions, we should also
repeat the argument above for propositions. This turns out to be no
biggie, so that there is no impediment to starting the inductive proof.

```agda
retract→is-prop
  : (f : A → B) (g : B → A) → is-left-inverse f g
  → is-prop A → is-prop B
retract→is-prop f g h propA x y =
  x       ≡⟨ sym (h _) ⟩
  f (g x) ≡⟨ ap f (propA _ _) ⟩
  f (g y) ≡⟨ h _ ⟩
  y       ∎

retract→is-hlevel
  : (n : Nat) (f : A → B) (g : B → A)
  → is-left-inverse f g → is-hlevel A n → is-hlevel B n
retract→is-hlevel 0 = retract→is-contr
retract→is-hlevel 1 = retract→is-prop
```

In the inductive case, we show that a retraction *induces* retractions
between path spaces: the map $\ap{g} : x \equiv y \to g(x) \equiv y$ is a
split surjection. The construction simply whiskers the proof $\ap{f}{p} :
fg(x) = fg(y)$ with paths that cancel $fg$:

```agda
retract→is-hlevel (suc (suc n)) f g h hlevel x y =
  retract→is-hlevel (suc n) sect (ap g) inv (hlevel (g x) (g y)) where
    sect : g x ≡ g y → x ≡ y
    sect path =
      x       ≡⟨ sym (h _) ⟩
      f (g x) ≡⟨ ap f path ⟩
      f (g y) ≡⟨ h _ ⟩
      y       ∎
```

The proof that this function _does_ invert `ap g` on the left is boring,
but it consists mostly of symbol pushing. The only non-trivial step, and
the key to the proof, is the theorem that `homotopies behave like
natural transformations`{.Agda ident=homotopy-natural}: We can flip `ap
f (ap g path)` and `h y` to get a pair of paths that annihilates on the
left, and `path` on the right.

```agda
    inv : is-left-inverse sect (ap g)
    inv path =
      sym (h x) ∙ ap f (ap g path) ∙ h y ∙ refl ≡⟨ ap (λ e → sym (h _) ∙ _ ∙ e) (∙-idr (h _)) ⟩
      sym (h x) ∙ ap f (ap g path) ∙ h y        ≡⟨ ap₂ _∙_ refl (sym (homotopy-natural h _)) ⟩
      sym (h x) ∙ h x ∙ path                    ≡⟨ ∙-assoc _ _ _ ⟩
      (sym (h x) ∙ h x) ∙ path                  ≡⟨ ap₂ _∙_ (∙-invl (h x)) refl ⟩
      refl ∙ path                               ≡⟨ ∙-idl path ⟩
      path                                      ∎
```

<!--
```agda
split-surjection→is-hlevel
  : ∀ n (f : A → B) (s : (b : B) → fibre f b)
  → is-hlevel A n → is-hlevel B n
split-surjection→is-hlevel n f s = retract→is-hlevel n f (λ x → s x .fst) (λ x → s x .snd)
```
-->

### Isomorphisms and equivalences

Even though we know that [[univalence]] implies that $n$-types are
closed under equivalences, this does not apply to types in different
universe levels. However, the construction above *does*, since every
equivalence, having a two-sided inverse, is a split surjection.

```agda
iso→is-hlevel : (n : Nat) (f : A → B) → is-iso f → is-hlevel A n → is-hlevel B n
iso→is-hlevel n f im = retract→is-hlevel n f g h
  where open is-iso im renaming (from to g ; rinv to h)

Iso→is-hlevel : (n : Nat) → Iso B A → is-hlevel A n → is-hlevel B n
Iso→is-hlevel n (f , im) = retract→is-hlevel n g f h
  where open is-iso im renaming (from to g ; linv to h)

equiv→is-hlevel : (n : Nat) (f : A → B) → is-equiv f → is-hlevel A n → is-hlevel B n
equiv→is-hlevel n f eqv = iso→is-hlevel n f (is-equiv→is-iso eqv)

Equiv→is-hlevel : (n : Nat) → (B ≃ A) → is-hlevel A n → is-hlevel B n
Equiv→is-hlevel n f = equiv→is-hlevel n _ (Equiv.inverse f .snd)
```

<!--
```agda
is-hlevel-ap : ∀ n → A ≃ B → is-hlevel A n ≃ is-hlevel B n
is-hlevel-ap n f =
  prop-ext
    (is-hlevel-is-prop n)
    (is-hlevel-is-prop n)
    (Equiv→is-hlevel n (f e⁻¹))
    (Equiv→is-hlevel n f)
```
-->

## Functions into n-types

We can now prove that the $n$-types are closed under all type formers
whose identity types are "self-similar". While we have to handle the
base cases ourselves, closure under retracts can take care of the
inductive cases. Function extensionality implies that an identity
between functions is a function into identities:

```agda
Π-is-hlevel : ∀ {a b} {A : Type a} {B : A → Type b}
            → (n : Nat) (Bhl : (x : A) → is-hlevel (B x) n)
            → is-hlevel ((x : A) → B x) n
Π-is-hlevel 0 bhl = record
  { paths = λ x i a → bhl _ .paths (x a) i
  }
Π-is-hlevel 1 bhl f g i a = bhl a (f a) (g a) i
Π-is-hlevel (suc (suc n)) bhl f g = retract→is-hlevel (suc n)
  funext happly (λ x → refl)
  (Π-is-hlevel (suc n) λ x → bhl x (f x) (g x))
```

<!--
```agda
Π-is-hlevel'
  : ∀ {a b} {A : Type a} {B : A → Type b}
  → (n : Nat) (Bhl : (x : A) → is-hlevel (B x) n)
  → is-hlevel ({x : A} → B x) n
Π-is-hlevel' n bhl = retract→is-hlevel n
  (λ f {x} → f x) (λ f x → f) (λ _ → refl)
  (Π-is-hlevel n bhl)

Π-is-hlevel-inst
  : ∀ {a b} {A : Type a} {B : A → Type b}
  → (n : Nat) (Bhl : (x : A) → is-hlevel (B x) n)
  → is-hlevel (⦃ x : A ⦄ → B x) n
Π-is-hlevel-inst n bhl = retract→is-hlevel n
  (λ f ⦃ x ⦄ → f x) (λ f x → f ⦃ x ⦄) (λ _ → refl)
  (Π-is-hlevel n bhl)

Π-is-hlevel²
  : ∀ {a b c} {A : Type a} {B : A → Type b} {C : ∀ a → B a → Type c}
  → (n : Nat) (Bhl : (x : A) (y : B x) → is-hlevel (C x y) n)
  → is-hlevel (∀ x y → C x y) n
Π-is-hlevel² n w = Π-is-hlevel n λ _ → Π-is-hlevel n (w _)

Π-is-hlevel²'
  : ∀ {a b c} {A : Type a} {B : A → Type b} {C : ∀ a → B a → Type c}
  → (n : Nat) (Bhl : (x : A) (y : B x) → is-hlevel (C x y) n)
  → is-hlevel (∀ {x y} → C x y) n
Π-is-hlevel²' n w = Π-is-hlevel' n λ _ → Π-is-hlevel' n (w _)

Π-is-hlevel³
  : ∀ {a b c d} {A : Type a} {B : A → Type b} {C : ∀ a → B a → Type c}
      {D : ∀ a b → C a b → Type d}
  → (n : Nat) (Bhl : (x : A) (y : B x) (z : C x y) → is-hlevel (D x y z) n)
  → is-hlevel (∀ x y z → D x y z) n
Π-is-hlevel³ n w = Π-is-hlevel n λ _ → Π-is-hlevel² n (w _)

Π-is-hlevel³'
  : ∀ {a b c d} {A : Type a} {B : A → Type b} {C : ∀ a → B a → Type c}
      {D : ∀ a b → C a b → Type d}
  → (n : Nat) (Bhl : (x : A) (y : B x) (z : C x y) → is-hlevel (D x y z) n)
  → is-hlevel (∀ {x y z} → D x y z) n
Π-is-hlevel³' n w = Π-is-hlevel' n λ _ → Π-is-hlevel²' n (w _)
```
-->

By taking the codomain to be a constant family, we obtain that the
$n$-types are an *exponential ideal*: $A \to B$ is an $n$-type if $B$
is.

```agda
fun-is-hlevel : ∀ n → is-hlevel B n → is-hlevel (A → B) n
fun-is-hlevel n hl = Π-is-hlevel n λ _ → hl
```

## Sums of n-types

A similar argument, using the fact that `paths between pairs are pairs
of paths`{.Agda ident=Σ-path-iso}, shows that dependent sums are also
closed under h-levels.

```agda
Σ-is-hlevel
  : {B : A → Type ℓ'} (n : Nat)
  → is-hlevel A n → (∀ x → is-hlevel (B x) n)
  → is-hlevel (Σ A B) n
Σ-is-hlevel 0 acontr bcontr = record
  { centre = acontr .centre , bcontr _ .centre
  ; paths  = λ x → Σ-pathp
    (acontr .paths _)
    (is-prop→pathp (λ _ → is-contr→is-prop (bcontr _)) _ _)
  }

Σ-is-hlevel 1 aprop bprop (a , b) (a' , b') i =
  aprop a a' i , is-prop→pathp (λ i → bprop (aprop a a' i)) b b' i

Σ-is-hlevel {B = B} (suc (suc n)) h1 h2 (x , p) (y , q) =
  iso→is-hlevel (suc n) _ (Σ-path-iso .snd) $
    Σ-is-hlevel (suc n) (h1 x y) λ x → h2 y (subst B x p) q
```

Analogous to the case of dependent products and functions, a
non-dependent sum is a product.

```agda
×-is-hlevel : ∀ n → is-hlevel A n → is-hlevel B n → is-hlevel (A × B) n
×-is-hlevel n ahl bhl = Σ-is-hlevel n ahl (λ _ → bhl)
```

Similarly, `Lift`{.Agda} does not induce a change of h-levels, i.e. if
$A$ is an $n$-type in a universe $U$, then it's also an $n$-type in any
successor universe:

```agda
opaque
  Lift-is-hlevel : ∀ n → is-hlevel A n → is-hlevel (Lift ℓ' A) n
  Lift-is-hlevel n a-hl = retract→is-hlevel n lift lower (λ _ → refl) a-hl
```

<!--
```agda
  Lift-is-hlevel' : ∀ n → is-hlevel (Lift ℓ' A) n → is-hlevel A n
  Lift-is-hlevel' n lift-hl = retract→is-hlevel n lower lift (λ _ → refl) lift-hl
```
-->

Finally, we'll show that the `fibre`{.Agda}s of a function between
$n$-types are themselves $n$-types.

```agda
fibre-is-hlevel
  : ∀ n → is-hlevel A n → is-hlevel B n
  → (f : A → B) → ∀ b → is-hlevel (fibre f b) n
fibre-is-hlevel n Ah Bh f b = Σ-is-hlevel n Ah λ _ → Path-is-hlevel n Bh
```

## Automation

For the common case of proving that a composite type built out of pieces
with a known h-level has that same h-level, we can apply the helpers
above very uniformly. So uniformly, in fact, that Agda's instance
resolution mechanism can do it for us. However, since `is-hlevel`{.Agda}
is a _recursive_ definition which unfolds depending on the level, we
must introduce a record wrapper around this type which prevents
recursion. Otherwise we could not expect Agda to find instances in
scope.

```agda
record H-Level {ℓ} (T : Type ℓ) (n : Nat) : Type ℓ where
  constructor hlevel-instance
  field
    has-hlevel : is-hlevel T n
```

The canonical entry point for the search is `hlevel`{.Agda}, which turns
an instance argument of `H-Level`{.Agda} to an actual usable witness.
Note that the parameter $n$ is explicit: We can not expect Agda to
recover $n$ from the expected type of the application.

```agda
hlevel : ∀ {ℓ} {T : Type ℓ} n ⦃ x : H-Level T n ⦄ → is-hlevel T n
hlevel n ⦃ x ⦄ = H-Level.has-hlevel x
```

<!--
```agda
private variable
  S T : Type ℓ

module _ where
  open H-Level
  H-Level-is-prop : ∀ {n} → is-prop (H-Level T n)
  H-Level-is-prop {n = n} x y i .has-hlevel =
    is-hlevel-is-prop n (x .has-hlevel) (y .has-hlevel) i
```
-->

Because of the way we set up our search, the "leaves" in the instance
search must support _offsetting_ the index by any positive number:
Rather than defining an instance saying that e.g. $\bb{N}$ has h-level
2, we define an instance saying it has h-level $2+k$, for any choice of
$k$. This is done using the `basic-instance`{.Agda} helper:

```agda
basic-instance : ∀ {ℓ} {T : Type ℓ} n → is-hlevel T n → ∀ {k} → H-Level T (n + k)
basic-instance {T = T} n hl {k} =
  subst (H-Level T) (+-comm n k) (hlevel-instance (is-hlevel-+ n k hl))
  where
    +-comm : ∀ n k → k + n ≡ n + k
    +-comm zero k = go k where
      go : ∀ k → k + 0 ≡ k
      go zero = refl
      go (suc x) = ap suc (go x)
    +-comm (suc n) k = go n k ∙ ap suc (+-comm n k) where
      go : ∀ n k → k + suc n ≡ suc (k + n)
      go n zero = refl
      go n (suc k) = ap suc (go n k)

prop-instance : ∀ {ℓ} {T : Type ℓ} → is-prop T → ∀ {k} → H-Level T (suc k)
prop-instance {T = T} hl = hlevel-instance (is-prop→is-hlevel-suc hl)
```

We then have a family of instances for solving compound types, e.g.
function types, $\Sigma$-types, path types, lifts, etc.

```agda
instance opaque
  H-Level-pi
    : ∀ {n} {S : T → Type ℓ}
    → ⦃ ∀ {x} → H-Level (S x) n ⦄
    → H-Level (∀ x → S x) n
  H-Level-pi {n = n} .H-Level.has-hlevel = Π-is-hlevel n λ _ → hlevel n

  H-Level-⊤ : ∀ {n} → H-Level ⊤ n
  H-Level-⊤ {n = zero} = hlevel-instance (contr tt (λ x i → tt))
  H-Level-⊤ {n = suc n} = prop-instance λ x y i → tt

  H-Level-⊥ : ∀ {n} → H-Level ⊥ (suc n)
  H-Level-⊥ {n = n} = prop-instance λ x y → absurd x

  H-Level-pi'
    : ∀ {n} {S : T → Type ℓ}
    → ⦃ ∀ {x} → H-Level (S x) n ⦄
    → H-Level (∀ {x} → S x) n
  H-Level-pi' {n = n} .H-Level.has-hlevel = Π-is-hlevel' n λ _ → hlevel n

  H-Level-pi''
    : ∀ {n} {S : T → Type ℓ}
    → ⦃ ∀ {x} → H-Level (S x) n ⦄
    → H-Level (∀ ⦃ x ⦄ → S x) n
  H-Level-pi'' {n = n} .H-Level.has-hlevel = Π-is-hlevel-inst n λ _ → hlevel n

  H-Level-sigma
    : ∀ {n} {S : T → Type ℓ}
    → ⦃ H-Level T n ⦄ → ⦃ ∀ {x} → H-Level (S x) n ⦄
    → H-Level (Σ T S) n
  H-Level-sigma {n = n} .H-Level.has-hlevel =
    Σ-is-hlevel n (hlevel n) λ _ → hlevel n

  H-Level-PathP
    : ∀ {n} {S : I → Type ℓ} ⦃ s : H-Level (S i1) (suc n) ⦄ {x y}
    → H-Level (PathP S x y) n
  H-Level-PathP {n = n} .H-Level.has-hlevel = PathP-is-hlevel' n (hlevel (suc n)) _ _

  H-Level-Lift
    : ∀ {n} ⦃ s : H-Level T n ⦄ → H-Level (Lift ℓ T) n
  H-Level-Lift {n = n} .H-Level.has-hlevel = Lift-is-hlevel n (hlevel n)

  H-Level-is-contr : ∀ {n} {ℓ} {T : Type ℓ} → H-Level (is-contr T) (suc n)
  H-Level-is-contr = prop-instance is-contr-is-prop

  H-Level-is-equiv
    : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} {n}
    → H-Level (is-equiv f) (suc n)
  H-Level-is-equiv = prop-instance (is-equiv-is-prop _)
```

<!--
```agda
positive-hlevel : ∀ {ℓ} (T : Type ℓ) → Nat → Type _
positive-hlevel T n = ∀ {k} → H-Level T (n + k)
{-# INLINE positive-hlevel #-}
```
-->
