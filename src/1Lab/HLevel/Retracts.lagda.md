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
module 1Lab.HLevel.Retracts where
```

# Closure of h-levels

<!--
```
private variable
  ℓ ℓ' : Level
  A B C : Type ℓ
  F G : A → Type ℓ
```
-->

The homotopy [[n-types]] have many closure properties. A trivial example is
that they are closed under equivalences, since any property of types is
preserved by equivalence (This is the [[univalence axiom]]). More
interesting is that they are closed under retractions:

## Retractions

The first base case is to show that **retracts** of contractible types
are contractible. We say that $A$ is a retract of $B$ if there is a map
$f : A \to B$ admitting a `right-inverse`{.Agda}. This means that $f$ is
the retraction (the left inverse). The proof is a calculation:

```agda
retract→is-contr : (f : A → B) (g : B → A)
                 → is-left-inverse f g
                 → is-contr A
                 → is-contr B
retract→is-contr f g h isC .centre = f (isC .centre)
retract→is-contr f g h isC .paths x =
  f (isC .centre) ≡⟨ ap f (isC .paths _) ⟩
  f (g x)         ≡⟨ h _ ⟩
  x               ∎
```

We must also show that retracts of _propositions_ are propositions:

```agda
retract→is-prop : (f : A → B) (g : B → A)
                → is-left-inverse f g
                → is-prop A
                → is-prop B
retract→is-prop f g h propA x y =
  x       ≡⟨ sym (h _) ⟩
  f (g x) ≡⟨ ap f (propA _ _) ⟩
  f (g y) ≡⟨ h _ ⟩
  y       ∎
```

Now we can extend this to all h-levels by induction:

```agda
retract→is-hlevel : (n : Nat) (f : A → B) (g : B → A)
                 → is-left-inverse f g
                 → is-hlevel A n
                 → is-hlevel B n
retract→is-hlevel 0 = retract→is-contr
retract→is-hlevel 1 = retract→is-prop
```

For the base case, we already have the proofs we're after. For the
inductive case, a function `g x ≡ g y → x ≡ y` is constructed, which is
a left inverse to the function `ap g`. Then, since `(g x) ≡ (g y)` is a
homotopy (n+1)-type, we conclude that so is `x ≡ y`.

```agda
retract→is-hlevel (suc (suc n)) f g h hlevel x y =
  retract→is-hlevel (suc n) sect (ap g) inv (hlevel (g x) (g y))
  where
    sect : g x ≡ g y → x ≡ y
    sect path =
      x       ≡⟨ sym (h _) ⟩
      f (g x) ≡⟨ ap f path ⟩
      f (g y) ≡⟨ h _ ⟩
      y       ∎
```

The left inverse is constructed out of `ap`{.Agda} and the given
homotopy.

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

The proof that this function _does_ invert `ap g` on the left is boring,
but it consists mostly of symbol pushing. The only non-trivial step, and
the key to the proof, is the theorem that `homotopies behave like
natural transformations`{.Agda ident=homotopy-natural}: We can flip `ap
f (ap g path)` and `h y` to get a pair of paths that annihilates on the
left, and `path` on the right.

### Equivalences

It follows, without a use of univalence, that h-levels are closed under
isomorphisms and equivalences:

```agda
iso→is-hlevel : (n : Nat) (f : A → B) → is-iso f → is-hlevel A n → is-hlevel B n
iso→is-hlevel n f is-iso =
  retract→is-hlevel n f (is-iso .is-iso.inv)
                       (is-iso .is-iso.rinv)

equiv→is-hlevel : (n : Nat) (f : A → B) → is-equiv f → is-hlevel A n → is-hlevel B n
equiv→is-hlevel n f eqv = iso→is-hlevel n f (is-equiv→is-iso eqv)

is-hlevel≃ : (n : Nat) → (B ≃ A) → is-hlevel A n → is-hlevel B n
is-hlevel≃ n f = iso→is-hlevel n (equiv→inverse (f .snd)) (iso (f .fst) (equiv→unit (f .snd)) (equiv→counit (f .snd)))

Iso→is-hlevel : (n : Nat) → Iso B A → is-hlevel A n → is-hlevel B n
Iso→is-hlevel n (f , isic) = iso→is-hlevel n (isic .is-iso.inv) $
  iso f (isic .is-iso.linv) (isic .is-iso.rinv)
```

## Functions into n-types

Since h-levels are closed under retracts, The type of functions into a
homotopy n-type is itself a homotopy n-type.

```agda
Π-is-hlevel : ∀ {a b} {A : Type a} {B : A → Type b}
            → (n : Nat) (Bhl : (x : A) → is-hlevel (B x) n)
            → is-hlevel ((x : A) → B x) n
Π-is-hlevel 0 bhl = contr (λ x → bhl _ .centre) λ x i a → bhl _ .paths (x a) i
Π-is-hlevel 1 bhl f g i a = bhl a (f a) (g a) i
Π-is-hlevel (suc (suc n)) bhl f g =
  retract→is-hlevel (suc n) funext happly (λ x → refl)
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

By taking `B` to be a type rather than a family, we get that `A → B`
also inherits the h-level of B.

```agda
fun-is-hlevel
  : ∀ {a b} {A : Type a} {B : Type b}
  → (n : Nat) → is-hlevel B n
  → is-hlevel (A → B) n
fun-is-hlevel n hl = Π-is-hlevel n (λ _ → hl)
```

## Sums of n-types

A similar argument, using the fact that `paths between pairs are pairs
of paths`{.Agda ident=Σ-path-iso}, shows that dependent sums are also
closed under h-levels.

```agda
Σ-is-hlevel : {A : Type ℓ} {B : A → Type ℓ'} (n : Nat)
            → is-hlevel A n
            → ((x : A) → is-hlevel (B x) n)
            → is-hlevel (Σ A B) n
Σ-is-hlevel 0 acontr bcontr =
  contr (acontr .centre , bcontr _ .centre)
    λ x → Σ-pathp (acontr .paths _)
                  (is-prop→pathp (λ _ → is-contr→is-prop (bcontr _)) _ _)

Σ-is-hlevel 1 aprop bprop (a , b) (a' , b') i =
  (aprop a a' i) , (is-prop→pathp (λ i → bprop (aprop a a' i)) b b' i)

Σ-is-hlevel {B = B} (suc (suc n)) h1 h2 x y =
  iso→is-hlevel (suc n)
    (is-iso.inverse (Σ-path-iso .snd) .is-iso.inv)
    (Σ-path-iso .snd)
    (Σ-is-hlevel (suc n) (h1 (fst x) (fst y)) λ x → h2 _ _ _)
```

Similarly for dependent products and functions, there is a non-dependent
version of `Σ-is-hlevel`{.Agda} that expresses closure of h-levels under
`_×_`{.Agda}.

```agda
×-is-hlevel : ∀ {a b} {A : Type a} {B : Type b}
            → (n : Nat)
            → is-hlevel A n → is-hlevel B n
            → is-hlevel (A × B) n
×-is-hlevel n ahl bhl = Σ-is-hlevel n ahl (λ _ → bhl)
```

Similarly, `Lift`{.Agda} does not induce a change of h-levels, i.e. if
$A$ is an $n$-type in a universe $U$, then it's also an $n$-type in any
successor universe:

```agda
opaque
  Lift-is-hlevel : ∀ {a b} {A : Type a}
                → (n : Nat)
                → is-hlevel A n
                → is-hlevel (Lift b A) n
  Lift-is-hlevel n a-hl = retract→is-hlevel n lift Lift.lower (λ _ → refl) a-hl
```

Likewise, if the `Lift`{.Agda} of $A$ is an $n$-type, then $A$ must also
be an n-type.

```agda
  Lift-is-hlevel'
    : ∀ {a b} {A : Type a}
    → (n : Nat)
    → is-hlevel (Lift b A) n
    → is-hlevel A n
  Lift-is-hlevel' n lift-hl = retract→is-hlevel n Lift.lower lift (λ _ → refl) lift-hl
```

The `fibre`{.Agda}s of a function between $n$-types are $n$-types.

```agda
fibre-is-hlevel
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → (n : Nat)
  → is-hlevel A n → is-hlevel B n
  → (f : A → B)
  → ∀ b → is-hlevel (fibre f b) n
fibre-is-hlevel n Ah Bh f b = Σ-is-hlevel n Ah λ _ → Path-is-hlevel n Bh
```

# Automation

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

private variable
  S T : Type ℓ

module _ where
  open H-Level
  H-Level-is-prop : ∀ {n} → is-prop (H-Level T n)
  H-Level-is-prop {n = n} x y i .has-hlevel =
    is-hlevel-is-prop n (x .has-hlevel) (y .has-hlevel) i
```

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
```

<!--
```agda
positive-hlevel : ∀ {ℓ} (T : Type ℓ) → Nat → Type _
positive-hlevel T n = ∀ {k} → H-Level T (n + k)
{-# INLINE positive-hlevel #-}
```
-->
