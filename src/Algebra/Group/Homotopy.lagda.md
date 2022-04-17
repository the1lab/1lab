```agda
open import 1Lab.Prelude

open import Algebra.Semigroup
open import Algebra.Monoid
open import Algebra.Group
open import Algebra.Magma

open import Data.Set.Truncation

module Algebra.Group.Homotopy where
```

<!--
```agda
private variable
  ℓ : Level
  A : Type ℓ
```
-->

# Homotopy Groups

Given a `pointed type`{.Agda ident=Type∙} $(A, a)$ we refer to the type
$a = a$ as the **loop space of $A$**, and refer to it in short as
$\Omega A$. Since we always have $\id{refl} : a = a$, $\Omega A$ is
_itself_ a pointed type, the construction can be iterated, a process
which we denote $\Omega^n A$.

```agda
Ω^ : Nat → Type∙ ℓ → Type∙ ℓ
Ω^ zero A    = A
Ω^ (suc n) (A , x) with Ω^ n (A , x)
... | (T , x) = Path T x x , refl
```

For positive $n$, we can give $\Omega^n A$ a `Group`{.Agda} structure,
obtained by [truncating](1Lab.HIT.Truncation.Set.html) the higher
groupoid structure that $A$ is equiped with. We call the sequence
$\pi_n(A)$ the **homotopy groups** of $A$, but remark that the indexing
used by `πₙ`{.Agda} is off by 1: `πₙ 0 A` is the **fundamental group**
$\pi_1(A)$.

```agda
πₙ₊₁ : Nat → Type∙ ℓ → Group ℓ
πₙ₊₁ n t .fst = ∥ Ω^ (suc n) t .fst ∥₀
πₙ₊₁ n t .snd =
  make-group squash
    (inc refl)
    (∥-∥₀-map₂ _∙_)
    (∥-∥₀-map sym)
```

As mentioned above, the group structure is given entirely by the
groupoid structure of types: The neutral element is `refl`{.Agda}, the
group operation is `path concatenation`{.Agda ident=_∙_}, and the
inverses are given by `inverting paths`{.Agda ident=sym}.

```agda
    (∥-∥₀-elim₃ (λ _ _ _ → is-prop→is-set (squash _ _))
      λ x y z i → inc (∙-assoc x y z (~ i)))
    (∥-∥₀-elim (λ _ → is-prop→is-set (squash _ _))
      λ x i → inc (∙-inv-l x i))
    (∥-∥₀-elim (λ _ → is-prop→is-set (squash _ _))
      λ x i → inc (∙-inv-r x i))
    (∥-∥₀-elim (λ _ → is-prop→is-set (squash _ _))
      λ x i → inc (∙-id-l x i))
```

A direct cubical transcription of the Eckmann-Hilton argument tells us
that path concatenation is commutative for $\Omega^{n + 2} A$ is
commutative, independent of $A$.

```agda
Ωⁿ⁺²-is-abelian-group
  : ∀ {ℓ} {A : Type∙ ℓ} (n : Nat) (p q : Ω^ (2 + n) A .fst)
  → p ∙ q ≡ q ∙ p
Ωⁿ⁺²-is-abelian-group n p q =
  transport
    (λ i → ap (λ x → ∙-id-r x i) p ∙ ap (λ x → ∙-id-l x i) q
         ≡ ap (λ x → ∙-id-l x i) q ∙ ap (λ x → ∙-id-r x i) p)
    (λ i → (λ j → p (j ∧ ~ i) ∙ q (j ∧ i))
         ∙ (λ j → p (~ i ∨ j) ∙ q (i ∨ j)))
```

Lifting this result through the set truncation establishes that
$\pi_{n+2}$ is an Abelian group:

```agda
πₙ₊₂-is-abelian-group : ∀ {ℓ} {A : Type∙ ℓ} (n : Nat)
                   → is-abelian-group (πₙ₊₁ (1 + n) A)
πₙ₊₂-is-abelian-group {A = A} n =
  ∥-∥₀-elim₂ (λ x y → is-prop→is-set (squash _ _))
             (λ x y i → inc (Ωⁿ⁺²-is-abelian-group n x y i))
```

## Deloopings

A natural question to ask, given that all pointed types have a
fundamental group, is whether every group arises as the fundamental
group of some type. The answer to this question is "yes", but in the
annoying way that questions like these tend to be answered: Given any
group $G$, we construct a type $B(G)$ with $\pi_1(B(G)) \equiv G$. We
call $B(G)$ the **delooping** of $G$.

```agda
module _ {ℓ} (G : Group ℓ) where
  module G = Group-on (G .snd)
  open G

  data Deloop : Type ℓ where
    base    : Deloop
    squash  : is-groupoid Deloop
    path    : G .fst → base ≡ base
    path-sq : (x y : G .fst) → Square refl (path x) (path (x ⋆ y)) (path y)

  instance
    H-Level-Deloop : ∀ {n} → H-Level Deloop (3 + n)
    H-Level-Deloop = basic-instance 3 squash
```

The delooping is constructed as a higher inductive type. We have a
generic `base`{.Agda} point, and a constructor expressing that
`Deloop`{.Agda} is a groupoid; Since it is a groupoid, it has a set of
loops `point ≡ point`: this is necessary, since otherwise we would not
be able to prove that $\pi_1(B(G)) \equiv G$. We then have the
"interesting" higher constructors: `path`{.Agda} lets us turn any
element of $G$ to a path `point ≡ point`, and `path-sq`{.Agda} expresses
that `path`{.Agda} is a group homomorphism. More specifically,
`path-sq`{.Agda} fills the square below:

~~~{.quiver}
\[\begin{tikzcd}
  \bullet && \bullet \\
  \\
  \bullet && \bullet
  \arrow["{\id{refl}}"', from=1-1, to=3-1]
  \arrow["{\id{path}(x)}", from=1-1, to=1-3]
  \arrow["{\id{path}(y)}", from=1-3, to=3-3]
  \arrow["{\id{path}(x \star y)}"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

Using the `uniqueness result for double composition`{.Agda
ident=··-unique}, we derive that `path`{.Agda} is a homomorphism in the
traditional sense:

```agda
  abstract
    path-∙ : ∀ x y → path (x ⋆ y) ≡ path x ∙ path y
    path-∙ x y i j =
      ··-unique refl (path x) (path y)
        (path (x ⋆ y)    , path-sq x y)
        (path x ∙ path y , ∙-filler _ _)
        i .fst j
```

<details>
<summary>
And the standard argument shows that `path`{.Agda}, being a group
homomorphism, preserves the group identity.
</summary>

```agda
    path-unit : path unit ≡ refl
    path-unit =
      path unit                               ≡⟨ sym (∙-id-r _) ⟩
      path unit ∙ refl                        ≡⟨ ap₂ _∙_ refl (sym (∙-inv-r _))  ⟩
      path unit ∙ path unit ∙ sym (path unit) ≡⟨ ∙-assoc _ _ _ ∙ ap₂ _∙_ (sym (path-∙ _ _)) refl ⟩
      path (unit ⋆ unit) ∙ sym (path unit)    ≡⟨ ap₂ _∙_ (ap path G.idr) refl ⟩
      path unit ∙ sym (path unit)             ≡⟨ ∙-inv-r _  ⟩
      refl                                    ∎
```
</details>

We define an elimination principle for `Deloop`{.Agda}, which has a
monstruous type since it works in full generality. We'll also need an
eliminator into propositions later, so we define that now.

```agda
  Deloop-elim
    : ∀ {ℓ'} (P : Deloop → Type ℓ')
    → (∀ x → is-hlevel (P x) 3)
    → (p : P base)
    → (ploop : ∀ x → PathP (λ i → P (path x i)) p p)
    → ( ∀ x y
        → SquareP (λ i j → P (path-sq x y i j))
                  (λ _ → p) (ploop x) (ploop (x ⋆ y)) (ploop y))
    → ∀ x → P x
  Deloop-elim P grpd pp ploop psq base = pp
  Deloop-elim P grpd pp ploop psq (path x i) = ploop x i
  Deloop-elim P grpd pp ploop psq (path-sq x y i j) = psq x y i j
  Deloop-elim P grpd pp ploop psq (squash a b p q r s i j k) =
    is-hlevel→is-hlevel-dep 2 grpd
      (g a) (g b) (λ i → g (p i)) (λ i → g (q i))
      (λ i j → g (r i j)) (λ i j → g (s i j)) (squash a b p q r s) i j k
    where
      g = Deloop-elim P grpd pp ploop psq

  Deloop-elim-prop
    : ∀ {ℓ'} (P : Deloop → Type ℓ')
    → (∀ x → is-prop (P x))
    → P base
    → ∀ x → P x
  Deloop-elim-prop P pprop p =
    Deloop-elim P
      (λ x → is-prop→is-hlevel-suc {n = 2} (pprop x)) p
      (λ x → is-prop→pathp (λ i → pprop (path x i)) p p)
      (λ x y → is-prop→squarep (λ i j → pprop (path-sq x y i j)) _ _ _ _)
```

We can then proceed to characterise the type `point ≡ x` by an
encode-decode argument. We define a family `Code`{.Agda}, where the
fibre over `base`{.Agda} is definitionally `G`; Then we exhibit inverse
equivalences `base ≡ x → Code x` and `Code x → base ≡ x`, which fit
together to establish `G ≡ (base ≡ base)`. First, to define
`Code`{.Agda}, we perform induction on `Deloop`{.Agda}:

```agda
  Code : Deloop → Set ℓ
  Code =
    Deloop-elim _
      (λ _ → hlevel 3)
      (G .fst , Group-on.has-is-set (G .snd))
      (λ x → n-ua (map x))
      λ x y → n-Type-square (transport (sym Square≡··) (lemma x y))
```

Since we must map into a type which is known to be a groupoid, we map to
the type of `Set`{.Agda}s; Since the collection of $n$-types is a
$(n+1)$-type, this is a groupoid. To arrange that the fibre over
`base`{.Agda} is `G`, we give `G` as the argument for `base`{.Agda} in
the elimination. This locks us into giving a family of automorphisms
`map : G → G ≡ G` for the `path`{.Agda} constructor; The constructor
`path-sq`{.Agda} then requires that `map` be a homomorphism from $G$ to
$\id{Aut}(G)$.

```agda
    where
      map : ∀ x → G .fst ≃ G .fst
      map x = Iso→Equiv (_⋆ x , p) where
        open is-iso

        p : is-iso (_⋆ x)
        p .inv = _⋆ x ⁻¹
        p .rinv x = sym G.associative ·· ap₂ G._⋆_ refl G.inversel ·· G.idr
        p .linv x = sym G.associative ·· ap₂ G._⋆_ refl G.inverser ·· G.idr
```

We take $y \mapsto y \star x$ as the definition of the map, which is an
automorphism of $G$ since it is invertible by $y \mapsto y \star
x^{-1}$, and it preserves composition by associativity of $\star$, as is
shown in the lemma below.

```agda
      lemma : ∀ x y → ua (map x) ∙ ua (map y) ≡ ua (map (x ⋆ y))
      lemma x y =
        ua (map x) ∙ ua (map y) ≡⟨ sym ua∙ ⟩
        ua (map x ∙e map y)     ≡⟨ ap ua (Σ-prop-path is-equiv-is-prop (funext λ z → sym (Group-on.associative (G .snd)))) ⟩
        ua (map (x ⋆ y))        ∎
```

We then define the encoding and decoding functions. The encoding
function `encode`{.Agda} is given by lifting a path from `Deloop`{.Agda}
to `Code`{.Agda}. For decoding, we do induction on `Deloop`{.Agda} with
`Code x .fst → base ≡ x` as the motive.

```agda
  encode : ∀ x → base ≡ x → ∣ Code x ∣
  encode x p = subst (λ x → ∣ Code x ∣) p unit

  decode : ∀ x → ∣ Code x ∣ → base ≡ x
  decode = Deloop-elim _
    (λ _ → hlevel 3)
```

With this motive, the type of what we must give for `base`{.Agda}
reduces to `G → base ≡ base`, for which `path`{.Agda} suffices; The
`path`{.Agda} case is handled by `path-sq`{.Agda}, and the
`path-sq`{.Agda} case is automatic.

```agda
    path
    (λ x → ua→ λ a → path-sq _ _)
    (λ x y → is-set→squarep (λ i j → hlevel 2) _ _ _ _)
```

Proving that these are inverses finishes the proof. For one direction,
we use path induction to reduce to the case `decode base (encode base
refl) ≡ refl`; A quick argument tells us that `encode base refl`{.Agda}
is the group identity, and since `path`{.Agda} is a group homomorphism,
we have `path unit = refl`, as required.

```agda
  encode→decode : ∀ {x} (p : base ≡ x) → decode x (encode x p) ≡ p
  encode→decode p =
    J (λ y p → decode y (encode y p) ≡ p)
      (ap path (transport-refl _) ∙ path-unit)
      p
```

In the other direction, we do induction on deloopings; Since the motive
is a family of propositions, we can use `Deloop-elim-prop`{.Agda} instead
of the full `Deloop-elim`{.Agda}, which reduces the goal to proving $1
\star 1 = 1$.

```agda
  decode→encode : ∀ x (c : ∣ Code x ∣) → encode x (decode x c) ≡ c
  decode→encode =
    Deloop-elim-prop
      (λ x → (c : ∣ Code x ∣) → encode x (decode x c) ≡ c)
      (λ x → Π-is-hlevel 1 λ _ → Code x .is-tr _ _)
      λ c → transport-refl _ ∙ G.idl
```

This completes the proof, and lets us establish that the fundamental
group of `Deloop`{.Agda} is `G`, which is what we wanted.

```
  G≃ΩB : G .fst ≃ (base ≡ base)
  G≃ΩB = Iso→Equiv (path , iso (encode base) encode→decode (decode→encode base))

  G≡π₁B : G ≡ πₙ₊₁ 0 (Deloop , base)
  G≡π₁B = sip Group-univalent
    ( G≃ΩB ∙e (_ , ∥-∥₀-idempotent (squash base base))
    , record { pres-⋆ = λ x y i → inc (path-∙ x y i) })
```
