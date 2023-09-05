<!--
```agda
open import 1Lab.Prelude
open import 1Lab.Rewrite

open import Algebra.Group.Homotopy
open import Algebra.Group.Cat.Base
open import Algebra.Group.Ab
open import Algebra.Group

open import Cat.Base

open import Data.Set.Truncation
```
-->

```agda
module Homotopy.Space.Delooping where
```

# Deloopings {defines="delooping"}

A natural question to ask, given that all pointed types have a
fundamental group, is whether every group arises as the fundamental
group of some type. The answer to this question is "yes", but in the
annoying way that questions like these tend to be answered: Given any
group $G$, we construct a type $\B{G}$ with $\pi_1(\B{G}) \equiv G$. We
call $\B{G}$ the **delooping** of $G$.

<!--
```agda
module _ {ℓ} (G : Group ℓ) where
  module G = Group-on (G .snd)
  open G
```
-->

```agda
  data Deloop : Type ℓ where
    base    : Deloop
    path    : ⌞ G ⌟ → base ≡ base
    path-sq : (x y : ⌞ G ⌟) → Square refl (path x) (path (x ⋆ y)) (path y)
    squash  : is-groupoid Deloop
```

<!--
```
  private instance
    H-Level-Deloop : ∀ {n} → H-Level Deloop (3 + n)
    H-Level-Deloop = basic-instance 3 squash
```
-->

The delooping is constructed as a higher inductive type. We have a
generic `base`{.Agda} point, and a constructor expressing that
`Deloop`{.Agda} is a groupoid; Since it is a groupoid, it has a set of
loops `point ≡ point`: this is necessary, since otherwise we would not
be able to prove that $\pi_1(\B{G}) \equiv G$. We then have the
"interesting" higher constructors: `path`{.Agda} lets us turn any
element of $G$ to a path `point ≡ point`, and `path-sq`{.Agda} expresses
that `path`{.Agda} is a group homomorphism. More specifically,
`path-sq`{.Agda} fills the square below:

~~~{.quiver}
\[\begin{tikzcd}
  \bullet && \bullet \\
  \\
  \bullet && \bullet
  \arrow["{\refl}"', from=1-1, to=3-1]
  \arrow["{\rm{path}(x)}", from=1-1, to=1-3]
  \arrow["{\rm{path}(y)}", from=1-3, to=3-3]
  \arrow["{\rm{path}(x \star y)}"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

Using the `uniqueness result for double composition`{.Agda
ident=··-unique}, we derive that `path`{.Agda} is a homomorphism in the
traditional sense:

```agda
  abstract
    path-∙ : ∀ x y → path (x ⋆ y) ≡ path x ∙ path y
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
      path unit                               ≡⟨ sym (∙-idr _) ⟩
      path unit ∙ ⌜ refl ⌝                    ≡˘⟨ ap¡ (∙-invr _)  ⟩
      path unit ∙ path unit ∙ sym (path unit) ≡⟨ ∙-assoc _ _ _ ∙ ap₂ _∙_ (sym (path-∙ _ _)) refl ⟩
      path ⌜ unit ⋆ unit ⌝ ∙ sym (path unit)  ≡⟨ ap! G.idr ⟩
      path unit ∙ sym (path unit)             ≡⟨ ∙-invr _  ⟩
      refl                                    ∎
```
</details>

We define an elimination principle for `Deloop`{.Agda}, which has the
following monstruous type since it works for mapping into arbitrary
groupoids. As usual, if we're mapping into a family of types that's more
truncated (i.e. a family of sets or propositions), some of the higher
cases become automatic.

```agda
  Deloop-elim
    : ∀ {ℓ'} (P : Deloop → Type ℓ')
    → (∀ x → is-groupoid (P x))
    → (p : P base)
    → (ploop : ∀ x → PathP (λ i → P (path x i)) p p)
    → ( ∀ x y
        → SquareP (λ i j → P (path-sq x y i j))
                  (λ _ → p) (ploop x) (ploop (x ⋆ y)) (ploop y))
    → ∀ x → P x
```

<!--
```agda
  Deloop-elim P grpd pp ploop psq base = pp
  Deloop-elim P grpd pp ploop psq (path x i) = ploop x i
  Deloop-elim P grpd pp ploop psq (path-sq x y i j) = psq x y i j
  Deloop-elim P grpd pp ploop psq (squash a b p q r s i j k) =
    is-hlevel→is-hlevel-dep 2 grpd
      (g a) (g b) (λ i → g (p i)) (λ i → g (q i))
      (λ i j → g (r i j)) (λ i j → g (s i j)) (squash a b p q r s) i j k
    where
      g = Deloop-elim P grpd pp ploop psq

  Deloop-elim-set
    : ∀ {ℓ'} (P : Deloop → Type ℓ')
    → (∀ x → is-set (P x))
    → (p : P base)
    → (ploop : ∀ x → PathP (λ i → P (path x i)) p p)
    → ∀ x → P x
  Deloop-elim-set P pset p q = Deloop-elim P (λ x → is-hlevel-suc 2 (pset _)) p q
    λ x y → is-set→squarep (λ _ _ → pset _) _ _ _ _

  Deloop-elim-prop
    : ∀ {ℓ'} (P : Deloop → Type ℓ')
    → (∀ x → is-prop (P x))
    → P base → ∀ x → P x
  Deloop-elim-prop P pprop p =
    Deloop-elim P
      (λ x → is-prop→is-hlevel-suc {n = 2} (pprop x)) p
      (λ x → is-prop→pathp (λ i → pprop (path x i)) p p)
      (λ x y → is-prop→squarep (λ i j → pprop (path-sq x y i j)) _ _ _ _)
```
-->

We can then proceed to characterise the type `point ≡ x` by an
encode-decode argument. We define a family `Code`{.Agda}, where the
fibre over `base`{.Agda} is definitionally `G`; Then we exhibit inverse
equivalences `base ≡ x → Code x` and `Code x → base ≡ x`, which fit
together to establish `G ≡ (base ≡ base)`.

We'll want to define the family `Code` by induction on `Deloop`. First,
since we have to map into a [[groupoid]], we'll map into the type
$\set$, rather than $\ty$. This takes care of the truncation
constructor (which is hidden from the page since it is entirely
formulaic): let's tackle the rest in order. We can also handle the
`base`{.Agda} case, since `Code base = G` was already a part of our
specification.

```agda
  Code : Deloop → Set ℓ
  Code = go module Code where
    open is-iso

    base-case : Set ℓ
    ∣ base-case ∣    = ⌞ G ⌟
    base-case .is-tr = hlevel!
```

To handle the path case, we'll have to produce, given an element $x :
G$, an equivalence $G \simeq G$: by univalence, we can then lift this
equivalence to a path $G \equiv G$, which we can use as the
`path-case`{.Agda}. While there might be many maps $G \to (G \simeq G)$,
one is canonical: the [[Yoneda embedding]] map, sending $x$ to $y
\mapsto xy$.

```agda
    path-case : ⌞ G ⌟ → base-case ≡ base-case
    path-case x = n-ua eqv module path-case where
      rem₁ : is-iso (_⋆ x)
      rem₁ .inv = _⋆ x ⁻¹
      rem₁ .rinv x = cancelr inversel
      rem₁ .linv x = cancelr inverser

      eqv : ⌞ G ⌟ ≃ ⌞ G ⌟
      eqv .fst = _
      eqv .snd = is-iso→is-equiv rem₁

    open path-case
```

Finally, we can satisfy the coherence case `path-sq`{.Agda} by an
algebraic calculation on paths:

```agda
    coh : ∀ x y → Square refl (path-case x) (path-case (x ⋆ y)) (path-case y)
    coh x y = n-Type-square $ transport (sym Square≡double-composite-path) $
      ua (eqv x) ∙ ua (eqv y) ≡˘⟨ ua∙ ⟩
      ua (eqv x ∙e eqv y)     ≡⟨ ap ua (Σ-prop-path! (funext λ _ → sym associative)) ⟩
      ua (eqv (x ⋆ y))        ∎
```

<!--
```agda
    go : Deloop → Set ℓ
    go base = base-case
    go (path x i) = path-case x i
    go (path-sq x y i j) = coh x y i j
    go (squash x y p q α β i j k) =
      n-Type-is-hlevel 2 (Code x) (Code y)
        (λ i → Code (p i))     (λ i → Code (q i))
        (λ i j → Code (α i j)) (λ i j → Code (β i j))
        i j k
```
-->

We can then define the encoding and decoding functions. The encoding
function `encode`{.Agda} is given by lifting a path from `Deloop`{.Agda}
to `Code`{.Agda}. For decoding, we do induction on `Deloop`{.Agda} with
`Code x .fst → base ≡ x` as the motive.

```agda
  opaque
    encode : ∀ x → base ≡ x → ∣ Code x ∣
    encode x p = subst (λ x → ∣ Code x ∣) p unit

    decode : ∀ x → ∣ Code x ∣ → base ≡ x
    decode = Deloop-elim (λ x → ⌞ Code x ⌟ → base ≡ x) (λ _ → hlevel 3)
```

With this motive, the type of what we must give for `base`{.Agda}
reduces to `G → base ≡ base`, for which `path`{.Agda} suffices; The
`path`{.Agda} case is handled by `path-sq`{.Agda}, and the
`path-sq`{.Agda} case is automatic.

```agda
      path
      (λ x   → ua→ λ a → path-sq _ _)
      (λ x y → is-set→squarep (λ i j → hlevel 2) _ _ _ _)
```

<!--
```agda
    decode-base : decode base ≡rw path
    decode-base = make-rewrite refl
    {-# REWRITE decode-base #-}
```
-->

Proving that these are inverses finishes the proof. For one direction,
we use path induction to reduce to the case `decode base (encode base
refl) ≡ refl`; A quick argument tells us that `encode base refl`{.Agda}
is the group identity, and since `path`{.Agda} is a group homomorphism,
we have `path unit = refl`, as required.

```agda
  opaque
    unfolding encode decode

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

```agda
  G≃ΩB : ⌞ G ⌟ ≃ (base ≡ base)
  G≃ΩB = Iso→Equiv (decode base , iso (encode base) encode→decode (decode→encode base))

  G≡π₁B : G ≡ πₙ₊₁ 0 (Deloop , base)
  G≡π₁B = ∫-Path Groups-equational
    (total-hom (λ x → inc (path x))
      record { pres-⋆ = λ x y → ap ∥_∥₀.inc (path-∙ _ _) })
    (∙-is-equiv (G≃ΩB .snd) (∥-∥₀-idempotent (squash base base)))
```

<!--
```agda
  opaque
    inc-path-is-group-hom
      : is-group-hom (G .snd) (πₙ₊₁ 0 (Deloop , base) .snd) (λ x → inc (path x))
    inc-path-is-group-hom .is-group-hom.pres-⋆ x y = ap ∥_∥₀.inc (path-∙ _ _)

    encode-proj-is-group-hom
      : is-group-hom (πₙ₊₁ 0 (Deloop , base) .snd) (G .snd)
          (λ x → encode base (∥-∥₀-idempotent.proj (squash base base) x))
    encode-proj-is-group-hom = equiv-hom→inverse-hom Groups-equational {a = G} {b = πₙ₊₁ 0 (Deloop , base)}
        (_ , ∙-is-equiv (G≃ΩB .snd) (∥-∥₀-idempotent (squash base base)))
        (record { pres-⋆ = λ x y → ap ∥_∥₀.inc (path-∙ x y) })

  encode-is-group-hom : is-group-hom (π₁Groupoid {T = Deloop} {base} squash) (G .snd) (encode base)
  encode-is-group-hom .is-group-hom.pres-⋆ x y =
    encode-proj-is-group-hom .is-group-hom.pres-⋆ (inc x) (inc y)

instance
  H-Level-Deloop : ∀ {n} {ℓ} {G : Group ℓ} → H-Level (Deloop G) (3 + n)
  H-Level-Deloop {n} = basic-instance 3 squash
```
-->


## For abelian groups

```agda
module _ {ℓ} (G : Group ℓ) (ab : is-commutative-group G) where
  open Group-on (G .snd)
  open is-group-hom

  private
    opaque
      ∙-comm : (p q : Path (Deloop G) base base) → p ∙ q ≡ q ∙ p
      ∙-comm p q = Equiv.injective (Equiv.inverse (G≃ΩB G))
        (encode-is-group-hom G .pres-⋆ _ _ ·· ab _ _ ·· sym (encode-is-group-hom G .pres-⋆ _ _))

  winding : {x : Deloop G} → x ≡ x → ⌞ G ⌟
  winding {x = x} = go x module windingⁱ where
    hl : (x : Deloop G) → is-set (x ≡ x → ⌞ G ⌟)
    hl _ = hlevel!

    abstract
      coh : (x : ⌞ G ⌟) → PathP (λ i → path {G = G} x i ≡ path x i → ⌞ G ⌟) (encode G base) (encode G base)
      coh x = to-pathp $ funext λ p → transport-refl _ ∙ ap (encode G base) (
          transport-path p (sym (path x)) (sym (path x))
        ·· ap (path x ∙_) (∙-comm _ _)
        ·· ∙-cancell (sym (path x)) p)

    go : (x : Deloop G) → x ≡ x → ⌞ G ⌟
    go base       loop = encode G base loop
    go (path x i) loop = coh x i loop
    go (path-sq x y i j) loop = sq i j loop where
      sq : SquareP (λ i j → path-sq {G = G} x y i j ≡ path-sq x y i j → ⌞ G ⌟)
            (λ i → encode G base) (coh x) (coh (x ⋆ y)) (coh y)
      sq = is-set→squarep (λ _ _ → hl _) _ _ _ _
    go (squash x y p q α β i j k) loop =
      is-hlevel→is-hlevel-dep 2 (λ x → is-hlevel-suc 2 (hl x))
        (go x) (go y) (λ i → go (p i)) (λ j → go (q j))
        (λ i j → go (α i j)) (λ i j → go (β i j))
        (squash x y p q α β) i j k loop

  {-# DISPLAY windingⁱ.go x p = winding p #-}

  opaque
    winding-is-equiv : ∀ x → is-equiv (winding {x})
    winding-is-equiv = Deloop-elim-prop G _ (λ _ → is-equiv-is-prop _) (Equiv.inverse (G≃ΩB G) .snd)

  module winding {x} = Equiv (winding , winding-is-equiv x)

  pathᵇ : (x : Deloop G) → ⌞ G ⌟ → x ≡ x
  pathᵇ _ = winding.from
```

<!--
```agda
  -- Want: pathᵇ base ≡ path, definitionally
  -- Have: pathᵇ base is a projection from some opaque record
  -- Soln: Evil hack!
  opaque
    unfolding winding-is-equiv

    winding-is-equiv-base : winding-is-equiv base ≡rw Equiv.inverse (G≃ΩB G) .snd
    winding-is-equiv-base = make-rewrite prop!

  {-# REWRITE winding-is-equiv-base #-}

  _ : pathᵇ base ≡ path
  _ = refl -- MUST check!
```
-->

```agda
  pathᵇ-sq : ∀ (x : Deloop G) g h → Square refl (pathᵇ x g) (pathᵇ x (g ⋆ h)) (pathᵇ x h)
  pathᵇ-sq = Deloop-elim-prop G _
    (λ x → Π-is-hlevel² 1 λ g h → PathP-is-hlevel' {A = λ i → x ≡ pathᵇ x h i} 1
      (squash _ _) _ _)
    λ g h → path-sq g h
```
