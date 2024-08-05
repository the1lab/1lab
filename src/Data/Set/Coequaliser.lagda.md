<!--
```agda
open import 1Lab.Reflection.Induction
open import 1Lab.Prelude

open import Data.Dec

open is-iso
```
-->

```agda
module Data.Set.Coequaliser where
```

<!--
```agda
private variable
  ℓ ℓ' : Level
  A B A' B' A'' B'' : Type ℓ
```
-->

# Set coequalisers {defines="set-coequaliser"}

In their most general form, colimits can be pictured as taking disjoint
unions and then "gluing together" some parts. The "gluing together" part
of that definition is where **coequalisers** come in: If you have
parallel maps $f, g : A \to B$, then the coequaliser $\rm{coeq}(f,g)$
can be thought of as "$B$, with the images of $f$ and $g$ identified".

```agda
data Coeq (f g : A → B) : Type (level-of A ⊔ level-of B) where
  inc    : B → Coeq f g
  glue   : ∀ x → inc (f x) ≡ inc (g x)
  squash : is-set (Coeq f g)
```

The universal property of coequalisers, being a type of colimit, is a
_mapping-out_ property: Maps _from_ $\rm{coeq}(f,g)$ are maps out of
$B$, satisfying a certain property. Specifically, for a map $h : B \to
C$, if we have $h \circ f = h \circ g$, then the map $f$ factors
(uniquely) through `inc`{.Agda}. The situation can be summarised with
the diagram below.

~~~{.quiver}
\[\begin{tikzcd}
  A & B & {\rm{coeq}(f,g)} \\
  && C
  \arrow["f", shift left=1, from=1-1, to=1-2]
  \arrow["g"', shift right=1, from=1-1, to=1-2]
  \arrow["{\rm{inc}}", from=1-2, to=1-3]
  \arrow["h"', from=1-2, to=2-3]
  \arrow["{\exists!}", dashed, from=1-3, to=2-3]
\end{tikzcd}\]
~~~

We refer to this unique factoring as `Coeq-rec`{.Agda}.

```agda
Coeq-rec
  : ∀ {ℓ} {C : Type ℓ} {f g : A → B} ⦃ _ : H-Level C 2 ⦄
  → (h : B → C)
  → (∀ x → h (f x) ≡ h (g x)) → Coeq f g → C
Coeq-rec h h-coeqs (inc x) = h x
Coeq-rec h h-coeqs (glue x i) = h-coeqs x i
Coeq-rec ⦃ cs ⦄ h h-coeqs (squash x y p q i j) =
  hlevel 2 (g x) (g y) (λ i → g (p i)) (λ i → g (q i)) i j
  where g = Coeq-rec ⦃ cs ⦄ h h-coeqs
```

An alternative phrasing of the desired universal property is
precomposition with `inc`{.Agda} induces an equivalence between the
"space of maps $B \to C$ which coequalise $f$ and $g$" and the maps
$\rm{coeq}(f,g) \to C$. In this sense, `inc`{.Agda} is the universal
map which coequalises $f$ and $g$.

<!--
This is hella confusing, because we need coeq-elim-prop to define
`Coeq-univ`, but `Coeq-univ` comes first in the "didactic order"!
-->

<div style="display: flex; flex-flow: column-reverse nowrap;">
<div>

To construct the map above, we used `Coeq-elim-prop`{.Agda}, which has
not yet been defined. It says that, to define a dependent function from
`Coeq`{.Agda} to a family of propositions, it suffices to define how it
acts on `inc`{.Agda}: The path constructions don't matter.

```agda
Coeq-elim-prop
  : ∀ {ℓ} {f g : A → B} {C : Coeq f g → Type ℓ}
  → (∀ x → is-prop (C x))
  → (∀ x → C (inc x))
  → ∀ x → C x
Coeq-elim-prop cprop cinc (inc x) = cinc x
```

Since C was assumed to be a family of propositions, we automatically get
the necessary coherences for `glue`{.Agda} and `squash`{.Agda}.

```agda
Coeq-elim-prop {f = f} {g = g} cprop cinc (glue x i) =
  is-prop→pathp (λ i → cprop (glue x i)) (cinc (f x)) (cinc (g x)) i
Coeq-elim-prop cprop cinc (squash x y p q i j) =
  is-prop→squarep (λ i j → cprop (squash x y p q i j))
    (λ i → g x) (λ i → g (p i)) (λ i → g (q i)) (λ i → g y) i j
  where g = Coeq-elim-prop cprop cinc
```

<!--
```agda
instance
  Inductive-Coeq
    : ∀ {ℓ ℓm} {f g : A → B} {P : Coeq f g → Type ℓ}
    → ⦃ _ : Inductive (∀ x → P (inc x)) ℓm ⦄
    → ⦃ _ : ∀ {x} → H-Level (P x) 1 ⦄
    → Inductive (∀ x → P x) ℓm
  Inductive-Coeq ⦃ i ⦄ = record
    { methods = i .Inductive.methods
    ; from    = λ f → Coeq-elim-prop (λ x → hlevel 1) (i .Inductive.from f)
    }

  Extensional-coeq-map
    : ∀ {ℓ ℓ' ℓ'' ℓr} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {f g : A → B}
    → ⦃ sf : Extensional (B → C) ℓr ⦄ ⦃ _ : H-Level C 2 ⦄
    → Extensional (Coeq f g → C) ℓr
  Extensional-coeq-map ⦃ sf ⦄ .Pathᵉ f g = sf .Pathᵉ (f ∘ inc) (g ∘ inc)
  Extensional-coeq-map ⦃ sf ⦄ .reflᵉ f = sf .reflᵉ (f ∘ inc)
  Extensional-coeq-map ⦃ sf ⦄ .idsᵉ .to-path h = funext $
    elim! (happly (sf .idsᵉ .to-path h))
  Extensional-coeq-map ⦃ sf ⦄ .idsᵉ .to-path-over p =
    is-prop→pathp (λ i → Pathᵉ-is-hlevel 1 sf (hlevel 2)) _ _

  Number-Coeq : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → ⦃ Number B ⦄ → {f g : A → B} → Number (Coeq f g)
  Number-Coeq {ℓ = ℓ} ⦃ b ⦄ .Number.Constraint n = Lift ℓ (b .Number.Constraint n)
  Number-Coeq ⦃ b ⦄ .Number.fromNat n ⦃ lift c ⦄ = inc (b .Number.fromNat n ⦃ c ⦄)
```
-->

</div>

<div>

Since "the space of maps $h : B \to C$ which coequalise $f$ and $g$" is
a bit of a mouthful, we introduce an abbreviation: Since a colimit is
defined to be a certain universal (co)cone, we call these
`Coeq-cone`{.Agda}s.

```agda
private
  coeq-cone : ∀ {ℓ} (f g : A → B) → Type ℓ → Type _
  coeq-cone {B = B} f g C = Σ[ h ∈ (B → C) ] (h ∘ f ≡ h ∘ g)
```

The universal property of `Coeq`{.Agda} then says that
`Coeq-cone`{.Agda} is equivalent to the maps $\rm{coeq}(f,g) \to C$,
and this equivalence is given by `inc`{.Agda}, the "universal
Coequalising map".

```agda
Coeq-univ : ∀ {ℓ} {C : Type ℓ} {f g : A → B} ⦃ _ : H-Level C 2 ⦄
          → is-equiv {A = Coeq f g → C} {B = coeq-cone f g C}
            (λ h → h ∘ inc , λ i z → h (glue z i))
Coeq-univ {C = C} {f = f} {g = g} =
  is-iso→is-equiv (iso cr' (λ x → refl) islinv) where
    cr' : coeq-cone f g C → Coeq f g → C
    cr' (f , f-coeqs) = Coeq-rec f (happly f-coeqs)

    islinv : is-left-inverse cr' (λ h → h ∘ inc , λ i z → h (glue z i))
    islinv f = trivial!
```

</div>
</div>

# Elimination

Above, we defined what it means to define a dependent function $(x :
\rm{coeq}(f,g)) \to C\ x$ when $C$ is a family of propositions, and
what it means to define a non-dependent function $\rm{coeq}(f,g) \to
C$. Now, we combine the two notions, and allow dependent elimination
into families of sets:

```agda
Coeq-elim : ∀ {ℓ} {f g : A → B} {C : Coeq f g → Type ℓ}
          → (∀ x → is-set (C x))
          → (ci : ∀ x → C (inc x))
          → (∀ x → PathP (λ i → C (glue x i)) (ci (f x)) (ci (g x)))
          → ∀ x → C x
Coeq-elim cset ci cg (inc x) = ci x
Coeq-elim cset ci cg (glue x i) = cg x i
Coeq-elim cset ci cg (squash x y p q i j) =
  is-set→squarep (λ i j → cset (squash x y p q i j))
    (λ i → g x) (λ i → g (p i)) (λ i → g (q i)) (λ i → g y) i j
  where g = Coeq-elim cset ci cg
```

<!--
```agda
Coeq-rec₂ : ∀ {ℓ} {f g : A → B} {f' g' : A' → B'} {C : Type ℓ}
          → is-set C
          → (ci : B → B' → C)
          → (∀ a x → ci (f x) a ≡ ci (g x) a)
          → (∀ a x → ci a (f' x) ≡ ci a (g' x))
          → Coeq f g → Coeq f' g' → C
Coeq-rec₂ cset ci r1 r2 (inc x) (inc y) = ci x y
Coeq-rec₂ cset ci r1 r2 (inc x) (glue y i) = r2 x y i
Coeq-rec₂ cset ci r1 r2 (inc x) (squash y z p q i j) = cset
  (Coeq-rec₂ cset ci r1 r2 (inc x) y)
  (Coeq-rec₂ cset ci r1 r2 (inc x) z)
  (λ j → Coeq-rec₂ cset ci r1 r2 (inc x) (p j))
  (λ j → Coeq-rec₂ cset ci r1 r2 (inc x) (q j))
  i j

Coeq-rec₂ cset ci r1 r2 (glue x i) (inc x₁) = r1 x₁ x i
Coeq-rec₂ {f = f} {g} {f'} {g'} cset ci r1 r2 (glue x i) (glue y j) =
  is-set→squarep (λ i j → cset)
    (λ j → r1 (f' y) x j)
    (λ j → r2 (f x) y j)
    (λ j → r2 (g x) y j)
    (λ j → r1 (g' y) x j)
    i j

Coeq-rec₂ {f = f} {g} {f'} {g'} cset ci r1 r2 (glue x i) (squash y z p q j k) =
  is-hlevel-suc 2 cset
    (go (glue x i) y) (go (glue x i) z)
    (λ j → go (glue x i) (p j))
    (λ j → go (glue x i) (q j))
    (λ i j → exp i j) (λ i j → exp i j)
    i j k
  where
    go = Coeq-rec₂ cset ci r1 r2
    exp : I → I → _
    exp l m = cset
      (go (glue x i) y) (go (glue x i) z)
      (λ j → go (glue x i) (p j))
      (λ j → go (glue x i) (q j))
      l m

Coeq-rec₂ cset ci r1 r2 (squash x y p q i j) z =
  cset (go x z) (go y z) (λ j → go (p j) z) (λ j → go (q j) z) i j
  where go = Coeq-rec₂ cset ci r1 r2

instance
  H-Level-coeq : ∀ {f g : A → B} {n} → H-Level (Coeq f g) (2 + n)
  H-Level-coeq = basic-instance 2 squash
```
-->

# Quotients {defines=quotient}

With dependent sums, we can recover quotients as a special case of
coequalisers. Observe that, by taking the total space of a relation $R :
A \to A \to \ty$, we obtain two projection maps which have as image all
of the possible related elements in $A$. By coequalising these
projections, we obtain a space where any related objects are identified:
the **quotient** $A/R$.

```agda
private
  tot : ∀ {ℓ} → (A → A → Type ℓ) → Type (level-of A ⊔ ℓ)
  tot {A = A} R = Σ[ x ∈ A ] Σ[ y ∈ A ] R x y

  /-left : ∀ {ℓ} {R : A → A → Type ℓ} → tot R → A
  /-left (x , _ , _) = x

  /-right : ∀ {ℓ} {R : A → A → Type ℓ} → tot R → A
  /-right (_ , x , _) = x
```
<!--
```agda
private variable
  R S T : A → A → Type ℓ
```
-->

We form the quotient as the aforementioned coequaliser of the two
projections from the total space of $R$:

```agda
_/_ : ∀ {ℓ ℓ'} (A : Type ℓ) (R : A → A → Type ℓ') → Type (ℓ ⊔ ℓ')
A / R = Coeq (/-left {R = R}) /-right

infixl 25 _/_

quot : ∀ {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'} {x y : A} → R x y
    → Path (A / R) (inc x) (inc y)
quot r = glue (_ , _ , r)
```

Using `Coeq-elim`{.Agda}, we can recover the elimination principle for
quotients:

```agda
Quot-elim : ∀ {ℓ} {B : A / R → Type ℓ}
          → (∀ x → is-set (B x))
          → (f : ∀ x → B (inc x))
          → (∀ x y (r : R x y) → PathP (λ i → B (quot r i)) (f x) (f y))
          → ∀ x → B x
Quot-elim bset f r = Coeq-elim bset f λ { (x , y , w) → r x y w }
```

::: {.definition #coequalisers-as-quotients}
Conversely, we can describe coequalisers in terms of quotients.
In order to form the coequaliser of $f, g : A \to B$, we interpret the
span formed by $f$ and $g$ as a binary relation on $B$: a witness
that $x, y : B$ are related is an element of the [[fibre]] of
$\langle f, g \rangle$ at $(x, y)$, that is an $a : A$ such that
$f(a) = x$ and $g(a) = y$.
:::

```agda
span→R
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f g : A → B)
  → B → B → Type (ℓ ⊔ ℓ')
span→R f g = curry (fibre ⟨ f , g ⟩)
```

We then recover the coequaliser of $f$ and $g$ as the quotient of $B$
by this relation.

```agda
Coeq≃quotient
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f g : A → B)
  → Coeq f g ≃ B / span→R f g
Coeq≃quotient {B = B} f g = Iso→Equiv is where
  is : Iso (Coeq f g) (B / span→R f g)
  is .fst = Coeq-rec inc λ a → quot (a , refl)
  is .snd .inv = Coeq-rec inc λ (_ , _ , a , p) →
    sym (ap (inc ∘ fst) p) ·· glue a ·· ap (inc ∘ snd) p
  is .snd .rinv = elim! λ _ → refl
  is .snd .linv = elim! λ _ → refl
```

<!--
```agda
inc-is-surjective : {f g : A → B} → is-surjective {B = Coeq f g} inc
inc-is-surjective (inc x) = inc (x , refl)
inc-is-surjective {f = f} {g = g} (glue x i) = is-prop→pathp
  (λ i → ∥_∥.squash {A = fibre Coeq.inc (glue x i)})
  (∥_∥.inc (f x , refl))
  (∥_∥.inc (g x , refl)) i
inc-is-surjective (squash x y p q i j) = is-prop→squarep
  (λ i j → ∥_∥.squash {A = fibre inc (squash x y p q i j)})
  (λ i → inc-is-surjective x)
  (λ j → inc-is-surjective (p j))
  (λ j → inc-is-surjective (q j))
  (λ i → inc-is-surjective y) i j
```
-->

## Effectivity {defines="congruence effectivity quotients-are-effective"}

The most well-behaved case of quotients is when $R : A \to A \to \ty$
takes values in propositions, is reflexive, transitive and symmetric (an
equivalence relation). In this case, we have that the quotient $A / R$
is **effective**: The map `quot`{.Agda} is an equivalence.

```agda
record Congruence {ℓ} (A : Type ℓ) ℓ' : Type (ℓ ⊔ lsuc ℓ') where
  field
    _∼_         : A → A → Type ℓ'
    has-is-prop : ∀ x y → is-prop (x ∼ y)
    reflᶜ : ∀ {x} → x ∼ x
    _∙ᶜ_  : ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z
    symᶜ  : ∀ {x y}   → x ∼ y → y ∼ x

  infixr 30 _∙ᶜ_

  relation = _∼_

  quotient : Type _
  quotient = A / _∼_
```

We will show this using an encode-decode method. For each $x : A$, we
define a type family $\rm{Code}_x(p)$, which represents an equality
$\rm{inc}(x) = y$. Importantly, the fibre over $\rm{inc}(y)$
will be $R(x, y)$, so that the existence of functions converting between
$\rm{Code}_x(y)$ and paths $\rm{inc}(x) = y$ is enough to
establish effectivity of the quotient.

```agda
  private
    Code : A → quotient → Prop ℓ'
    Code x = Quot-elim
      (λ x → n-Type-is-hlevel 1)
      (λ y → el (x ∼ y) (has-is-prop x y) {- 1 -})
      λ y z r →
        n-ua (prop-ext (has-is-prop _ _) (has-is-prop _ _)
          (λ z → z ∙ᶜ r)
          λ z → z ∙ᶜ (symᶜ r))
```

We do quotient induction into the `type of propositions`{.Agda
ident=Prop}, which by univalence `is a set`{.Agda ident=n-Type-is-hlevel}.
Since the fibre over $\rm{inc}(y)$ must be $R(x, y)$, that's what we
give for the `inc`{.Agda} constructor (`{- 1 -}`{.Agda}, above). For
this to respect the quotient, it suffices to show that, given $R(y,z)$,
we have $R(x,y) \Leftrightarrow R(x,z)$, which follows from the
assumption that $R$ is an equivalence relation (`{- 2 -}`{.Agda}).

```agda
    encode : ∀ x y (p : inc x ≡ y) → ∣ Code x y ∣
    encode x y p = subst (λ y → ∣ Code x y ∣) p reflᶜ

    decode : ∀ x y (p : ∣ Code x y ∣) → inc x ≡ y
    decode = elim! λ x y r → quot r
```

For `encode`{.Agda}, it suffices to transport the proof that $R$ is
reflexive along the given proof, and for decoding, we eliminate from the
quotient to a proposition. It boils down to establishing that $R(x,y)
\to \rm{inc}(x) \equiv \rm{inc}(y)$, which is what the
constructor `quot`{.Agda} says. Putting this all together, we get a
proof that equivalence relations are `effective`{.Agda}.

```agda
  is-effective : ∀ {x y : A} → is-equiv (quot {R = relation})
  is-effective {x = x} {y} =
    prop-ext (has-is-prop x y) (squash _ _) (decode x (inc y)) (encode x (inc y)) .snd
```

<!--
```agda
  effective : ∀ {x y : A} → Path quotient (inc x) (inc y) → x ∼ y
  effective = equiv→inverse is-effective
```
-->

<!--
```agda
Quot-op₂ : ∀ {C : Type ℓ} {T : C → C → Type ℓ'}
         → (∀ x → R x x) → (∀ y → S y y)
         → (_⋆_ : A → B → C)
         → ((a b : A) (x y : B) → R a b → S x y → T (a ⋆ x) (b ⋆ y))
         → A / R → B / S → C / T
Quot-op₂ Rr Sr op resp =
  Coeq-rec₂ squash (λ x y → inc (op x y))
    (λ { z (x , y , r) → quot (resp x y z z r (Sr z)) })
    λ { z (x , y , r) → quot (resp z z x y (Rr z) r) }

Discrete-quotient
  : ∀ {A : Type ℓ} (R : Congruence A ℓ')
  → (∀ x y → Dec (Congruence.relation R x y))
  → Discrete (Congruence.quotient R)
Discrete-quotient cong rdec {x} {y} =
  elim! {P = λ x → ∀ y → Dec (x ≡ y)} go _ _ where
  go : ∀ x y → Dec (inc x ≡ inc y)
  go x y with rdec x y
  ... | yes xRy = yes (quot xRy)
  ... | no ¬xRy = no λ p → ¬xRy (Congruence.effective cong p)

open Congruence

Congruence-pullback
  : ∀ {ℓa ℓb ℓ} {A : Type ℓa} {B : Type ℓb}
  → (A → B) → Congruence B ℓ → Congruence A ℓ
Congruence-pullback {ℓ = ℓ} {A = A} f R = f*R where
  module R = Congruence R
  f*R : Congruence A ℓ
  f*R ._∼_ x y = f x R.∼ f y
  f*R .has-is-prop x y = R.has-is-prop _ _
  f*R .reflᶜ = R.reflᶜ
  f*R ._∙ᶜ_ f g = f R.∙ᶜ g
  f*R .symᶜ f = R.symᶜ f
```
-->

## Relation to surjections {defines="surjections-are-quotient-maps"}

As mentioned in the definition of [[surjection]], we can view a cover $f
: A \to B$ as expressing a way of _gluing together_ the type $B$ by
adding paths between the elements of $A$. When $A$ and $B$ are sets,
this sounds a lot like a quotient! And, indeed, we can prove that every
surjection induces an equivalence between its codomain and a quotient of
its domain.

First, we define the **kernel pair** of a function $f : A \to B$, the
congruence on $A$ defined to be _identity under $f$._

```agda
Kernel-pair
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → is-set B → (A → B)
  → Congruence A ℓ'
Kernel-pair b-set f ._∼_ a b = f a ≡ f b
Kernel-pair b-set f .has-is-prop x y = b-set (f x) (f y)
Kernel-pair b-set f .reflᶜ = refl
Kernel-pair b-set f ._∙ᶜ_  = _∙_
Kernel-pair b-set f .symᶜ  = sym
```

We can then set about proving that, if $f : A \epi B$ is a surjection
into a set, then $B$ is the quotient of $A$ under the kernel pair of
$f$.


```agda
surjection→is-quotient
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → (b-set : is-set B)
  → (f : A ↠ B)
  → B ≃ Congruence.quotient (Kernel-pair b-set (f .fst))
```

<!--
```agda
surjection→is-quotient {A = A} {B} b-set (f , surj) =
  _ , injective-surjective→is-equiv! g'-inj g'-surj
  where

  private module c = Congruence (Kernel-pair b-set f)
```
-->

The construction is pretty straightforward: each fibre $(a, p) : f^*x$
defines an element $[a] : A/\ker f$; If we have another fibre $(b, q)$,
then $[a] = [b]$ because

$$
f(a) \overset{p}{\equiv} x \overset{q}{\equiv} f(b)
$$,

so the function $f^*x \to A/\ker f$ is constant, and factors through the
[[propositional truncation]] $\| f^*x \|$.

```agda
  g₀ : ∀ {x} → fibre f x → c.quotient
  g₀ (a , p) = inc a

  abstract
    g₀-const : ∀ {x} (p₁ p₂ : fibre f x) → g₀ p₁ ≡ g₀ p₂
    g₀-const (_ , p) (_ , q) = quot (p ∙ sym q)

  g₁ : ∀ {x} → ∥ fibre f x ∥ → c.quotient
  g₁ f = ∥-∥-rec-set (hlevel 2) g₀ g₀-const f
```

Since each $\| f^*x \|$ is inhabited, all of these functions glue
together to give a function $B \to A/\ker f$. A simple calculation shows
that this function is both injective and surjective; since its codomain
is a set, that means it's an equivalence.

```agda
  g' : B → c.quotient
  g' x = g₁ (surj x)

  g'-inj : injective g'
  g'-inj {x} {y} = ∥-∥-elim₂ {P = λ a b → g₁ a ≡ g₁ b → x ≡ y}
    (λ _ _ → fun-is-hlevel 1 (b-set _ _))
    (λ (_ , p) (_ , q) r → sym p ∙ c.effective r ∙ q)
    (surj x) (surj y)

  g'-surj : is-surjective g'
  g'-surj x = do
    (y , p) ← inc-is-surjective x
    pure (f y , ap g₁ (squash (surj (f y)) (inc (y , refl))) ∙ p)
```

<!--
```agda
private module test where
  variable C : Type ℓ

  _ : {f g : A / R → B} ⦃ _ : H-Level B 2 ⦄
    → ((x : A) → f (inc x) ≡ g (inc x)) → f ≡ g
  _ = ext

  _ : {f g : (A × B) / R → C} ⦃ _ : H-Level C 2 ⦄
    → ((x : A) (y : B) → f (inc (x , y)) ≡ g (inc (x , y)))
    → f ≡ g
  _ = ext
```
-->

## Closures {defines="congruence-closure"}

We define the reflexive, transitive and symmetric closure of a relation
$R$ and prove that it induces the same quotient as $R$.

```agda
module _ {ℓ ℓ'} {A : Type ℓ} (R : A → A → Type ℓ') where
  data Closure : A → A → Type (ℓ ⊔ ℓ') where
    inc : ∀ {x y} → R x y → Closure x y
    Closure-refl : ∀ {x} → Closure x x
    Closure-trans : ∀ {x y z} → Closure x y → Closure y z → Closure x z
    Closure-sym : ∀ {x y} → Closure y x → Closure x y
    squash : ∀ {x y} → is-prop (Closure x y)

  Closure-congruence : Congruence A _
  Closure-congruence .Congruence._∼_ = Closure
  Closure-congruence .Congruence.has-is-prop _ _ = squash
  Closure-congruence .Congruence.reflᶜ = Closure-refl
  Closure-congruence .Congruence._∙ᶜ_ = Closure-trans
  Closure-congruence .Congruence.symᶜ = Closure-sym
```

<!--
```agda
  unquoteDecl Closure-elim-prop = make-elim-n 1 Closure-elim-prop (quote Closure)

  Closure-rec-congruence
    : ∀ {ℓ''} (S : Congruence A ℓ'') (let module S = Congruence S)
    → (∀ {x y} → R x y → x S.∼ y)
    → ∀ {x y} → Closure x y → x S.∼ y
  Closure-rec-congruence S h = Closure-elim-prop
    {P = λ {x} {y} _ → x S.∼ y}
    (λ _ → S.has-is-prop _ _)
    h S.reflᶜ (λ _ q _ r → q S.∙ᶜ r) (λ _ r → S.symᶜ r)
    where module S = Congruence S

  Closure-rec-≡
    : ∀ {ℓ'} {D : Type ℓ'}
    → ⦃ H-Level D 2 ⦄
    → (f : A → D)
    → (∀ {x y} → R x y → f x ≡ f y)
    → ∀ {x y} → Closure x y → f x ≡ f y
  Closure-rec-≡ f = Closure-rec-congruence (Kernel-pair (hlevel 2) f)
```
-->

```agda
Closure-quotient
  : ∀ {ℓ ℓ'} {A : Type ℓ} (R : A → A → Type ℓ')
  → A / R ≃ A / Closure R
Closure-quotient {A = A} R = Iso→Equiv is where
  is : Iso (A / R) (A / Closure R)
  is .fst = Coeq-rec inc λ (a , b , r) → quot (inc r)
  is .snd .inv = Coeq-rec inc λ (a , b , r) → Closure-rec-≡ _ inc quot r
  is .snd .rinv = elim! λ _ → refl
  is .snd .linv = elim! λ _ → refl
```

<!--
```agda
instance
  Closure-H-Level
    : ∀ {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'} {x y} {n}
    → H-Level (Closure R x y) (suc n)
  Closure-H-Level = prop-instance squash
```
-->
