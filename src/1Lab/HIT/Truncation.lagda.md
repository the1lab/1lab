---
definition: |
  We construct propositional truncations, the reflections of a type into
  the universe of propositions.
---
<!--
```agda
open import 1Lab.Reflection.Induction
open import 1Lab.Reflection.HLevel
open import 1Lab.HLevel.Closure
open import 1Lab.Path.Reasoning
open import 1Lab.Type.Sigma
open import 1Lab.Inductive
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Data.Dec.Base
```
-->

```agda
module 1Lab.HIT.Truncation where
```

# Propositional truncation {defines="propositional-truncation"}

Let $A$ be a type. The **propositional truncation** of $A$ is a type
which represents the [[proposition]] "A is inhabited". In MLTT,
propositional truncations can not be constructed without postulates,
even in the presence of impredicative prop. However, Cubical Agda
provides a tool to define them: _higher inductive types_.

```agda
data ∥_∥ {ℓ} (A : Type ℓ) : Type ℓ where
  inc    : A → ∥ A ∥
  squash : is-prop ∥ A ∥
```

The two constructors that generate `∥_∥`{.Agda} state precisely that the
truncation is inhabited when `A` is (`inc`{.Agda}), and that it is a
proposition (`squash`{.Agda}).

```agda
is-prop-∥-∥ : ∀ {ℓ} {A : Type ℓ} → is-prop ∥ A ∥
is-prop-∥-∥ = squash
```

<!--
```agda
instance
  H-Level-truncation : ∀ {n} {ℓ} {A : Type ℓ} → H-Level ∥ A ∥ (suc n)
  H-Level-truncation = prop-instance squash
```
-->

The eliminator for `∥_∥`{.Agda} says that you can eliminate onto $P$
whenever it is a family of propositions, by providing a case for
`inc`{.Agda}.

```agda
∥-∥-elim : ∀ {ℓ ℓ'} {A : Type ℓ}
             {P : ∥ A ∥ → Type ℓ'}
         → ((x : _) → is-prop (P x))
         → ((x : A) → P (inc x))
         → (x : ∥ A ∥) → P x
∥-∥-elim pprop incc (inc x) = incc x
∥-∥-elim pprop incc (squash x y i) =
  is-prop→pathp (λ j → pprop (squash x y j)) (∥-∥-elim pprop incc x)
                                             (∥-∥-elim pprop incc y)
                                             i
```

<!--
```agda
∥-∥-elim₂ : ∀ {ℓ ℓ₁ ℓ₂} {A : Type ℓ} {B : Type ℓ₁}
              {P : ∥ A ∥ → ∥ B ∥ → Type ℓ₂}
          → (∀ x y → is-prop (P x y))
          → (∀ x y → P (inc x) (inc y))
          → ∀ x y → P x y
∥-∥-elim₂ {A = A} {B} {P} pprop work x y = go x y where
  go : ∀ x y → P x y
  go (inc x) (inc x₁) = work x x₁
  go (inc x) (squash y y₁ i) =
    is-prop→pathp (λ i → pprop (inc x) (squash y y₁ i))
                  (go (inc x) y) (go (inc x) y₁) i

  go (squash x x₁ i) z =
    is-prop→pathp (λ i → pprop (squash x x₁ i) z)
                  (go x z) (go x₁ z) i

∥-∥-rec : ∀ {ℓ ℓ'} {A : Type ℓ} {P : Type ℓ'}
        → is-prop P
        → (A → P)
        → (x : ∥ A ∥) → P
∥-∥-rec pprop = ∥-∥-elim (λ _ → pprop)

∥-∥-out : ∀ {ℓ} {A : Type ℓ} → is-prop A → ∥ A ∥ → A
∥-∥-out ap = ∥-∥-rec ap λ x → x

∥-∥-rec₂ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ''} {P : Type ℓ'}
         → is-prop P
         → (A → B → P)
         → (x : ∥ A ∥) (y : ∥ B ∥) → P
∥-∥-rec₂ pprop = ∥-∥-elim₂ (λ _ _ → pprop)

∥-∥-out! : ∀ {ℓ} {A : Type ℓ} ⦃ _ : H-Level A 1 ⦄ → ∥ A ∥ → A
∥-∥-out! = ∥-∥-out (hlevel 1)

instance
  Inductive-∥∥
    : ∀ {ℓ ℓ' ℓm} {A : Type ℓ} {P : ∥ A ∥ → Type ℓ'} ⦃ i : Inductive (∀ x → P (inc x)) ℓm ⦄
    → ⦃ _ : ∀ {x} → H-Level (P x) 1 ⦄
    → Inductive (∀ x → P x) ℓm
  Inductive-∥∥ ⦃ i ⦄ = record
    { methods = i .Inductive.methods
    ; from    = λ f → ∥-∥-elim (λ x → hlevel 1) (i .Inductive.from f)
    }

  Dec-∥∥ : ∀ {ℓ} {A : Type ℓ} → ⦃ Dec A ⦄ → Dec ∥ A ∥
  Dec-∥∥ ⦃ yes a ⦄ = yes (inc a)
  Dec-∥∥ ⦃ no ¬a ⦄ = no (rec! ¬a)
```
-->

The propositional truncation can be called the **free proposition** on a
type, because it satisfies the universal property that a [[left
adjoint]] would have. Specifically, let `B` be a proposition. We have:

```agda
∥-∥-univ : ∀ {ℓ} {A : Type ℓ} {B : Type ℓ}
         → is-prop B → (∥ A ∥ → B) ≃ (A → B)
∥-∥-univ {A = A} {B = B} bprop = Iso→Equiv (inc' , iso rec (λ _ → refl) beta) where
  inc' : (x : ∥ A ∥ → B) → A → B
  inc' f x = f (inc x)

  rec : (f : A → B) → ∥ A ∥ → B
  rec f (inc x) = f x
  rec f (squash x y i) = bprop (rec f x) (rec f y) i

  beta : _
  beta f = funext (∥-∥-elim (λ _ → is-prop→is-set bprop _ _) (λ _ → refl))
```

Furthermore, as required of a free construction, the propositional
truncation extends to a functor:

```agda
∥-∥-map : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
        → (A → B) → ∥ A ∥ → ∥ B ∥
∥-∥-map f (inc x)        = inc (f x)
∥-∥-map f (squash x y i) = squash (∥-∥-map f x) (∥-∥-map f y) i
```

<!--
```agda
∥-∥-map₂ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
         → (A → B → C) → ∥ A ∥ → ∥ B ∥ → ∥ C ∥
∥-∥-map₂ f (inc x) (inc y)  = inc (f x y)
∥-∥-map₂ f (squash x y i) z = squash (∥-∥-map₂ f x z) (∥-∥-map₂ f y z) i
∥-∥-map₂ f x (squash y z i) = squash (∥-∥-map₂ f x y) (∥-∥-map₂ f x z) i
```
-->

Using the propositional truncation, we can define the **existential
quantifier** as a truncated `Σ`{.Agda}.

```agda
∃ : ∀ {a b} (A : Type a) (B : A → Type b) → Type _
∃ A B = ∥ Σ A B ∥
```

<!--
```agda
∃-syntax : ∀ {a b} (A : Type a) (B : A → Type b) → Type _
∃-syntax = ∃

syntax ∃-syntax A (λ x → B) = ∃[ x ∈ A ] B
infix 5 ∃-syntax
```
-->

Note that if $P$ is already a proposition, then truncating it does
nothing:

```agda
is-prop→equiv∥-∥ : ∀ {ℓ} {P : Type ℓ} → is-prop P → P ≃ ∥ P ∥
is-prop→equiv∥-∥ pprop = prop-ext pprop squash inc (∥-∥-out pprop)
```

In fact, an alternative definition of `is-prop`{.Agda} is given by "being
equivalent to your own truncation":

```agda
is-prop≃equiv∥-∥ : ∀ {ℓ} {P : Type ℓ}
               → is-prop P ≃ (P ≃ ∥ P ∥)
is-prop≃equiv∥-∥ {P = P} =
  prop-ext is-prop-is-prop eqv-prop is-prop→equiv∥-∥ inv
  where
    inv : (P ≃ ∥ P ∥) → is-prop P
    inv eqv = equiv→is-hlevel 1 ((eqv e⁻¹) .fst) ((eqv e⁻¹) .snd) squash

    eqv-prop : is-prop (P ≃ ∥ P ∥)
    eqv-prop x y = Σ-path (λ i p → squash (x .fst p) (y .fst p) i)
                          (is-equiv-is-prop _ _ _)
```

:::{.definition #merely alias="mere"}
Throughout the 1Lab, we use the words "mere" and "merely" to modify a
type to mean its propositional truncation. This terminology is adopted
from the HoTT book. For example, a type $X$ is said _merely equivalent_
to $Y$ if the type $\| X \equiv Y \|$ is inhabited.
:::

## Maps into sets

The elimination principle for $\| A \|$ says that we can only use the
$A$ inside in a way that _doesn't matter_: the motive of elimination
must be a family of propositions, so our use of $A$ must not matter in a
very strong sense. Often, it's useful to relax this requirement
slightly: Can we map out of $\| A \|$ using a _constant_ function?

The answer is yes, provided we're mapping into a [[set]]! In that case,
the [[image]] of $f$ is a proposition, so that we can map from
$\| A \| \to \im f \to B$.
In the [next section](#maps-into-groupoids), we'll see a more general
method for mapping into types that aren't sets.

From the discussion in [1Lab.Counterexamples.Sigma], we know the
definition of image, or more properly of $(-1)$-image:

[1Lab.Counterexamples.Sigma]: 1Lab.Counterexamples.Sigma.html

```agda
image : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → Type _
image {A = A} {B = B} f = Σ[ b ∈ B ] ∃[ a ∈ A ] (f a ≡ b)
```

To see that the `image`{.Agda} indeed implements the concept of image,
we define a way to factor any map through its image. By the definition
of image, we have that the map `f-image`{.Agda} is always surjective,
and since `∃` is a family of props, the first projection out of
`image`{.Agda} is an embedding. Thus we factor a map $f$ as $A \epi \im
f \mono B$.

```agda
f-image
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → (f : A → B) → A → image f
f-image f x = f x , inc (x , refl)
```

We now prove the theorem that will let us map out of a propositional
truncation using a constant function into sets: if $B$ is a set, and $f
: A \to B$ is a constant function, then $\im f$ is a
proposition.

```agda
is-constant→image-is-prop
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → is-set B
  → (f : A → B) → (∀ x y → f x ≡ f y) → is-prop (image f)
```

This is intuitively true (if the function is constant, then there is at
most one thing in the image!), but formalising it turns out to be
slightly tricky, and the requirement that $B$ be a set is perhaps
unexpected.

A sketch of the proof is as follows. Suppose that we have some $(a, x)$
and $(b, y)$ in the image. We know, morally, that $x$ (respectively $y$) give us
some $f^*(a) : A$ and $p : f(f^*a) = a$ (resp $q : f(f^*(b)) = b$) ---
which would establish that $a \equiv b$, as we need, since we have $a =
f(f^*(a)) = f(f^*(b)) = b$, where the middle equation is by constancy of
$f$ --- but $p$ and $q$ are hidden under propositional truncations, so
we crucially need to use the fact that $B$ is a set so that $a = b$ is a
proposition.

```agda
is-constant→image-is-prop bset f fconst (a , x) (b , y) =
  Σ-prop-path (λ _ → squash)
    (∥-∥-elim₂ (λ _ _ → bset _ _)
      (λ { (f*a , p) (f*b , q) → sym p ·· fconst f*a f*b ·· q }) x y)
```

Using the image factorisation, we can project from a propositional
truncation onto a set using a constant map.

```agda
∥-∥-rec-set : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
            → is-set B
            → (f : A → B)
            → (∀ x y → f x ≡ f y)
            → ∥ A ∥ → B
∥-∥-rec-set {A = A} {B} bset f fconst x =
  ∥-∥-elim {P = λ _ → image f}
    (λ _ → is-constant→image-is-prop bset f fconst) (f-image f) x .fst
```

<!--
```agda
∥-∥-rec-set!
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} ⦃ _ : H-Level B 2 ⦄
  → (f : A → B) (c : ∀ x y → f x ≡ f y)
  → ∥ A ∥ → B
∥-∥-rec-set! {A = A} f c x = go x .fst where
  go : ∥ A ∥ → image f
  go (inc x)        = f x , inc (x , refl)
  go (squash x y i) = is-constant→image-is-prop (hlevel 2) f c (go x) (go y) i
```
-->

## Maps into groupoids

We can push this idea further: as discussed in [@Kraus:2015], in general,
functions $\| A \| \to B$ are equivalent to **coherently constant**
functions $A \to B$. This involves an infinite tower of conditions,
each relating to the previous one, which isn't something we can easily
formulate in the language of type theory.

However, when $B$ is an $n$-type, it is enough to ask for the first $n$
levels of the tower. In the case of sets, we've [seen](#maps-into-sets)
that the naïve notion of constancy is enough. We now deal with the case
of [[groupoids]], which requires an additional step: we ask for a function
$f : A \to B$ equipped with a witness of constancy $\rm{const}_{x,y} :
f x \equiv f y$ *and* a coherence $\rm{coh}_{x,y,z} : \rm{const}_{x,y}
\bullet \rm{const}_{y,z} \equiv \rm{const}_{x,z}$.

This time, we cannot hope to show that the image of $f$ is a proposition:
the image of a map $\top \to S^1$ is $S^1$. Instead, we use the following
higher inductive type, which can be thought of as the "codiscrete groupoid"
on $A$:

```agda
data ∥_∥³ {ℓ} (A : Type ℓ) : Type ℓ where
  inc : A → ∥ A ∥³
  iconst : ∀ a b → inc a ≡ inc b
  icoh : ∀ a b c → PathP (λ i → inc a ≡ iconst b c i) (iconst a b) (iconst a c)
  squash : is-groupoid ∥ A ∥³
```

The recursion principle for this type says exactly that any
coherently constant function into a groupoid factors through $\| A \|^3$!

```agda
∥-∥³-rec
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → is-groupoid B
  → (f : A → B)
  → (fconst : ∀ x y → f x ≡ f y)
  → (∀ x y z → fconst x y ∙ fconst y z ≡ fconst x z)
  → ∥ A ∥³ → B
∥-∥³-rec {A = A} {B} bgrpd f fconst fcoh = go where
  go : ∥ A ∥³ → B
  go (inc x) = f x
  go (iconst a b i) = fconst a b i
  go (icoh a b c i j) = ∙→square (sym (fcoh a b c)) i j
  go (squash x y a b p q i j k) = bgrpd
    (go x) (go y)
    (λ i → go (a i)) (λ i → go (b i))
    (λ i j → go (p i j)) (λ i j → go (q i j))
    i j k
```

All that remains to show is that $\| A \|^3$ is a proposition^[in fact, it's
even a *propositional truncation* of $A$, in that it satisfies the same
universal property as $\| A \|$], which mainly requires writing more elimination
principles.

<!--
```agda
∥-∥³-elim-set
  : ∀ {ℓ} {A : Type ℓ} {ℓ'} {P : ∥ A ∥³ → Type ℓ'}
  → (∀ a → is-set (P a))
  → (f : (a : A) → P (inc a))
  → (∀ a b → PathP (λ i → P (iconst a b i)) (f a) (f b))
  → ∀ a → P a
unquoteDef ∥-∥³-elim-set = make-elim-n 2 ∥-∥³-elim-set (quote ∥_∥³)

∥-∥³-elim-prop
  : ∀ {ℓ} {A : Type ℓ} {ℓ'} {P : ∥ A ∥³ → Type ℓ'}
  → (∀ a → is-prop (P a))
  → (f : (a : A) → P (inc a))
  → ∀ a → P a
unquoteDef ∥-∥³-elim-prop = make-elim-n 1 ∥-∥³-elim-prop (quote ∥_∥³)
```
-->

```agda
∥-∥³-is-prop : ∀ {ℓ} {A : Type ℓ} → is-prop ∥ A ∥³
∥-∥³-is-prop = is-contr-if-inhabited→is-prop $
  ∥-∥³-elim-prop (λ _ → hlevel 1)
    (λ a → contr (inc a) (∥-∥³-elim-set (λ _ → squash _ _) (iconst a) (icoh a)))
```

Hence we get the desired recursion principle for the usual propositional
truncation.

```agda
∥-∥-rec-groupoid
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → is-groupoid B
  → (f : A → B)
  → (fconst : ∀ x y → f x ≡ f y)
  → (∀ x y z → fconst x y ∙ fconst y z ≡ fconst x z)
  → ∥ A ∥ → B
∥-∥-rec-groupoid bgrpd f fconst fcoh =
  ∥-∥³-rec bgrpd f fconst fcoh ∘ ∥-∥-rec ∥-∥³-is-prop inc
```

<details>
<summary>
As we hinted at above, this method generalises (externally) to $n$-types;
we sketch the details of the next level for the curious reader.
</summary>

The next coherence involves a tetrahedron all of whose faces are $\rm{coh}$,
or, since we're doing cubical type theory, a "cubical tetrahedron":

~~~{.quiver}
\[\begin{tikzcd}
	a &&& a \\
	& b & b \\
	& c & d \\
	a &&& a
	\arrow[""{name=0, anchor=center, inner sep=0}, from=3-2, to=3-3]
	\arrow[""{name=1, anchor=center, inner sep=0}, Rightarrow, no head, from=2-2, to=2-3]
	\arrow[""{name=2, anchor=center, inner sep=0}, from=2-3, to=3-3]
	\arrow[from=2-2, to=3-2]
	\arrow[from=1-4, to=2-3]
	\arrow[""{name=3, anchor=center, inner sep=0}, from=1-1, to=2-2]
	\arrow[Rightarrow, no head, from=1-1, to=1-4]
	\arrow[""{name=4, anchor=center, inner sep=0}, from=4-4, to=3-3]
	\arrow[""{name=5, anchor=center, inner sep=0}, Rightarrow, no head, from=1-4, to=4-4]
	\arrow[""{name=6, anchor=center, inner sep=0}, from=4-1, to=3-2]
	\arrow[Rightarrow, no head, from=4-1, to=1-1]
	\arrow[Rightarrow, no head, from=4-1, to=4-4]
	\arrow["{\rm{coh}_{b,c,d}}"{description}, draw=none, from=0, to=1]
	\arrow["{\rm{coh}_{a,b,d}}"{description}, draw=none, from=2, to=5]
	\arrow["{\rm{coh}_{a,c,d}}"{description}, draw=none, from=6, to=4]
	\arrow["{\rm{coh}_{a,b,c}}"{description}, draw=none, from=3, to=6]
\end{tikzcd}\]
~~~

```agda
data ∥_∥⁴ {ℓ} (A : Type ℓ) : Type ℓ where
  inc : A → ∥ A ∥⁴
  iconst : ∀ a b → inc a ≡ inc b
  icoh : ∀ a b c → PathP (λ i → inc a ≡ iconst b c i) (iconst a b) (iconst a c)
  iassoc : ∀ a b c d → PathP (λ i → PathP (λ j → inc a ≡ icoh b c d i j)
                                          (iconst a b) (icoh a c d i))
                             (icoh a b c) (icoh a b d)
  squash : is-hlevel ∥ A ∥⁴ 4

∥-∥⁴-rec
  : ∀ {ℓ} {A : Type ℓ} {ℓ'} {B : Type ℓ'}
  → is-hlevel B 4
  → (f : A → B)
  → (fconst : ∀ a b → f a ≡ f b)
  → (fcoh : ∀ a b c → PathP (λ i → f a ≡ fconst b c i) (fconst a b) (fconst a c))
  → (∀ a b c d → PathP (λ i → PathP (λ j → f a ≡ fcoh b c d i j)
                                    (fconst a b) (fcoh a c d i))
                       (fcoh a b c) (fcoh a b d))
  → ∥ A ∥⁴ → B
unquoteDef ∥-∥⁴-rec = make-rec-n 4 ∥-∥⁴-rec (quote ∥_∥⁴)
```
</details>

<!--
```agda
open import Meta.Idiom
open import Meta.Bind

instance
  Map-∥∥ : Map (eff ∥_∥)
  Map-∥∥ .Map.map = ∥-∥-map

  Idiom-∥∥ : Idiom (eff ∥_∥)
  Idiom-∥∥ .Idiom.pure = inc
  Idiom-∥∥ .Idiom._<*>_ {A = A} {B = B} = go where
    go : ∥ (A → B) ∥ → ∥ A ∥ → ∥ B ∥
    go (inc f) (inc x) = inc (f x)
    go (inc f) (squash x y i) = squash (go (inc f) x) (go (inc f) y) i
    go (squash f g i) y = squash (go f y) (go g y) i

  Bind-∥∥ : Bind (eff ∥_∥)
  Bind-∥∥ .Bind._>>=_ {A = A} {B = B} = go where
    go : ∥ A ∥ → (A → ∥ B ∥) → ∥ B ∥
    go (inc x) f = f x
    go (squash x y i) f = squash (go x f) (go y f) i
```
-->
