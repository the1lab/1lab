---
talk: yes
slide-level: 2
---

# Cubical types in everyday life

::: author
Amélia Liao
:::

# The 1Lab

<!--
```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import 1Lab.Prelude hiding (Extensional ; uncurry ; id ; _∘_ ; _==_)

open import Data.Nat.Base hiding (_==_)
open import Data.Sum

module Talks.Topos2024 where

private variable
  ℓ ℓr : Level
  A B C : Type ℓ
  w x y z : A
  n k : Nat
  P : A → Type ℓ
  Q : (x : A) → P x → Type ℓ

private module _ where private
```
-->

::: incremental

* Library of formalised mathematics in Agda (think "alternate standard library")
* ... and reference website ("the $n\text{Lab}$ for $n = 1$")
* ... and testing ground for new Agda features (`opaque`{.kw}, revamped instance search, ...)

:::

. . .

Quite a lot of moving parts! The talk today: *usability*.

## HoTT

Types as $\infty$-groupoids means *any* identity type is possibly
non-trivial. This can be a problem!

. . .

```agda
  record Category o ℓ : Type (lsuc (o ⊔ ℓ)) where
    infixr 40 _∘_

    field
      Ob  : Type o
      Hom : Ob → Ob → Type ℓ
```

. . .

```agda
      id  : Hom x x
      _∘_ : Hom y z → Hom x y → Hom x z
```

. . .

```agda
      idr : (f : Hom x y) → f ∘ id ≡ f
      idl : (f : Hom x y) → id ∘ f ≡ f
      assoc : (f : Hom y z) (g : Hom x y) (h : Hom w x)
            → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
```

<!--
```agda
  instance
    Underlying-Category : ∀ {o ℓ} → Underlying (Category o ℓ)
    Underlying-Category = record { ⌞_⌟ = Category.Ob }
```
-->

. . .

Looks right!

---

Let's try slicing them. Fix a $\cC$ and $X : \cC$...

<!--
```agda
  module _ {o ℓ} (C : Category o ℓ) (X : ⌞ C ⌟) where
    open Category C
    private module C = Category
```
-->

```agda
    Slice : Category (o ⊔ ℓ) ℓ
    Slice .C.Ob = Σ[ Y ∈ C ] (Hom Y X)
    Slice .C.Hom (Y , y) (Z , z) = Σ[ h ∈ Hom Y Z ] y ≡ z ∘ h
```

. . .

```agda
    Slice .C.id {x , f} = id , sym (idr f)
    Slice .C._∘_ (f , p) (g , q) = f ∘ g ,
      q ∙ ap₂ _∘_ p refl ∙ sym (assoc _ _ _)
```

. . .

```agda
    Slice .C.idl (h , p) = idl h ,ₚ _
```

We're missing something!

. . .

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  {g \circ h} \&\& {(g \circ \mathrm{id}) \circ h} \\
  \\
  {g \circ h} \&\& {g \circ (\mathrm{id} \circ h)}
  \arrow["{(\mathrm{idr}\ g)\inv\ \circ\ h}"', from=1-1, to=1-3]
  \arrow["{\mathrm{refl}}"', from=1-1, to=3-1]
  \arrow["{\mathrm{assoc}\ g\ \mathrm{id}\ h}", from=1-3, to=3-3]
  \arrow["{g\ \circ\ (\mathrm{idl}\ h)}", from=3-3, to=3-1]
\end{tikzcd}\]
~~~

<!--
```agda
    Slice .C.idr {x , f} {y , g} (h , p) = idr _ ,ₚ _
    Slice .C.assoc _ _ _ = assoc _ _ _ ,ₚ _
```
-->

---

The issue lies in the identity types of `Hom`{.Agda}. To identify $f, g$ in

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  A \&\& B \\
  \\
  \& X
	\arrow[""{name=0, anchor=center, inner sep=0}, "f", curve={height=-12pt}, from=1-1, to=1-3]
	\arrow[""{name=1, anchor=center, inner sep=0}, "g"', curve={height=12pt}, from=1-1, to=1-3]
  \arrow["a"', from=1-1, to=3-2]
  \arrow["b", from=1-3, to=3-2]
  \arrow["r", shorten <=3pt, shorten >=3pt, Rightarrow, no head, from=0, to=1]
\end{tikzcd}\]

~~~

<!--
```agda
    _ : ∀ {(A , a) (B , b) : ⌞ Slice ⌟} {(f , p) (g , q) : Slice .C.Hom (A , a) (B , b)}
```
-->

we need not only $r : f \is g$,

```agda
        (r : f ≡ g)
```

. . .

but also a *homotopy* between $q : a \is bg$ and the action of $r$ on $p
: a \is bf$.

. . .

```agda
      → (α : q ≡ p ∙ ap (b ∘_) r)
      → (f , p) ≡ (g , q)
    _ = λ p q → p ,ₚ commutes→square (∙-idl _ ∙ q)
```

# Propositions

A type $P : \ty$ is a [[proposition]] if, given any $x, y : X$, we can
find $x \is y$.

. . .

**Theorem**: If $P : X \to \ty$ is a family of propositions, then the
map $\pi_1 : (\Sigma_{x : A} P(x)) \to A$ induces an equivalence
$$
\ap{\pi_1} :\ ((a,\, p) \is (b,\, q)) \simeq (a \is b)
$$
for any $a, b : A$, $p : P(a)$, $q : P(b)$.

. . .

If $P$ is a family of propositions, $\Sigma_{x : A} P(x)$ is the type of
"those $A$s which satisfy $P$"!

---

## Sets

We say that $X : \ty$ is a [[set]] if all its identity types
$x \is_X y$ are propositions.

. . .

* Any type with decidable equality ($\bN$, $\bZ$, $\bQ$) is a set.
* The real numbers are a set.
* If $F : X \to \ty$ is a family of sets, then $(x : X) \to F(x)$ is a set.
* If $X$ is a set and $F : X \to \ty$ is a family of sets, then
  $\Sigma_{x : X} F(x)$ is a set.
* Every proposition is a set.

. . .

We can fix the issue with slice categories by defining categories to
have `Hom`{.Agda}-**sets** rather than `Hom`{.Agda}-types.

<!--
```agda
open import Cat.Base hiding (H-Level-Nat)

private module _ {o ℓ} (C : Precategory o ℓ) (X : ⌞ C ⌟) where private
  private module C = Precategory
  open Precategory C
```
-->

## Slices, take two

Start as before...

```agda
  Slice : Precategory (o ⊔ ℓ) ℓ
  Slice .C.Ob  = Σ[ Y ∈ C ] (Hom Y X)
  Slice .C.Hom (Y , y) (Z , z) = Σ[ h ∈ Hom Y Z ] y ≡ z ∘ h
  Slice .C.id {x , f} = id , sym (idr f)
  Slice .C._∘_ (f , p) (g , q) = f ∘ g ,
    q ∙ ap₂ _∘_ p refl ∙ sym (assoc _ _ _)
```

. . .

But now our coherence issue is handled! We can use our assumption that
$\cC(-,-)$ is a set.

```agda
  Slice .C.idl (f , α) = idl f ,ₚ
    is-prop→pathp (λ i → Hom-set _ _ _ _) _ _
```

<!--
```
  Slice .C.idr _ = Σ-prop-path! (idr _)
  Slice .C.assoc _ _ _ = Σ-prop-path! (assoc _ _ _)
```
-->

---

We still have to show that $\cC/X(-,-)$ is a set.

```agda
  Slice .C.Hom-set (Y , y) (Z , z) =
    Σ-is-hlevel 2 (Hom-set Y Z) λ x →
      is-prop→is-set (Hom-set Y X y (z ∘ x))
```

It's rote application of the closure properties.

## Getting Agda to do it

The solution is classic: instance search. We have a class
`H-Level`{.Agda}, and instances for all of the closure properties:

```agda
  _ : H-Level Nat 2
  _ = auto
```

. . .

```agda
  _ : ⦃ _ : H-Level A n ⦄ ⦃ _ : H-Level B n ⦄ → H-Level (A × B) n
  _ = auto

  _ : ⦃ _ : H-Level B n ⦄ → H-Level (A → B) n
  _ = auto
```

. . .

```agda
  _ : ⦃ _ : H-Level A n ⦄ ⦃ _ : H-Level B n ⦄ ⦃ _ : 2 ≤ n ⦄
    → H-Level (A ⊎ B) n
  _ = auto
```

. . .

Agda doesn't backtrack during instance search. We handle upwards closure
at each of the leaf instances:

```agda
  _ : H-Level Nat 75
  _ = H-Level-Nat
```

---

<!--
```agda
private module _ {o ℓ} (C : Precategory o ℓ) (X : ⌞ C ⌟) where private
  private module C = Precategory
  open Precategory C
  Slice : Precategory (o ⊔ ℓ) ℓ
  Slice .C.Ob  = Σ[ Y ∈ C ] (Hom Y X)
  Slice .C.Hom (Y , y) (Z , z) = Σ[ h ∈ Hom Y Z ] y ≡ z ∘ h
  Slice .C.id {x , f} = id , sym (idr f)
  Slice .C._∘_ (f , p) (g , q) = f ∘ g ,
    q ∙ ap₂ _∘_ p refl ∙ sym (assoc _ _ _)
```
-->

Now we can get Agda to fill in *all* the coherences in the definition of
`Slice`{.Agda}!

```agda
  Slice .C.idl _ = idl _ ,ₚ prop!
  Slice .C.idr _ = idr _ ,ₚ prop!
  Slice .C.assoc _ _ _ = assoc _ _ _ ,ₚ prop!
  Slice .C.Hom-set _ _ = hlevel 2
```

. . .

h-Level proofs are ubiquitous, often perfectly mechanical, and very
boring to write by hand. This is the oldest trick in our book!

# Identity systems

<!--
```agda
_ = funext
_ = _,ₚ_
```
-->

We've already seen that a path between pairs is a pair of paths.

Similarly, a path between functions is a function between paths.

These are **identity systems**: (coherent) replacements for identity
types.

. . .

An identity system on $A$ is a relation $R(-, -)$ equipped with $r :
\forall a \to R(a, a)$, such that...

::: incremental
- The map $p \mapsto \operatorname{subst}(R(a, -))(p)(r\ a)$ is an equivalence $a \is b \to R(a, b)$, or
- We have a map $t : (p : R(a, b)) \to (a,\ r\ a) \is (b,\ p)$, or
- The total space $\Sigma_{b : A} R(a, b)$ is [[contractible]] for any $a$.
:::

. . .

These are all equivalent *definitions*.

. . .

<!--
```agda
_ = J
```
-->

Any construction on identity *types* works for an arbitrary identity
*system*, since any identity system satisfies `J`{.Agda}.

## Examples

On product types, we have pointwise equality:

```agda
~Π : (f g : (x : A) → P x) → Type _
~Π f g = ∀ a → f a ≡ g a
```

. . .

On dependent sums, we have componentwise equality:

```agda
~Σ : (p q : Σ A P) → Type _
~Σ {P = P} (u , x) (v , y) = Σ[ p ∈ u ≡ v ]
  PathP (λ i → P (p i)) x y
```

. . .

On inductive types, we have equality-by-cases:

```agda
_==_ : Nat → Nat → Type
zero  == zero  = ⊤
zero  == suc _ = ⊥
suc _ == zero  = ⊥
suc x == suc y = x == y
```

. . .

Identity systems can be computed "by cases on the type": see (higher)
observational type theory.

---

But we can also apply domain-specific knowledge: The relation
$$
(a : A) \to f(\operatorname{inc} a) = g(\operatorname{inc} a)
$$
is an identity system on functions $f, g : A/R \to B$, whenever $B$ is a set.

. . .

Similarly, if $f, g : (w : \Sigma_{x : A} B(x)) \to C(w)$, then
$$\forall\, a\ b \to f(a,\ b) = g(a,\ b)$$
is an identity system.

. . .

These "domain specific" rules break *parametricity* (or *confluence*, or
*stability under substitution*). But they sure are handy!

---

### Extensionality

Once again, this is an instance search problem!

<!--
```agda
private module _ where private instance
```
-->

```agda
  record Extensional (A : Type ℓ) ℓ-rel : Type (ℓ ⊔ lsuc ℓ-rel) where
    no-eta-equality
    field
      Pathᵉ : A → A → Type ℓ-rel
      reflᵉ : ∀ x → Pathᵉ x x
      idsᵉ : is-identity-system Pathᵉ reflᵉ
```

<!--
```agda
  open Extensional
  open Extensional ⦃ ... ⦄ renaming (Pathᵉ to _~_) using ()
```
-->

We can get the elaborator to solve for identity systems, by declaring
them as instances.

It won't be stable under substitution, but who cares! We're not defining
an actual *function* from types.

---

The base case is just the identity type:

```agda
  base : Extensional A (level-of A)
  base .Pathᵉ   = _≡_
  base .reflᵉ _ = refl
  base .idsᵉ    = Path-identity-system
```

. . .

We can lift `Extensional`{.Agda} instances through `Π`-types:

```agda
  liftΠ
    : ⦃ ∀ {x} → Extensional (P x) ℓr ⦄
    → Extensional ((x : A) → P x) _

  liftΠ ⦃ sb ⦄ .Pathᵉ f g =
    ∀ x → Pathᵉ sb (f x) (g x)

  liftΠ ⦃ sb ⦄ .reflᵉ f x = reflᵉ sb (f x)
```

<!--
```agda
  liftΠ ⦃ sb ⦄ .idsᵉ .to-path h =
    funext λ i → sb .idsᵉ .to-path (h i)
  liftΠ ⦃ sb ⦄ .idsᵉ .to-path-over h =
    funextP λ i → sb .idsᵉ .to-path-over (h i)
```
-->

---

Our non-parametric instances are no problem:

```agda
  uncurry
    : ⦃ sb : Extensional ((x : A) (y : P x) → Q x y) ℓr ⦄
    → Extensional (((x , y) : Σ A P) → Q x y) ℓr

  uncurry ⦃ sb ⦄ .Pathᵉ f g = sb .Pathᵉ (curry f) (curry g)

  uncurry ⦃ sb ⦄ .reflᵉ f = sb .reflᵉ (curry f)
```

<!--
```agda
  uncurry ⦃ sb = sb ⦄ .idsᵉ .to-path h i (a , b) = sb .idsᵉ .to-path h i a b
  uncurry ⦃ sb = sb ⦄ .idsᵉ .to-path-over h = sb .idsᵉ .to-path-over h
```
-->

. . .

... we just have to make it clear they're a tad evil.

```agda
  {-# INCOHERENT base uncurry #-}
```

---

This all works exactly as expected:

<!--
```agda
  private module _ {A : Type} {B : A → Type} {C : (x : A) → B x → Type} {D : (x : A) (y : B x) → C x y → Type} where
```
-->

```agda
    _ : ∀ {f g : ((a , b) : (Σ A B)) (c : C a b) → D a b c}
      → (f ~ g) ≡ (∀ a b c → f (a , b) c ≡ g (a , b) c)
    _ = refl
```

Non-parametric `Extensional`{.Agda} was integral to formalising Day
convolution:
```agda
open import Cat.Monoidal.Instances.Day
```

# Structure identity
