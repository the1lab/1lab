<!--
```agda
open import 1Lab.Reflection.Induction

open import Algebra.Group.Cat.FinitelyComplete
open import Algebra.Group.Cat.Base
open import Algebra.Prelude
open import Algebra.Group

open import Cat.Diagram.Colimit.Finite

open Finitely-cocomplete
open is-group-hom
open is-pushout
open Coproduct
open Pushout
```
-->

```agda
module Algebra.Group.Free.Product {ℓ} where
```

# Free products of groups {defines="free-product amalgamated-free-product"}

Given two [[groups]] $A$ and $B$, their **free product** is the [[coproduct]]
$A + B$ in the [[category of groups]] (not to be confused with the
[[*direct* product|direct product of groups]] $A \times B$, which is the
categorical [[product]]).

As the name suggests, we can describe the free product $A + B$ as the
free group equipped with inclusions $A \hookrightarrow A + B$ and
$B \hookrightarrow A + B$. In fact, we define a more general construction:
the **amalgamated free product** of a span of groups
$A \overset{f}{\ot} C \overset{g}{\to} B$, which realises the
[[pushout]] of this span.

<!--
```agda
module _ {A B C : Group ℓ} (f : Groups.Hom C A) (g : Groups.Hom C B) where
  private
    module A = Group-on (A .snd)
    module B = Group-on (B .snd)
```
-->

We start by freely adding the group operations and enforcing the group
axioms, just like for [[free groups|free group construction]]...

```agda
  data Amalgamated : Type ℓ where
    _◆_ : Amalgamated → Amalgamated → Amalgamated
    inv : Amalgamated → Amalgamated
    nil : Amalgamated

    f-assoc : ∀ x y z → x ◆ (y ◆ z) ≡ (x ◆ y) ◆ z
    f-invl  : ∀ x → inv x ◆ x ≡ nil
    f-idl   : ∀ x → nil ◆ x ≡ x
```

...we then throw in the inclusions of $A$ and $B$, which are required to
be [[group homomorphisms]] and to make the pushout square commute...

```agda
    inl : ⌞ A ⌟ → Amalgamated
    inl-hom : ∀ a a' → inl (a A.⋆ a') ≡ inl a ◆ inl a'

    inr : ⌞ B ⌟ → Amalgamated
    inr-hom : ∀ b b' → inr (b B.⋆ b') ≡ inr b ◆ inr b'

    glue : (c : ⌞ C ⌟) → inl (f # c) ≡ inr (g # c)
```

...finally, we truncate the resulting type to a set.

```agda
    squash : is-set Amalgamated
```

<!--
```agda
  unquoteDecl Amalgamated-elim-prop = make-elim-n 1
    Amalgamated-elim-prop (quote Amalgamated)
```
-->

<details>
<summary>
As expected, this data perfectly assembles into a group $A +_C B$
together with homomorphisms $A \to A +_C B$ and $B \to A +_C B$
fitting into a square with $f$ and $g$.

~~~{.quiver}
\[\begin{tikzcd}
  & C \\
  A && B \\
  & {A +_C B}
  \arrow["f"', from=1-2, to=2-1]
  \arrow["g", from=1-2, to=2-3]
  \arrow["{\mathrm{inl}}"', from=2-1, to=3-2]
  \arrow["{\mathrm{inr}}", from=2-3, to=3-2]
\end{tikzcd}\]
~~~

```agda
  Amalgamated-free-product : Group ℓ
  inlᴳ : Groups.Hom A Amalgamated-free-product
  inrᴳ : Groups.Hom B Amalgamated-free-product
  glueᴳ : inlᴳ Groups.∘ f ≡ inrᴳ Groups.∘ g
```
</summary>

```agda
  Amalgamated-free-product = to-group fp where
    fp : make-group Amalgamated
    fp .make-group.group-is-set = squash
    fp .make-group.unit = nil
    fp .make-group.mul = _◆_
    fp .make-group.inv = inv
    fp .make-group.assoc = f-assoc
    fp .make-group.invl = f-invl
    fp .make-group.idl = f-idl

  inlᴳ .hom = inl
  inlᴳ .preserves .pres-⋆ = inl-hom

  inrᴳ .hom = inr
  inrᴳ .preserves .pres-⋆ = inr-hom

  glueᴳ = ext glue
```
</details>

The universal property of the pushout is easy to verify.

```agda
  Groups-pushout : is-pushout (Groups ℓ) f inlᴳ g inrᴳ
  Groups-pushout .square = glueᴳ
  Groups-pushout .universal {Q} {p} {q} comm .hom = go where
    module Q = Group-on (Q .snd)
    go : Amalgamated → ⌞ Q ⌟
    go (x ◆ y) = go x Q.⋆ go y
    go (inv x) = go x Q.⁻¹
    go nil = Q.unit
    go (f-assoc x y z i) = Q.associative {go x} {go y} {go z} i
    go (f-invl x i) = Q.inversel {go x} i
    go (f-idl x i) = Q.idl {go x} i
    go (inl a) = p # a
    go (inl-hom a a' i) = p .preserves .pres-⋆ a a' i
    go (inr b) = q # b
    go (inr-hom b b' i) = q .preserves .pres-⋆ b b' i
    go (glue c i) = unext comm c i
    go (squash x y α β i j) =
      Q.has-is-set (go x) (go y) (λ i → go (α i)) (λ i → go (β i)) i j
  Groups-pushout .universal comm .preserves .pres-⋆ _ _ = refl
  Groups-pushout .universal∘i₁ = trivial!
  Groups-pushout .universal∘i₂ = trivial!
  Groups-pushout .unique {Q = Q} {colim' = u} comm₁ comm₂ = ext $
    Amalgamated-elim-prop (λ _ → hlevel 1)
      (λ x p y q → u .preserves .pres-⋆ x y ∙ ap₂ Q._⋆_ p q)
      (λ x p → pres-inv (u .preserves) ∙ ap Q._⁻¹ p)
      (pres-id (u .preserves))
      (unext comm₁) (unext comm₂)
    where module Q = Group-on (Q .snd)

  Groups-Pushout : Pushout (Groups ℓ) f g
  Groups-Pushout .coapex = Amalgamated-free-product
  Groups-Pushout .i₁ = inlᴳ
  Groups-Pushout .i₂ = inrᴳ
  Groups-Pushout .has-is-po = Groups-pushout
```

Since the [[zero group]] is also an [[initial object]], this shows that the
category of groups is [[finitely cocomplete]].

```agda
Groups-finitely-cocomplete : Finitely-cocomplete (Groups ℓ)
Groups-finitely-cocomplete = with-pushouts (Groups _)
  (Zero.initial ∅ᴳ) Groups-Pushout
```

We thus get the free product of $A$ and $B$ by abstract nonsense, as the
pushout of the span $A \overset{¡}{\ot} 0 \overset{¡}{\to} B$.

```agda
Free-product : Group ℓ → Group ℓ → Group ℓ
Free-product A B = Groups-finitely-cocomplete .coproducts A B .coapex
```
