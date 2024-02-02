<!--
```agda
open import Cat.Functor.Kan.Duality
open import Cat.Functor.Kan.Global
open import Cat.Instances.Functor
open import Cat.Functor.Kan.Base
open import Cat.Functor.Adjoint
open import Cat.Functor.Compose
open import Cat.Prelude
```
-->

```agda
module Cat.Functor.Kan.Adjoint where
```

<!--
```agda
open _=>_
open _⊣_

private
  variable
    o ℓ : Level
    C D E : Precategory o ℓ
```
-->

# Adjoints are Kan extensions {defines="adjoints-are-kan-extensions"}

One way to think about [[Kan extensions]] is that, when they exist, they
allow us to "compose" two functors when one of them is going the wrong
way: given a span

$$
D \xot{F} C \xto{H} E
$$

we get a "composite" $\Lan_F(H) : D \to E$. With this perspective in
mind, it's reasonable to expect that, if $F$ has an [inverse] $G : D \to
C$, the composite we get should be the actual composite $H \circ G$.

In fact, we can do better: if $F$ only has a [[right adjoint]] $F \dashv
G$ (which we can think of as a directed inverse), then the induced
`precomposite adjunction`{.Agda ident=precomposite-adjunction} $- \circ
G \dashv - \circ F$ means that *left* ([global]) Kan extensions along
$F$ are given by precomposition with $G$ (and, dually, [[right Kan
extensions]] along $G$ are given by precomposition with $F$).

[inverse]: Cat.Functor.Equivalence.html
[global]: Cat.Functor.Kan.Global.html

```agda
module _ {F : Functor C D} {G : Functor D C} (F⊣G : F ⊣ G) where
  adjoint→is-lan
    : (H : Functor C E)
    → is-lan F H (H F∘ G) (precomposite-adjunction F⊣G .unit .η H)
  adjoint→is-lan = adjoint-precompose→Lan F (precompose G) (precomposite-adjunction F⊣G)
```

A more common way to say this is that $G$ is the `absolute`{.Agda
ident=is-absolute-lan} left Kan extension of $F$ along the identity;
this is essentially a reformulation of the above fact:

```agda
  adjoint→is-lan-id : is-lan F Id G (F⊣G .unit)
  adjoint→is-lan-id =
    transport (λ i → is-lan F Id (F∘-idl i) (fixNT i))
      (adjoint→is-lan Id)
    where
      fixNT : PathP (λ i → Id => F∘-idl {F = G} i F∘ F) _ _
      fixNT = Nat-pathp refl (λ i → F∘-idl i F∘ F) (λ _ → refl)

  adjoint→is-absolute-lan : is-absolute-lan adjoint→is-lan-id
  adjoint→is-absolute-lan H =
    transport (λ i → is-lan F (F∘-idr (~ i)) (H F∘ G) (fixNT (~ i)))
      (adjoint→is-lan H)
    where
      fixNT : PathP (λ i → F∘-idr {F = H} i => (H F∘ G) F∘ F) _ _
      fixNT = Nat-pathp F∘-idr refl (λ _ → refl)
```

The dual statement is obtained by... [duality], this time using the
`counit`{.Agda} of the precomposite adjunction:

[duality]: Cat.Functor.Kan.Duality.html

```agda
module _ {F : Functor C D} {G : Functor D C} (F⊣G : F ⊣ G) where
  adjoint→is-ran
    : (H : Functor D E)
    → is-ran G H (H F∘ F) (precomposite-adjunction F⊣G .counit .η H)
  adjoint→is-ran H =
    transport (λ i → is-ran G H (fixF i) (fixNT i))
      (is-co-lan'→is-ran G H
        (adjoint→is-lan (opposite-adjunction F⊣G) (Functor.op H)))
    where
      fixF : Functor.op (Functor.op H F∘ Functor.op F) ≡ H F∘ F
      fixF = Functor-path (λ _ → refl) (λ _ → refl)
      fixNT : PathP (λ i → fixF i F∘ G => H) _ _
      fixNT = Nat-pathp (λ i → fixF i F∘ G) refl (λ _ → refl)
```

Even more dually, we can flip the span above to get a *cospan* of
functors, giving rise to the theory of **Kan lifts**. We then get
analogous statements: left (resp. right) adjoints are absolute left
(resp. right) Kan lifts along the identity.
