<!--
```agda
open import Cat.Diagram.Coend.Sets
open import Cat.Functor.Bifunctor
open import Cat.Instances.Functor
open import Cat.Functor.Compose
open import Cat.Functor.Closed
open import Cat.Diagram.Coend
open import Cat.Functor.Hom
open import Cat.Bi.Base
open import Cat.Prelude

open import Data.Set.Coequaliser

import Cat.Functor.Reasoning as Fr
import Cat.Reasoning

open make-natural-iso
open Make-bifunctor
open Cowedge
open Functor
open _=>_
```
-->

```agda
module Cat.Functor.Profunctor where
```

# Profunctors {defines="profunctor"}

<!--
```agda
private variable
  o ℓ o' ℓ' : Level
  C D E : Precategory o ℓ
```
-->

A **profunctor** $P : \cC \rel \cD$ is a [[bifunctor]]
$P : \cD\op \times \cC \to \Sets$.
As with [[presheaves]], we define `Profunctor`{.Agda} parametrically
over the universe level in which the functors are valued. Much like a
presheaf on $\cC$ can be thought of as a *predicate* on $\cC$, a
profunctor $\cC \rel \cD$ can be thought of as a *relation* between
$\cC$ and $\cD$.

```agda
Profunctor : (C : Precategory o ℓ) (D : Precategory o' ℓ') (ℓ : Level) → Type _
Profunctor C D ℓ = Bifunctor (D ^op) C (Sets ℓ)
```

In the formalisation, we use `_↬_`{.Agda} to indicate that both
categories are *small* relative to some universe and that the
profunctors will be valued in this universe. This restricted situation
allows defining a [[bicategory]] of [[precategories]], profunctors, and
[[natural transformations]].

```agda
_↬_ : Precategory ℓ ℓ → Precategory ℓ ℓ → Precategory _ _
_↬_ {ℓ = ℓ} C D = Cat[ D ^op , Cat[ C , Sets ℓ ] ]

module Prof {ℓ} {C D : Precategory ℓ ℓ} = Cat.Reasoning (C ↬ D)
```

## Profunctor composition

The composition of profunctors $F : \cD \rel \cE$ and $G : \cC \rel \cD$
computes, at each pair $(x, z) : \cE\op \times \cC$, the set of ways in
which an object $y : \cD$ can "bridge the gap" between $F(-, x)$ and
$G(z, -)$. We start by considering the type
$$
  \sum_{y : \cD} F(x, y) \times G(y, z)
$$
whose inhabitants are triples $\langle y, f, g \rangle$. This can be
made functorial in $x$ and $z$ using the functorial actions of $F$ on
$\cE\op$ and $G$ on $\cC$, respectively; this construction is even
functorial in $F$ and $G$, so it has the right *type* to be the
composition $F \circ G$.  However, it is not: none of the bicategorical
coherences are constructible.

Suppose we have $G : \cC \rel \cD$ and we want to show that composition
is unital on the left, i.e. we want to construct a (natural) isomorphism
$$
  G(a, b) \cong \sum_{y : \cD} \cD(a, y) \times G(y, b)
$$. In one direction, we can send $g : G(a, b)$ to the triple $\langle
a, \id, g \rangle$. In the other, where we have a triple $(y, h, g)$,
the functorial action of $G$ on its left variable is a function $G(h, -)
: G(y, b) \to G(a, b)$. Tracing an element $g : G(a, b)$ through this
process computes $G(\id, -)(g) = g$, as we wanted; In the converse
direction, tracing a triple $\langle y, h, g \rangle$ results instead in
$\langle a, \id, G(h, -)(g) \rangle$, but we have no hope of showing $y
= a$ to even compare the rest of the pairs. However, if we recall that
$$
  h = {\id} \circ h = \cD(-, h)(\id)
$$
we can rewrite our original triple as instead $\langle y, \cD(-,
h)(\id), g \rangle$, making it clear that we started with a triple
constructed by applying the *right* action of $\cD(-, -)$ on the *left*
coordinate, but ended up with one where the *right* coordinate is under
the *left* action of $G$. Generically, then, we want to identify all
triples
$$
  \langle -, F(-, h)(f), g \rangle = \langle -, f, G(h, -)(g) \rangle
$$
which differ only by this swap of which action is used for the $\cD$
variable. This is a canned categorical construction: the [[coend]]
$$
  \int^{y : \cD} F(x, y) \times G(y, z)
$$.

<!--
```agda
private module procompose (F : ⌞ D ↬ E ⌟) (G : ⌞ C ↬ D ⌟) where
  open Functor
  private
    module F = Bifunctor F
    module F◀ {X} = Fr (F.Left X)
    module F▶ {X} = Fr (F.Right X)

    module G = Bifunctor G
    module G◀ {X} = Fr (G.Left X)
    module G▶ {X} = Fr (G.Right X)
```
-->

We start by constructing the diagram over which the coend will be taken.
Note that this uses the *right* action of $F$ and the *left* action of
$G$.

```agda
  procompose-diagram : ⌞ C ⌟ → ⌞ E ⌟ → ⌞ D ↬ D ⌟
  procompose-diagram c e = make-bifunctor λ where
    .F₀ d⁻ d⁺ .∣_∣   → ⌞ F · e · d⁺ ⌟ × ⌞ G · d⁻ · c ⌟
    .lmap f (a , b) → a , G.lmap f b
    .rmap f (a , b) → F.rmap f a , b
```

<!--
```agda
    .F₀ d⁻ d⁺ .is-tr → hlevel 2
    .lmap-id         → ext λ a b → refl ,ₚ G◀.elim refl ·ₚ _
    .rmap-id         → ext λ a b → F▶.elim refl ·ₚ _ ,ₚ refl
    .lmap-∘ f g      → ext λ a b → refl ,ₚ G◀.expand refl ·ₚ _
    .rmap-∘ f g      → ext λ a b → F▶.expand refl ·ₚ _ ,ₚ refl
    .lrmap  f g      → ext λ a b → refl

  procompose-coend : ∀ c e → Coend (procompose-diagram c e)
  procompose-coend c e = Set-coend (procompose-diagram c e)

  module procompose-coend c e = Coend (procompose-coend c e)
```
-->

<details>
<summary>
We can then calculate that, even after imposing the extranaturality
condition, we can still extend the actions of $F$ and $G$ on the
extremities into actions on the coend. This uses the *left* action of
$F$ and the *right* action of $G$.

```agda
  procompose : Profunctor C E _
  procompose = make-bifunctor mk where
    mk : Make-bifunctor {C = E ^op} {C} {Sets _}
    mk .F₀ e c = procompose-coend.nadir c e
    mk .lmap {a} {b} {x} f = rec! λ where
      .inc* c a b → begin c (F.lmap f a , b)
      .glue*      → ext λ x y g α β →
        begin _ (F.lmap f (F.rmap g α) , β) ≡⟨ ap (begin _) (F.lrmap _ _ ·ₚ _ ,ₚ refl) ⟩
        begin _ (F.rmap g (F.lmap f α) , β) ≡⟨ coend-glue _ _ ⟩
        begin _ (F.lmap f α , G.lmap g β)   ∎
```

The rest of the calculation is symmetric.
</summary>

```agda
    mk .rmap {a} {b} {x} f = rec! λ where
      .inc* c a b → begin c (a , G.rmap f b)
      .glue*      → ext λ x y g α β →
        begin _ (F.rmap g α , G.rmap f β)   ≡⟨ coend-glue _ _ ⟩
        begin _ (α , G.lmap g (G.rmap f β)) ≡⟨ ap (begin _) (refl ,ₚ G.lrmap _ _ ·ₚ _)  ⟩
        begin _ (α , G.rmap f (G.lmap g β)) ∎

    mk .lmap-id    = ext λ a b c → ap (begin _) (F◀.elim   refl ·ₚ _ ,ₚ refl)
    mk .lmap-∘ f g = ext λ a b c → ap (begin _) (F◀.expand refl ·ₚ _ ,ₚ refl)
    mk .rmap-id    = ext λ a b c → ap (begin _) (refl ,ₚ G▶.elim   refl ·ₚ _)
    mk .rmap-∘ f g = ext λ a b c → ap (begin _) (refl ,ₚ G▶.expand refl ·ₚ _)
    mk .lrmap  f g = ext λ a b c → refl
```

</details>

<!--
```agda
open procompose using (procompose) public
open procompose
```
-->

<details>
<summary>
It is also straightforward to show that `procompose`{.Agda} can be made
into a bifunctor between profunctor categories.
</summary>

```agda
procompose-functor : Bifunctor (D ↬ E) (C ↬ D) (C ↬ E)
procompose-functor = make-bifunctor mk where
  mk : Make-bifunctor
  mk .F₀   = procompose
  mk .lmap {F} {G} {H} f .η x .η y = rec! λ where
    .inc* c a b → begin c (f · x · c · a , b)
    .glue*      → ext λ x y h a b →
      begin x (f · _ · x · Bifunctor.rmap F h a , b)   ≡⟨ ap (begin _) (Binatural.natural-▶ f ·ₚ _ ,ₚ refl) ⟩
      begin x (Bifunctor.rmap G h (f · _ · y · a) , b) ≡⟨ coend-glue _ _ ⟩
      begin y (f · _ · y · a , Bifunctor.lmap H h b)   ∎
  mk .rmap {F} {G} {H} f .η x .η y = rec! λ where
    .inc* c a b → begin c (a , f · c · y · b)
    .glue*      → ext λ x y h a b →
      begin x (Bifunctor.rmap H h a , f · x · _ · b)   ≡⟨ coend-glue _ _ ⟩
      begin y (a , Bifunctor.lmap G h (f · x · _ · b)) ≡⟨ ap (begin _) (refl ,ₚ sym (Binatural.natural-◀ f ·ₚ _)) ⟩
      begin y (a , f · y · _ · Bifunctor.lmap F h b)   ∎

  mk .lmap f .η G .is-natural x y g = ext λ a b c → refl
  mk .lmap {F} {G} {H} f .is-natural x y g = ext λ a b c d →
    ap (begin _) (Binatural.natural-◀ f ·ₚ _ ,ₚ refl)

  mk .rmap {F} {G} {H} f .η x .is-natural _ _ _ = ext λ a b c →
    ap (begin _) (refl ,ₚ Binatural.natural-▶ f ·ₚ _)
  mk .rmap {F} {G} {H} f .is-natural x y f₁ = ext λ a b c d → refl

  mk .lmap-id    = ext λ i j k x y → refl
  mk .rmap-id    = ext λ i j k x y → refl
  mk .lmap-∘ f g = ext λ i j k x y → refl
  mk .rmap-∘ f g = ext λ i j k x y → refl
  mk .lrmap  f g = ext λ i j k x y → refl
```

</details>

Since it was used to motivate the coend, we linger on the definition of
the left unit coherence. The maps are as described above: if we start
with a triple (the `eta`{.Agda} case), we use the left action of $G$ to
put everything together. In the `inv`{.Agda} case, we form a triple by
grouping an element $g : G(a, b)$ with the identity map.

```agda
procompose-idl : (G : ⌞ C ↬ D ⌟) → procompose (Hom[-,-] D) G Prof.≅ G
procompose-idl {D = D} G = to-natural-iso mk where
  module G = Bifunctor G
  module D = Precategory D

  mk : make-natural-iso _ _
  mk .eta a .η b = rec! λ where
    .inc* y h g → G.lmap h g
    .glue*      → ext λ x y f z g → Fr.expand (G.Left _) refl ·ₚ _
  mk .inv a .η b g = begin a (D.id , g)
```

To show that these cancel, we first use the extranaturality we imposed
to swap the actions along the coordinates, then remove the extra
composite from the action of $\cD(-,-)$.

```agda
  mk .inv∘eta a = ext λ b y h g →
    begin a (D.id , G.lmap h g) ≡˘⟨ coend-glue _ _ ⟩
    begin y (h D.∘ D.id , g)    ≡⟨ ap (begin _) (D.idr _ ,ₚ refl) ⟩
    begin y (h , g)             ∎
```

<!--
```agda
  mk .eta x .is-natural y z f = ext λ x y z → G.lrmap _ _ ·ₚ _
  mk .inv x .is-natural y z f = refl
  mk .eta∘inv x     = ext λ i a     → G.lmap-id ·ₚ _
  mk .natural x y f = ext λ i a b c → Fr.collapse (G.Left _) refl ·ₚ _
```
-->

<details>
<summary>The rest of the coherence data is analogous.</summary>

```agda
procompose-idr : (F : ⌞ C ↬ D ⌟) → procompose F (Hom[-,-] C) Prof.≅ F
procompose-idr {C = C} F = to-natural-iso mk where
  module F = Bifunctor F
  module C = Precategory C

  mk : make-natural-iso _ _
  mk .eta x .η y = rec! λ where
    .inc* _ a b → F.rmap b a
    .glue*      → ext λ x y f z g → Fr.collapse (F.Right _) refl ·ₚ _
  mk .eta x .is-natural y z f = ext λ x y z → Fr.expand (F.Right _) refl ·ₚ _
  mk .inv x .η y z = begin y (z , C.id)
  mk .inv x .is-natural y z f = ext λ a → coend-glue _ _ ∙ ap (begin _) (refl ,ₚ C.idl _ ∙ sym (C.idr _))
  mk .eta∘inv x     = ext λ i a     → F.rmap-id ·ₚ _
  mk .inv∘eta x     = ext λ i a b c → coend-glue _ _ ∙ ap (begin _) (refl ,ₚ C.idl _)
  mk .natural x y f = ext λ i a b c → F.lrmap _ _ ·ₚ _

procompose-assoc : ∀ {ℓ} → Associator-for (_↬_ {ℓ = ℓ}) procompose-functor
procompose-assoc = to-natural-iso mk where
  mk : make-natural-iso _ _
  mk .eta (F , G , H) .η y .η i = rec! λ where
    .inc* _ .inc* _ a b c → begin _ (a , begin _ (b , c))
    .inc* _ .glue* → ext λ i j h x y z → coend-glue _ _
    .glue* → ext λ i j h k x y z → ap (begin _) (refl ,ₚ coend-glue _ _)

  mk .inv (F , G , H) .η x .η y = rec! λ where
    .inc* _ a .inc* _ b c → begin _ (begin _ (a , b) , c)
    .inc* _ a .glue* → ext λ j h x y z → coend-glue _ _
    .glue* → ext λ i j h k x y z → ap (begin _) (coend-glue _ _ ,ₚ refl)

  mk .eta x .η y .is-natural w z f = ext λ a b c d e → refl
  mk .eta x .is-natural y z f = ext λ a b c d e h → refl
  mk .inv (F , G , H) .η x .is-natural y z f = ext λ a b c d e → refl
  mk .inv (F , G , H) .is-natural x y f = ext λ i a b c d e → refl
  mk .eta∘inv (F , G , H) = ext λ a b c d e f g → refl
  mk .inv∘eta (F , G , H) = ext λ a b c d e f g → refl
  mk .natural _ _ _       = ext λ a b c d e f g → refl

open Prebicategory

Prof : ∀ ℓ → Prebicategory (lsuc ℓ) (lsuc ℓ) ℓ
Prof ℓ .Ob      = Precategory ℓ ℓ
Prof ℓ .Hom     = _↬_
Prof ℓ .id      = Hom[-,-] _
Prof ℓ .compose = procompose-functor
Prof ℓ .unitor-r = to-natural-iso mk where
  mk : make-natural-iso _ _
  mk .eta F   = Prof.from (procompose-idr F)
  mk .inv F   = Prof.to (procompose-idr F)
  mk .eta∘inv F = Prof.invr (procompose-idr F)
  mk .inv∘eta F = Prof.invl (procompose-idr F)
  mk .natural F G h = ext λ i j x → refl
Prof ℓ .unitor-l = to-natural-iso mk where
  mk : make-natural-iso _ _
  mk .eta F   = Prof.from (procompose-idl F)
  mk .inv F   = Prof.to (procompose-idl F)
  mk .eta∘inv F = Prof.invr (procompose-idl F)
  mk .inv∘eta F = Prof.invl (procompose-idl F)
  mk .natural F G h = ext λ i j x → refl
Prof ℓ .associator = procompose-assoc
Prof ℓ .triangle f g      = ext λ i j x a y h b     → coend-glue _ _
Prof ℓ .pentagon f g h i  = ext λ i j k x l y m z h → refl
```

</details>
