<!--
```agda
open import 1Lab.Path.Cartesian

open import Cat.Diagram.Monad
open import Cat.Prelude

import Cat.Reasoning

open Functor
open _=>_
```
-->

```agda
module Cat.Diagram.Monad.Extension where
```

<!--
```
module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C
```
-->

# Extension Systems {defines=extension-system}

An **extension system** on a category $\cC$ is a way of presenting a
[[monad]] on $\cC$. As the name suggests, extension systems are built
around an extension operation $\cC(X,M(Y)) \to \cC(M(X), M(Y))$ instead
of the $\cC(M(M(X)), M(X))$ of a monad. This has a couple of immediate
benefits:

1. Using an extension operation lets us avoid repeated iterations of $M$,
which tends to not be particularly ergonomic.
2. The extension operation $\cC(X,M(Y)) \to \cC(M(X), M(Y))$ provides
enough data to implement both the join of a monad *and* the functorial
action, which reduces the amount of data required.
3. It is not immediately clear how to generalize monads beyond endofunctors.
In constrast, extension systems can be readily generalized to
[[relative extension systems]].

With that bit of motivation out of the way, we shall proceed to define
extension systems. An extension system consists of:

1. A mapping of objects $M : \cC \to \cC$.
2. A family of morphisms $\eta_X : \cC(X, M(X))$, called the **unit**
of the extension system
3. An extension operation $\(-\)^{M} : \cC(X,M(y)) \to \cC(M(X), M(Y))$.
  Gesturing towards the "monads" found in functional programming, we shall
  call this operation `bind`.

Note that we do not require the mapping of objects to be functorial, nor
the do we require the unit to be natural.

```agda
  record Extension-system : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      M₀ : Ob → Ob
      unit : ∀ {x} → Hom x (M₀ x)
      bind : ∀ {x y} → Hom x (M₀ y) → Hom (M₀ x) (M₀ y)
```

We impose 3 additional equations atop this structure[^contrast this with
the 7 equations required for a monad: 2 for functoriality, 2 for naturality,
and 3 for unitality/associativity]:

1. For every $X : \cC$, $(\eta_X)^M = id_{M(X)}$
2. For every $f : \cC(X, M(Y))$, $f^M \circ \eta_X = f$
3. For every $f : \cC(Y, M(X))$ and $g : \cC(X, M(Y))$, $f^M \circ g^M = (f^M \circ g)^M$

```agda
      bind-unit-id : ∀ {x} → bind (unit {x}) ≡ id
      bind-unit-∘ : ∀ {x y} → (f : Hom x (M₀ y)) → bind f ∘ unit ≡ f
      bind-∘
        : ∀ {x y z}
        → (f : Hom y (M₀ z)) (g : Hom x (M₀ y))
        → bind f ∘ bind g ≡ bind (bind f ∘ g)
```

We can recover the join of the monad by extending the identity morphism
$id_{M(X)} : \cC(M(X), M(X))$.

```agda
    join : ∀ {x} → Hom (M₀ (M₀ x)) (M₀ x)
    join {x} = bind (id {M₀ x})
```

Furthermore, we can recover the functorial action of $M$ on $f : \cC(X,Y)$
by extending $\eta_{Y} \circ f : \cC(X, M(Y))$.

```agda
    M₁ : ∀ {x y} → Hom x y → Hom (M₀ x) (M₀ y)
    M₁ f = bind (unit ∘ f)
```

The extension system equations are strong enough to ensure functoriality.
In fact, the first equation **precisely** states that $M(id) = id$.

```agda
    M-id : ∀ {x} → M₁ (id {x}) ≡ id
    M-id =
      bind (unit ∘ id) ≡⟨ ap bind (idr _) ⟩
      bind unit        ≡⟨ bind-unit-id ⟩
      id               ∎
```

However, the second functoriality condition is less enlightening.

```agda
    M-∘ : ∀ {x y z} (f : Hom y z) (g : Hom x y) → M₁ (f ∘ g) ≡ M₁ f ∘ M₁ g
    M-∘ f g =
      bind (unit ∘ f ∘ g)                 ≡⟨ ap bind (extendl (sym (bind-unit-∘ (unit ∘ f)))) ⟩
      bind (bind (unit ∘ f) ∘ unit ∘ g)   ≡˘⟨ bind-∘ (unit ∘ f) (unit ∘ g) ⟩
      (bind (unit ∘ f) ∘ bind (unit ∘ g)) ∎
```

<!--
```agda
    M : Functor C C
    M .F₀ = M₀
    M .F₁ = M₁
    M .F-id = M-id
    M .F-∘ = M-∘
```
-->

Now that we have a functor, we can start to decipher the meaning of
the latter two equations. The second equation directly gives us naturality
of the unit, and the third gives us naturality of extension.

```agda
    unit-natural
      : ∀ {x y} (f : Hom x y)
      → unit ∘ f ≡ M₁ f ∘ unit
    unit-natural f =
      unit ∘ f               ≡˘⟨ bind-unit-∘ (unit ∘ f) ⟩
      bind (unit ∘ f) ∘ unit ∎

    bind-natural
      : ∀ {x y z} (f : Hom y z) (g : Hom x (M₀ y))
      → M₁ f ∘ bind g ≡ bind (M₁ f ∘ g)
    bind-natural f g =
      bind (unit ∘ f) ∘ bind g ≡⟨ bind-∘ (unit ∘ f) g ⟩
      bind (M₁ f ∘ g)          ∎
```

Naturality of join also follows, though is a bit more involved.

```agda
    join-natural
      : ∀ {x y} (f : Hom x y)
      → join ∘ M₁ (M₁ f) ≡ M₁ f ∘ join
    join-natural f =
      bind id ∘ bind (unit ∘ bind (unit ∘ f)) ≡⟨ bind-∘ id (unit ∘ bind (unit ∘ f)) ⟩
      bind (bind id ∘ unit ∘ bind (unit ∘ f)) ≡⟨ ap bind (cancell (bind-unit-∘ id) ∙ sym (idr _)) ⟩
      bind (bind (unit ∘ f) ∘ id)             ≡˘⟨ bind-∘ (unit ∘ f) id ⟩
      bind (unit ∘ f) ∘ bind id               ∎
```

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} {E E' : Extension-system C} where
  open Cat.Reasoning C
  private
    module E = Extension-system E
    module E' = Extension-system E'
    open Extension-system

  Extension-system-path
    : (p0 : ∀ x → E.M₀ x ≡ E'.M₀ x)
    → (∀ x → PathP (λ i → Hom x (p0 x i)) E.unit E'.unit)
    → (∀ {x y} (f : ∀ i → Hom x (p0 y i)) → PathP (λ i → Hom (p0 x i) (p0 y i)) (E.bind (f i0)) (E'.bind (f i1)))
    → E ≡ E'
  Extension-system-path p0 punit pbind = sys where
    coe-pbind
      : ∀ i
      → {x y : Ob}
      → (f : Hom x (p0 y i))
      → Hom (p0 x i) (p0 y i)
    coe-pbind i {x} {y} f = pbind (λ j → coe (λ i → Hom x (p0 y i)) i j f) i

    sys : E ≡ E'
    sys i .M₀ x = p0 x i
    sys i .unit {x} = punit x i
    sys i .bind f = coe-pbind i f
    sys i .bind-unit-id {x} =
      is-prop→pathp (λ i → Hom-set (p0 x i) (p0 x i) (coe-pbind i (punit x i)) id)
        E.bind-unit-id
        E'.bind-unit-id i
    sys i .bind-unit-∘ {x} {y} f =
      hcomp (∂ i) λ where
        j (i = i0) → Hom-set _ _ _ _ base (E.bind-unit-∘ f) j
        j (i = i1) → Hom-set _ _ _ _ base (E'.bind-unit-∘ f) j
        j (j = i0) → base
      where
        base =
          coe0→i (λ i → (f : Hom x (p0 y i)) → coe-pbind i f ∘ punit x i ≡ f)
            i
            (λ f → E.bind-unit-∘ {x} {y} f) f
    sys i .bind-∘ {x} {y} {z} f g =
      hcomp (∂ i) λ where
        j (i = i0) → Hom-set _ _ _ _ base (E.bind-∘ f g) j
        j (i = i1) → Hom-set _ _ _ _ base (E'.bind-∘ f g) j
        j (j = i0) → base
      where
        base =
          coe0→i (λ i → (f : Hom y (p0 z i)) (g : Hom x (p0 y i)) → coe-pbind i f ∘ coe-pbind i g ≡ coe-pbind i (coe-pbind i f ∘ g))
            i
            (λ f g → E.bind-∘ {x} {y} f g) f g
```
-->

## Equivalence with monads

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C
```
-->

We shall now prove that monads on $\cC$ are equivalent to extension systems
on $\cC$. We shall begin with the forward direction. Let $M$ be some monad
on $\cC$.


```agda
  Monad→Extension-system : Monad C → Extension-system C
  Monad→Extension-system M = system where
    module M = Monad M
    open Extension-system
```

The mapping of objects and unit are directly given by the functorial
action of $M$ and the unit of $M$.


```agda
    system : Extension-system C
    system .M₀ = M.M₀
    system .unit = M.unit.η _
```

Extension of a map $f : \cC(X, M(Y))$ is defined as $\mu_{Y} \circ M(f)$.

```agda
    system .bind f = M.mult.η _ ∘ M.M₁ f
```

The extension system equations follow from some short computations.

```agda
    system .bind-unit-id =
      M.mult.η _ ∘ F₁ M.M (M.unit.η _) ≡⟨ M.left-ident ⟩
      id ∎
    system .bind-unit-∘ f =
      (M.mult.η _ ∘ M.M₁ f) ∘ M.unit.η _ ≡⟨ pullr (sym $ M.unit.is-natural _ _ _) ⟩
      M.mult.η _ ∘ M.unit.η _ ∘ f        ≡⟨ cancell M.right-ident ⟩
      f                                  ∎
    system .bind-∘ f g =
      (M.mult.η _ ∘ M.M₁ f) ∘ (M.mult.η _ ∘ M.M₁ g)             ≡⟨ pullr (extendl (sym $ M.mult.is-natural _ _ _)) ⟩
      M.mult.η _ ∘ M.mult.η _ ∘ (M.M₁ (M.M₁ f) ∘ M.M₁ g)        ≡⟨ extendl (sym $ M.mult-assoc) ⟩
      M.mult.η _ ∘ M.M₁ (M.mult.η _) ∘ (M.M₁ (M.M₁ f) ∘ M.M₁ g) ≡⟨ ap₂ _∘_ refl (pulll (sym (M.M-∘ _ _)) ∙ sym (M.M-∘ _ _)) ⟩
      M.mult.η _ ∘ M.M₁ ((M.mult.η _ ∘ M.M₁ f) ∘ g) ∎
```

Constructing a monad from an extension system is simply a matter of
bolting together our results from the previous section.

```agda
  Extension-system→Monad : Extension-system C → Monad C
  Extension-system→Monad E = monad where
    module E = Extension-system E
    open Monad

    monad : Monad C
    monad .M = E.M
    monad .unit .η x = E.unit
    monad .unit .is-natural _ _ f = E.unit-natural f
    monad .mult .η x = E.join
    monad .mult .is-natural _ _ f = E.join-natural f
```

The monad laws follow from another short series of computations.

```agda
    monad .left-ident =
      E.bind id ∘ E.bind (E.unit ∘ E.unit) ≡⟨ E.bind-∘ _ _ ⟩
      E.bind (E.bind id ∘ E.unit ∘ E.unit) ≡⟨ ap E.bind (cancell (E.bind-unit-∘ id)) ⟩
      E.bind E.unit                        ≡⟨ E.bind-unit-id ⟩
      id                                   ∎
    monad .right-ident =
      E.bind id ∘ E.unit ≡⟨ E.bind-unit-∘ id ⟩
      id                 ∎
    monad .mult-assoc =
      E.bind id ∘ E.bind (E.unit ∘ E.bind id) ≡⟨ E.bind-∘ _ _ ⟩
      E.bind (E.bind id ∘ E.unit ∘ E.bind id) ≡⟨ ap E.bind (cancell (E.bind-unit-∘ id) ∙ sym (idr _)) ⟩
      E.bind (E.bind id ∘ id)                 ≡˘⟨ E.bind-∘ _ _ ⟩
      E.bind id ∘ E.bind id                   ∎
```

Moreover, these two functions constitute an equivalence between monads and
extension systems. In light of this fact, we will silently identify monads
and extension algebras whenever it is convenient.

```agda
  Monad≃Extension-system : Monad C ≃ Extension-system C
  Monad≃Extension-system = Iso→Equiv $
    Monad→Extension-system ,
    iso Extension-system→Monad
      (λ E →
        let module E = Extension-system E in
        Extension-system-path
          (λ _ → refl)
          (λ _ → refl)
          (λ f →
            E.bind id ∘ E.bind (E.unit ∘ f i0) ≡⟨ E.bind-∘ id (E.unit ∘ f i0) ⟩
            E.bind (E.bind id ∘ E.unit ∘ f i0) ≡⟨ ap E.bind (cancell (E.bind-unit-∘ id)) ⟩
            E.bind (f i0)                      ≡⟨ ap E.bind (coe0→1 (λ i → f i0 ≡ f i) refl) ⟩
            E.bind (f i1)                      ∎))
      (λ M →
        let module M = Monad M in
        Monad-path
          (λ _ → refl)
          (λ f →
            M.mult.η _ ∘ M.M₁ (M.unit.η _ ∘ f)        ≡⟨ pushr (M.M-∘ _ _) ⟩
            (M.mult.η _ ∘ M.M₁ (M.unit.η _)) ∘ M.M₁ f ≡⟨ eliml M.left-ident ⟩
            M.M₁ f ∎)
          (λ _ → refl)
          (λ _ → elimr M.M-id))
```

# Algebras over an extension system {defines=extension-algebra}

An **extension algebra** over $E$ is the extension system analog of a
[[algebra over a monad]]. Following the general theme of extension
operations, an extension algebra on $X : \cC$ is given by an operation
$\nu : \cC(A, X) \to \cC(M(A), X)$. Intuitively, this operation
lets us "evaluate" any $M$, so long as the codomain of the evaluation
is $X$.

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ)  where
  open Cat.Reasoning C
```
-->

```agda
  record Extension-algebra-on (E : Extension-system C) (x : Ob) : Type (o ⊔ ℓ) where
    no-eta-equality
    open Extension-system E
    field
      ν : ∀ {a} (f : Hom a x) → Hom (M₀ a) x
```

This operation must satisfy a pair of equations:

1. For every $f : \cC(A, X)$, $\nu(f) \circ \eta_{A} = f$
2. For every $f : \cC(B, X)$ and $g : \cC(A, M(b))$, $\nu(f) \circ g^M = \nu(\nu f \circ g)$.

```agda
      ν-unit : ∀ {a} (f : Hom a x) → ν f ∘ unit ≡ f
      ν-bind : ∀ {a b} (f : Hom b x) (g : Hom a (M₀ b)) → ν f ∘ bind g ≡ ν (ν f ∘ g)
```

From these, we can deduce a sort of naturality principle for $\nu$:

```agda
    ν-natural
      : ∀ {a b} (f : Hom b x) (g : Hom a b)
      → ν f ∘ M₁ g ≡ ν (f ∘ g)
    ν-natural f g =
      ν f ∘ bind (unit ∘ g) ≡⟨ ν-bind f (unit ∘ g) ⟩
      ν (ν f ∘ unit ∘ g)    ≡⟨ ap ν (pulll (ν-unit f)) ⟩
      ν (f ∘ g)  ∎

```

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} {E : Extension-system C} where
  open Cat.Reasoning C
  open Extension-system E
  open Extension-algebra-on
```
-->

<!--
```agda
  Extension-algebra-on-pathp
    : ∀ {x y}
    → (p : x ≡ y)
    → {α : Extension-algebra-on C E x} {β : Extension-algebra-on C E y}
    → (∀ {a} → (f : ∀ i → Hom a (p i)) → PathP (λ i → Hom (M₀ a) (p i)) (α .ν (f i0)) (β .ν (f i1)))
    → PathP (λ i → Extension-algebra-on C E (p i)) α β
  Extension-algebra-on-pathp {x} {y} p {α} {β} pν = sys where
    coe-ν : ∀ i → {a : Ob} → (f : Hom a (p i)) → Hom (M₀ a) (p i)
    coe-ν i {a} f = pν (λ j → coe (λ i → Hom a (p i)) i j f) i

    sys : PathP (λ i → Extension-algebra-on C E (p i)) α β
    sys i .ν f = coe-ν i f
    sys i .ν-unit {a} f =
      hcomp (∂ i) λ where
        j (i = i0) → Hom-set _ _ _ _ base (α .ν-unit f) j
        j (i = i1) → Hom-set _ _ _ _ base (β .ν-unit f) j
        j (j = i0) → base
      where
        base =
          coe0→i (λ i → (f : Hom a (p i)) → coe-ν i f ∘ unit ≡ f)
            i
            (α .ν-unit) f
    sys i .ν-bind {a} {b} f g =
      hcomp (∂ i) λ where
        j (i = i0) → Hom-set _ _ _ _ base (α .ν-bind f g) j
        j (i = i1) → Hom-set _ _ _ _ base (β .ν-bind f g) j
        j (j = i0) → base
      where
        base =
          coe0→i (λ i → (f : Hom b (p i)) → coe-ν i f ∘ bind g ≡ coe-ν i (coe-ν i f ∘ g))
            i
            (λ f → α .ν-bind f g) f
```
-->


## Equivalence with monad algebras

As the name suggests, extension algebras over $E$ are equivalent to
monad algebras over the canonical monad associated with $E$.

For the forward direction, let $\alpha : M(X) \to X$ be a monad algebra
over $E$. We can obtain the required extension operation $\nu$ by taking
$f : \cC(A, X)$ to $\alpha \circ M(f)$.

```agda
  Algebra-on→Extension-algebra-on
    : ∀ {x}
    → Algebra-on C (Extension-system→Monad E) x
    → Extension-algebra-on C E x
  Algebra-on→Extension-algebra-on {x = x} α = ext-alg where
    module α = Algebra-on α
    open Extension-algebra-on

    ext-alg : Extension-algebra-on C E x
    ext-alg .ν f = α.ν ∘ M₁ f
```

<details>
<summary>The monad algebra laws follow from some tedious calculations
that we shall omit.
</summary>

```agda
    ext-alg .ν-unit f =
      (α.ν ∘ M₁ f) ∘ unit ≡⟨ pullr (sym $ unit-natural f) ⟩
      α.ν ∘ unit ∘ f      ≡⟨ cancell α.ν-unit ⟩
      f ∎
    ext-alg .ν-bind f g =
      (α.ν ∘ M₁ f) ∘ bind g                    ≡⟨ pullr (bind-natural _ _) ⟩
      α.ν ∘ bind ⌜ M₁ f ∘ g ⌝                  ≡⟨ ap! (insertl (bind-unit-∘ id)) ⟩
      α.ν ∘ bind (join ∘ unit ∘ M₁ f ∘ g)      ≡⟨ pushr (sym (bind-∘ _ _)) ⟩
      (α.ν ∘ join) ∘ bind (unit ∘ M₁ f ∘ g)    ≡⟨ pushl (sym $ α.ν-mult) ⟩
      α.ν ∘ M₁ α.ν ∘ bind (unit ∘ M₁ f ∘ g)    ≡⟨ ap (α.ν ∘_) (bind-natural _ _) ⟩
      α.ν ∘ bind ⌜ M₁ α.ν ∘ unit ∘ M₁ f ∘ g ⌝  ≡⟨ ap! (centralizel (sym $ unit-natural _)) ⟩
      α.ν ∘ bind (unit ∘ (α.ν ∘ M₁ f) ∘ g)     ∎
```
</details>

Conversely, a monad algebra over $E$ can be derived from an extension
algebra $\nu : \cC(A, X) \to \cC(M(A), X)$ over $E$ by restricting to
$\nu(id_{X}) : \cC(M(X), X)$.

```agda
  Extension-algebra-on→Algebra-on
    : ∀ {x}
    → Extension-algebra-on C E x
    → Algebra-on C (Extension-system→Monad E) x
  Extension-algebra-on→Algebra-on {x = x} α = alg where
    module α = Extension-algebra-on α
    open Algebra-on

    alg : Algebra-on C (Extension-system→Monad E) x
    alg .ν = α.ν id
```

The proofs of the monad algebra laws are mercifully short.

```agda
    alg .ν-unit = α.ν-unit id
    alg .ν-mult =
      α.ν id ∘ M₁ (α.ν id) ≡⟨ α.ν-natural _ _ ⟩
      α.ν (id ∘ α.ν id)    ≡⟨ ap α.ν id-comm-sym ⟩
      α.ν (α.ν id ∘ id)    ≡˘⟨ α.ν-bind id id ⟩
      α.ν id ∘ join ∎
```

As expected, these two functions constitute an equivalence between monad
algebras and extension algebras.

```agda
  Algebra-on≃Extension-algebra-on
    : ∀ {x}
    → Algebra-on C (Extension-system→Monad E) x ≃ Extension-algebra-on C E x
  Algebra-on≃Extension-algebra-on {x} = Iso→Equiv $
    Algebra-on→Extension-algebra-on ,
    iso Extension-algebra-on→Algebra-on
      (λ α →
        let module α = Extension-algebra-on α in
        Extension-algebra-on-pathp refl λ f →
          α.ν id ∘ M₁ (f i0) ≡⟨ α.ν-natural _ _ ⟩
          α.ν (id ∘ f i0)    ≡⟨ ap α.ν (idl _) ⟩
          α.ν (f i0)         ≡⟨ ap α.ν (coe0→1 (λ i → f i0 ≡ f i) refl) ⟩
          α.ν (f i1)         ∎)
      (λ α →
        let module α = Algebra-on α in
        Algebra-on-pathp C refl $
          α.ν ∘ bind (unit ∘ id) ≡⟨ elimr (ap bind (idr _) ∙ bind-unit-id) ⟩
          α.ν                    ∎)
```
