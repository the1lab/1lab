<!--
```agda
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Functor.Reasoning.Presheaf as PSh

open Functor
open _=>_
```
-->

```agda
module Cat.Functor.Hom.Yoneda where
```

# The Yoneda lemma

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} (A : Functor (C ^op) (Sets ℓ)) where
  private module A = PSh A using (expand ; elim)
  open Precategory C
```
-->

The Yoneda lemma says that the set of *sections* $A(U)$ of a presheaf
$A$ is isomorphic to the set $\cC(-, U) \To A$ of natural
transformations into $A$, with domain a $\hom$-functor; and that this
isomorphism is natural. This result is actually extremely easy to prove,
as long as we expand *what* a natural transformation $\eta : \cC(-, U)
\To A$ consists of: a dependent function
$$\eta : \prod_{V : \cC} \cC(V, U) \to A(V)$$.

There's no secret in choosing the components of the isomorphism:

- Given a $x : A(U)$, we define a natural transformation
  $\operatorname{yo} x$ by sending a map $h : \cC(V, U)$ to the
  restriction $A(h)(x) : A(V)$.

```agda
  yo : ∀ {U} → A ʻ U → Hom-into C U => A
  yo a .η i h = A ⟪ h ⟫ a
  yo a .is-natural x y f = ext λ h → A.expand refl
```

- Given an $\eta : \cC(-, U) \To A$, we obtain a value
  $\eta_U(\id) : A(U)$.

```agda
  unyo : ∀ {U} → Hom-into C U => A → A ʻ U
  unyo h = h .η _ id
```

This inverse explains why the Yoneda lemma is sometimes stated as
"natural transformations (from a representable) are determined by their
component at the identity". These inverse equivalences compose to give
expressions which are easy to cancel using naturality and functoriality:

```agda
  yo-is-equiv : ∀ {U} → is-equiv (yo {U})
  yo-is-equiv = is-iso→is-equiv λ where
    .is-iso.inv  n → unyo n
    .is-iso.rinv x → ext λ i h →
      yo (unyo x) .η i h ≡˘⟨ x .is-natural _ _ _ # _ ⟩
      x .η i (id ∘ h)    ≡⟨ ap (x .η i) (idl h) ⟩
      x .η i h           ∎
    .is-iso.linv x →
      A ⟪ id ⟫ x ≡⟨ A.elim refl ⟩
      x          ∎
```

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} {A : Functor (C ^op) (Sets ℓ)} where
  private module A = PSh A
  open Precategory C
```
-->

## Naturality

The only part of the Yoneda lemma which is slightly tricky is working
out the naturality statements. Since the isomorphism
$$
(\cC(-,U) \To A) \simeq A(U)
$$
is natural in both $A$ and $U$, there are two statements. We implement
the proofs of naturality for the $\operatorname{yo}$-
$\operatorname{unyo}$ isomorphism as *combinators*, so that they can
slot into bigger proofs more easily. Calling these combinators $\refl$
gives back the familiar naturality results.

For naturality "on the right", i.e. in the $U$ coordinate, naturality
says that given $h : V \to U$, we have for all $x$,
$$
\operatorname{yo}(x) \circ \cC(-, h) = \operatorname{yo}(A(h)(x))
$$.

```agda
  yo-natr
    : ∀ {U V} {x : A ʻ U} {h : Hom V U} {y}
    → A ⟪ h ⟫ x ≡ y
    → yo A x ∘nt よ₁ C h ≡ yo A y
  yo-natr p = ext λ i f → A.expand refl ∙ A.ap p

  yo-naturalr
    : ∀ {U V} {x : A ʻ U} {h : Hom V U}
    → yo A x ∘nt よ₁ C h ≡ yo A (A ⟪ h ⟫ x)
  yo-naturalr = yo-natr refl
```

On "the left", i.e. in the variable $A$, naturality says that, given a
natural transformation $\eta : A \To B$, we have
$$
\eta \circ \operatorname{yo}_A(x) = \operatorname{yo}_B(\eta_U(x))
$$,
as natural transformations $\cC(-,U) \To B$, for any $x : A(U)$.

```agda
  yo-natl
    : ∀ {B : Functor (C ^op) (Sets ℓ)} {U} {x : A ʻ U} {y : B ʻ U} {h : A => B}
    → h .η U x ≡ y → h ∘nt yo {C = C} A x ≡ yo B y
  yo-natl {B = B} {h = h} p = ext λ i f → h .is-natural _ _ _ # _ ∙ PSh.ap B p

  yo-naturall
    : ∀ {B : Functor (C ^op) (Sets ℓ)} {U} {x : A ʻ U} {h : A => B}
    → h ∘nt yo {C = C} A x ≡ yo B (h .η U x)
  yo-naturall = yo-natl refl
```

<!--
```agda
  unyo-path : ∀ {U : ⌞ C ⌟} {x y : A ʻ U} → yo {C = C} A x ≡ yo A y → x ≡ y
  unyo-path {x = x} {y} p =
    x          ≡⟨ A.intro refl ⟩
    A ⟪ id ⟫ x ≡⟨ unext p _ id ⟩
    A ⟪ id ⟫ y ≡⟨ A.elim refl ⟩
    y          ∎
```
-->
