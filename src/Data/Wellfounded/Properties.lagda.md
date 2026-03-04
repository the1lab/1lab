<!--
```agda
open import 1Lab.Prelude

open import Data.Wellfounded.Base
open import Data.Nat.Order
open import Data.Nat.Base
```
-->

```agda
module Data.Wellfounded.Properties where
```

It was mentioned in the definition of `Acc`{.Agda} that being accessible
is a proposition, but this has not yet been established. We can do so
using, as usual, induction:

<!--
```agda
private variable
  ℓ ℓr ℓs : Level
  A B : Type ℓ
  R S : A → A → Type ℓ
```
-->

```agda
Acc-is-prop : ∀ x → is-prop (Acc R x)
Acc-is-prop x (acc s) (acc t) =
  ap acc (ext λ y y<x → Acc-is-prop y (s y y<x) (t y y<x))

Wf-is-prop : is-prop (Wf R)
Wf-is-prop = Π-is-hlevel 1 Acc-is-prop
```

## Instances

The usual induction principle for the natural numbers is equivalent to
saying that the relation $R(x,y) := y = 1+x$ is well-founded.
Additionally, the relation $<$ on the natural numbers is well-founded.

```agda
suc-wf : Wf (λ x y → y ≡ suc x)
suc-wf = Induction-wf (λ x y → y ≡ suc x) λ P m →
  Nat-elim P
    (m 0 λ y 0=suc → absurd (zero≠suc 0=suc))
    λ {n} Pn → m (suc n) (λ y s → subst P (suc-inj s) Pn)

<-wf : Wf _<_
<-wf x = go x x ≤-refl where
  go : (x y : Nat) → .(y ≤ x) → Acc _<_ y
  go x zero w = acc λ _ ()
  go (suc x) (suc y) w = acc k' where
    k' : ∀ x → x < suc y → Acc _<_ x
    k' x' w' = go x x' (≤-trans (≤-peel w') (≤-peel w))
```

Let $(A, R)$ and $(B, S)$ be a pair of types equipped with relations,
and $f : A \to B$ be a map that satisfies

$$
\forall x y.\ R(x, y) \to S(f(x), f(y))
$$.

If $S$ is a well-founded relation on $B$, then $R$ must also be well-founded.

```agda
reflect-wf
  : Wf S
  → (f : A → B)
  → (∀ {x y} → R x y → S (f x) (f y))
  → Wf R
```

The idea here is to use the fact that every $b$ in the image of $f$ must be accessible.
Let $a : A$, $b : B$ such that $f(a) = b$ and $b$ is accessible via $S$. To show that
$a$ is accessible via $R$, we must show that $a'$ is accessible for every $R(a', a)$. However,
monotonicity of $f$ means that $S(f(a'), f(a))$, and $f(a) = b$, which means that $f(a')$ must
be accessible via $S$. We can then recurse to show that $a'$ is accessible.

```agda
reflect-wf {B = B} {S = S} {A = A} {R = R} S-wf f f-mono a = im-acc (f a) a refl (S-wf (f a)) where
  im-acc : (b : B) (a : A) → f a ≡ b → Acc S b → Acc R a
  im-acc b a fa=b (acc rec) = acc λ a' R[a',a] →
    im-acc (f a') a' refl (rec (f a') (subst (S (f a')) fa=b (f-mono R[a',a])))
```

As a corollary, we can pull back accessibility along arbitrary functions.

```agda
pullback-wf
  : (f : A → B)
  → Wf R
  → Wf (λ x y → R (f x) (f y))
pullback-wf f R-wf = reflect-wf R-wf f id
```
