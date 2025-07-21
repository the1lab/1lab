<!--
```agda
open import 1Lab.Path.Cartesian
open import 1Lab.Prelude

open import Data.Set.Truncation

open import Homotopy.Connectedness.Automation
open import Homotopy.Space.Suspension
open import Homotopy.Connectedness
open import Homotopy.Space.Sphere
open import Homotopy.Truncation
open import Homotopy.Base
```
-->

```agda
module Homotopy.Space.Suspension.Properties where
```

# Properties of suspensions

## Connectedness {defines="connectedness-of-suspensions"}

The suspension operation increases the
[[connectedness]] of spaces: if $A$ is $n$-connected, then $\Susp A$ is
$(1+n)$-connected. Unfolding this a bit further, if $A$ is a type whose
homotopy groups below $n$ are trivial, then $\Susp A$ will have trivial
homotopy groups below $1 + n$.

```agda
Susp-is-connected
  : ∀ {ℓ} {A : Type ℓ} n
  → is-n-connected A n → is-n-connected (Susp A) (suc n)
Susp-is-connected 0 a-conn = inc north
Susp-is-connected 1 a-conn = ∥-∥-out! do
  pt ← a-conn
  pure $ is-connected∙→is-connected λ where
    north       → inc refl
    south       → inc (sym (merid pt))
    (merid x i) → is-prop→pathp (λ i → ∥_∥.squash {A = merid x i ≡ north})
      (inc refl) (inc (sym (merid pt))) i
Susp-is-connected {A = A} (suc (suc n)) a-conn =
  n-Tr-elim
    (λ _ → is-n-connected (Susp A) (3 + n))
    (λ _ → is-prop→is-hlevel-suc {n = suc n} (hlevel 1))
    (λ x → contr (inc north) (n-Tr-elim _ (λ _ → is-hlevel-suc (2 + n) (n-Tr-is-hlevel (2 + n) _ _))
      (Susp-elim _ refl (ap n-Tr.inc (merid x)) λ pt →
        commutes→square (ap (refl ∙_) (rem₂ .snd _ ∙ sym (rem₂ .snd _))))))
    (conn' .centre)
  where
    conn' : is-contr (n-Tr A (2 + n))
    conn' = is-n-connected-Tr (1 + n) a-conn

    rem₁ : is-equiv λ b a → b
    rem₁ = is-n-connected→n-type-const
      {B = n-Tr.inc {n = 3 + n} north ≡ inc south} {A = A}
      (suc n) (hlevel (2 + n)) a-conn

    rem₂ : Σ (inc north ≡ inc south) (λ p → ∀ x → ap n-Tr.inc (merid x) ≡ p)
    rem₂ = _ , λ x → sym (rem₁ .is-eqv _ .centre .snd) $ₚ x
```

As a direct corollary, the $n$-sphere is $(n-1)$-connected (remember that our
indices are offset by 2).

```agda
Sⁿ⁻¹-is-connected : ∀ n → is-n-connected (Sⁿ⁻¹ n) n
Sⁿ⁻¹-is-connected zero = _
Sⁿ⁻¹-is-connected (suc n) = Susp-is-connected n (Sⁿ⁻¹-is-connected n)
```

<!--
```agda
instance
  Connected-Susp : ∀ {ℓ} {A : Type ℓ} {n} → ⦃ Connected A n ⦄ → Connected (Susp A) (suc n)
  Connected-Susp {n = n} ⦃ conn-instance c ⦄ = conn-instance (Susp-is-connected n c)
```
-->

## Truncatedness

While there is no similarly pleasant characterisation of the [[truncatedness]]
of suspensions^[for instance, while the [[circle]] is a groupoid, its suspension,
the 2-[[sphere]], is not $n$-truncated for any $n$], we can give a few special cases.

First, the suspension of a contractible type is contractible.

```agda
Susp-is-contr
  : ∀ {ℓ} {A : Type ℓ}
  → is-contr A → is-contr (Susp A)
Susp-is-contr c .centre = north
Susp-is-contr c .paths north = refl
Susp-is-contr c .paths south = merid (c .centre)
Susp-is-contr c .paths (merid a i) j = hcomp (∂ i ∨ ∂ j) λ where
  k (k = i0) → merid (c .centre) (i ∧ j)
  k (i = i0) → north
  k (j = i0) → north
  k (i = i1) → merid (c .centre) j
  k (j = i1) → merid (c .paths a k) i
```

Notice the similarity with the proof that [the $\infty$-sphere is contractible]:
that argument is essentially a recursive version of this one, since $S^\infty$ is
its own suspension.

[the $\infty$-sphere is contractible]: Homotopy.Space.Sinfty.html#the-cubical-approach

Going up a level, we do *not* have that the suspension of a proposition is a proposition
(think of the suspension of $\bot$), but we *do* have that the suspension of a
proposition is a *set*.

```agda
module _ {ℓ} {A : Type ℓ} (prop : is-prop A) where
```

We start by defining a helper induction principle: in order to map out of
$\Sigma A \times \Sigma A$, it suffices to give values at the four poles, and,
assuming $A$ holds, a square over the meridians with the given corners.

```agda
  Susp-prop-elim²
    : ∀ {ℓ} {B : Susp A → Susp A → Type ℓ}
    → (bnn : B north north) (bns : B north south)
    → (bsn : B south north) (bss : B south south)
    → ((a : A) → (i j : I) → B (merid a i) (merid a j)
        [ _ ↦ (λ { (i = i0) (j = i0) → bnn
                 ; (i = i0) (j = i1) → bns
                 ; (i = i1) (j = i0) → bsn
                 ; (i = i1) (j = i1) → bss }) ])
    → ∀ a b → B a b
  Susp-prop-elim² bnn bns bsn bss bm = Susp-elim _
    (Susp-elim _ bnn bns λ a j → outS (bm a i0 j))
    (Susp-elim _ bsn bss λ a j → outS (bm a i1 j))
    λ a → funextP (Susp-elim _
      (λ i → outS (bm a i i0))
      (λ i → outS (bm a i i1))
      (subst-prop prop a (λ j i → outS (bm a i j))))
```

Then, we use the usual machinery of identity systems: we define a type family
of "codes" of equality for $\Sigma A$. Its values are either $\top$ for equal poles
or $A$ for different poles, and we fill the square using univalence.

```agda
  private
    Code : Susp A → Susp A → Type ℓ
    Code = Susp-prop-elim² (Lift _ ⊤) A A (Lift _ ⊤)
      λ a i j → inS (double-connection (sym (A≡⊤ a)) (A≡⊤ a) i j)
      where
        A≡⊤ : A → A ≡ Lift _ ⊤
        A≡⊤ a = ua (prop-ext prop (hlevel 1) _ (λ _ → a))
```

We've defined a reflexive family of propositions:

```agda
    Code-is-prop : ∀ a b → is-prop (Code a b)
    Code-is-prop = Susp-elim-prop (λ _ → hlevel 1)
      (Susp-elim-prop (λ _ → hlevel 1) (hlevel 1) prop)
      (Susp-elim-prop (λ _ → hlevel 1) prop (hlevel 1))

    Code-refl : ∀ a → Code a a
    Code-refl = Susp-elim-prop (λ a → Code-is-prop a a) _ _
```

Thus all that remains is to prove that it implies equality. At the poles, we can
use `refl`{.Agda} and `merid`{.Agda}.

<!--
```agda
    _ = I-interp
```
-->

```agda
    decode : ∀ a b → Code a b → a ≡ b
    decode = Susp-prop-elim²
      (λ _ → refl)          (λ c → merid c)
      (λ c → sym (merid c)) (λ _ → refl)
```

This time, if $A$ holds, we have to fill a *cube* with the given four edges:

~~~{.quiver}
\[\begin{tikzcd}
	N &&& S \\
	& N & N \\
	& S & S \\
	N &&& S
	\arrow[Rightarrow, no head, from=2-2, to=1-1]
	\arrow["{\mathrm{merid}\ c}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=2-3, to=1-4]
	\arrow[Rightarrow, no head, from=2-2, to=2-3]
	\arrow["{\mathrm{merid}\ a}"', color={rgb,255:red,153;green,92;blue,214}, from=2-2, to=3-2]
	\arrow[Rightarrow, no head, from=3-2, to=3-3]
	\arrow["{\mathrm{merid}\ a}", color={rgb,255:red,153;green,92;blue,214}, from=2-3, to=3-3]
	\arrow["{\mathrm{merid}\ a}", color={rgb,255:red,153;green,92;blue,214}, from=1-1, to=1-4]
	\arrow[Rightarrow, no head, from=1-4, to=4-4]
	\arrow["{\mathrm{merid}\ a}"', color={rgb,255:red,153;green,92;blue,214}, from=4-1, to=4-4]
	\arrow[Rightarrow, no head, from=3-3, to=4-4]
	\arrow["{\mathrm{merid}\inv\ c}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=3-2, to=4-1]
	\arrow[Rightarrow, no head, from=1-1, to=4-1]
\end{tikzcd}\]
~~~

Notice that we have two different meridians: $a$ comes from our assumption that $A$
holds, whereas $c$ comes from the function out of codes we're trying to build.
If $a$ and $c$ were the same, we could simply fill this cube by
`interpolating`{.Agda ident=I-interp} between $i$ and $j$ along $k$. However, we can
take a shortcut: since we've assumed $A$ holds, and $A$ is a proposition, then $A$
is contractible, and we've `shown`{.Agda ident=Susp-is-contr} that the suspension
of a contractible type is contractible, so we can trivially
`extend`{.Agda ident=is-contr→extend} our partial system to fill the desired cube!

```agda
      λ a i j → is-contr→extend
        (Π-is-hlevel 0 (λ _ → Path-is-hlevel 0
          (Susp-is-contr (is-prop∙→is-contr prop a))))
        (∂ i ∧ ∂ j) _
```

This concludes the proof that $\Sigma A$ is a set with $(N \equiv S) \simeq A$.

```agda
    Code-ids : is-identity-system Code Code-refl
    Code-ids = set-identity-system Code-is-prop (decode _ _)

  opaque
    Susp-prop-is-set : is-set (Susp A)
    Susp-prop-is-set = identity-system→hlevel 1 Code-ids Code-is-prop

  Susp-prop-path : Path (Susp A) north south ≃ A
  Susp-prop-path = identity-system-gives-path Code-ids e⁻¹
```
