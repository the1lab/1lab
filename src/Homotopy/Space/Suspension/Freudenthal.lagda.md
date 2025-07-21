<!--
```agda
open import 1Lab.Path.Reasoning
open import 1Lab.Prelude

open import Data.Nat.Properties
open import Data.Nat.Base

open import Homotopy.Space.Suspension.Properties
open import Homotopy.Space.Suspension
open import Homotopy.Connectedness
open import Homotopy.Truncation
open import Homotopy.Loopspace
open import Homotopy.Wedge
open import Homotopy.Base
```
-->

```agda
module Homotopy.Space.Suspension.Freudenthal where
```

# Freudenthal suspension theorem {defines="freudenthal-suspension-theorem"}

Recall that, if $A$ is a [[pointed type]][^point], the unit of the
[[suspension–loop space adjunction]] is a map $\sigma : A \to \Omega
\Susp A$, denoted `suspend`{.Agda} in code. If we're considering $A$
based at some other point $x : A$, we will write $\sigma_x$ instead.

[^point]:
  Throughout this page we will fix a [[pointed type]] $A$
  with basepoint $a_0$, and we will omit the distinction between $A$ and
  its underlying type.

The **Freudenthal suspension theorem** gives a bound on the failure of
this map to be an isomorphism. Precisely, it says that if $A$ is
$n$-[[connected]] with $n \ge 2$ then the suspension map $\sigma : A \to
\Omega \Susp A$ is $2(n - 1)$-connected. As a corollary, it induces an
[[equivalence]] of $2(n - 1)$-[[truncations]]
$$\| A \|_{2(n - 1)} \simeq \| \Omega \Susp A \|_{2(n - 1)}$$.

<!--
```agda
-- this line is unfortunately long but layout stacking doesn't work
-- unless it's all together like this :(
module freudenthal {ℓ} (A∙@(A , a₀) : Type∙ ℓ) (n : Nat) (conn : is-n-connected A (2 + n)) (let 2n = (suc n) + (suc n)) where
  ∥_∥₂ₙ : ∀ {ℓ} → Type ℓ → Type ℓ
  ∥ A ∥₂ₙ = n-Tr A 2n
```
-->

The proof we present is natively cubical, but the outline is the same as
the HoTT book proof [-@HoTT, sec. 8.6]: we will define a family
`code`{.Agda} over a point $x : \Susp A$ and path $p : x \is
\rm{north}$, satisfying
$$
\begin{align*}
\operatorname{code}(\rm{north}, p) &= \| \sigma^*(p) \|_{2(n - 1)} \\
\operatorname{code}(\rm{south}, p) &= \| \merid^*(p) \|_{2(n - 1)}\text{,}
\end{align*}
$$
and then show that $\operatorname{code}(\rm{south}, p)$ is contractible
at each $p$. We will start by giving a family of equivalences $i_a$,
over $a : A$, between the truncated fibres $\| \sigma^*(p) \|_{2(n -
1)}$ and $\| \sigma_a^*(p) \|_{2(n - 1)}$ over some $p : \rm{north} \is
\rm{north}$. We start by constructing an element of the latter fibre under the
assumptions that $b : A$ and $q : \sigma(b) = p$. By the [[wedge
connectivity]] lemma, it will suffice to do so when $a = a_0$ and $b =
a_0$, as long as our constructions agree when $a = a_0 = b$. When $b =
a_0$, we can show
$$
\sigma_a(a)
  = \merid{a} \cdot (\merid{a})\inv
  = \refl
  = \merid{a_0} \cdot (\merid{a_0})\inv
  = p
$$,
with the final step by our assumption of $q$; and when $a = a_0$ we are
immediately done. To show that these agree, we simply have to prove that
the round-trip between $\refl$ is the identity when $a = a_0$, but we
can easily arrange for those steps to cancel in this case.

```agda
  module wc (p : north ≡ north) =
    Wedge {A∙ = A∙} {A∙} {λ a b → suspend A∙ b ≡ p → ∥ fibre (suspend (A , a)) p ∥₂ₙ}
      n n conn conn (λ x y → hlevel 2n)
      (λ a q → inc (a , ∙-invr (merid a) ∙ sym (∙-invr (merid a₀)) ∙ q))
      (λ a q → inc (a , q))
      (funext λ x → ap (λ e → n-Tr.inc {n = 2n} (a₀ , e))
        (∙-cancell (sym (∙-invr (merid a₀))) x))
```

By truncation recursion, we can extend this to the function $i_a$
between fibres we promised. Since being an equivalence is a
[[proposition]] and $A$ is $(2 + n)$-connected, it will suffice to show
that $i_{a_0}$ is an equivalence; but in this case $i$ is the identity,
so we are done.

```agda
  fwd : ∀ p a → ∥ fibre (suspend A∙) p ∥₂ₙ → ∥ fibre (suspend (A , a)) p ∥₂ₙ
  fwd = elim! wc.elim

  fwd-is-equiv : ∀ p a → is-equiv (fwd p a)
```

<details>
<summary>Actually invoking these lemmas takes a bit of bureaucracy.</summary>

```agda
  fwd-is-equiv p a .is-eqv =
    let
      eqv = relative-n-type-const
        (λ a → ∀ t → is-contr (fibre (fwd p a) t))
        (λ _ → a₀) (suc n) (point-is-n-connected a₀ n conn)
        (λ x → hlevel (suc n))

      it : ∀ a (t : n-Tr (fibre (suspend A∙) p) 2n)
          → is-contr (fibre (fwd p a₀) t)
      it = elim! λ _ x q →
        subst (λ e → is-contr (fibre e (inc (x , q)))) {x = id} {y = _}
          (funext (elim! λ x → sym ∘ happly (wc.β₂ p x)))
          Singleton'-is-contr
    in Equiv.from (_ , eqv) it a
```

</details>

We can then use this equivalence to define the `code`{.Agda} family.
Here is when cubical type theory allows a significant simplification
over book HoTT: we can directly [[glue|glue type]] our equivalence along
a dependent identification `interpolate`{.Agda} between `suspend`{.Agda}
and `merid`{.Agda}, as in the diagram below (where we write $i$ for
`inv`{.Agda} and $\phi$ for `interpolate`{.Agda}).

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  {\| \sigma^*(p) \|_{2(n - 1)}} \&\&\&\& {\| \merid^*p \|_{2(n - 1)}} \\
  \\
  \\
  \\
  {\| \sigma_a^*p\|_{2(n - 1)}} \&\&\&\& {\| \merid^*p \|_{2(n-1)}}
  \arrow[equals, dashed, from=1-1, to=1-5]
  \arrow["i"{description}, from=1-1, to=5-1]
  \arrow["{\rm{Glue}\dots}"{description}, draw=none, from=1-1, to=5-5]
  \arrow["\id"{description}, from=1-5, to=5-5]
  \arrow["{\| \phi(a,j)^*p\|_{2(n-1)}}"', equals, from=5-1, to=5-5]
\end{tikzcd}\]
~~~

Constructing this dependent identification is very easy, and so
everything falls together as usual.

```agda
  interpolate
    : ∀ {ℓ} {A : Type ℓ} (a : A)
    → PathP (λ i → A → north ≡ merid a i) (suspend (A , a)) merid
  interpolate a i x j = ∙-filler (merid x) (sym (merid a)) (~ i) j

  code : (y : Susp A) → north ≡ y → Type ℓ
  code north p = ∥ fibre (suspend A∙) p ∥₂ₙ
  code south p = ∥ fibre merid p        ∥₂ₙ
  code (merid a i) p = Glue ∥ fibre (interpolate a i) p ∥₂ₙ λ where
    (i = i0) → ∥ fibre (suspend A∙) p ∥₂ₙ , fwd p a , fwd-is-equiv p a
    (i = i1) → ∥ fibre merid p        ∥₂ₙ , id≃
```

By path induction, each $\rm{code}(y, p)$ is inhabited. We will now show
that each $\operatorname{code}(\rm{south}, p)$ is contractible, with
centre the `encoding`{.Agda ident=encode} of $p$. By truncation
induction we can assume we have $a : A$ and $r : \merid{a} = p$, and by
path induction on $r$ we can assume $p$ is $\merid{a}$, so that our goal
is showing $\operatorname{encode}(\rm{south}, \merid{a})$ is $(a,
\refl)$. This is a simple, if tedious, calculation.

```agda
  encode : (y : Susp A) (p : north ≡ y) → code y p
  encode y = J code (inc (a₀ , ∙-invr (merid a₀)))

  encode-paths : ∀ p (c : ∥ fibre merid p ∥₂ₙ) → encode south p ≡ c
  encode-paths p = elim! λ a → J (λ p r → encode south p ≡ inc (a , r))
    let
      gp i = n-Tr (fibre (interpolate a i) (λ j → merid a (i ∧ j))) 2n

      rem₁ =
        wc.elim refl a a₀ (∙-invr (merid a₀))
          ≡⟨ happly (wc.β₁ refl a) (∙-invr (merid a₀)) ⟩
        inc (a , ∙-invr (merid a) ∙ sym (∙-invr (merid a₀)) ∙ ∙-invr (merid a₀))
          ≡⟨ ap (λ e → n-Tr.inc (a , e)) (∙-elimr (∙-invl (∙-invr (merid a₀)))) ⟩
        inc (a , ∙-invr (merid a))
          ∎

      rem₂ =
        transport gp (fwd refl a (inc (a₀ , ∙-invr (merid a₀))))
          ≡⟨ ap (transport gp) rem₁ ⟩
        transport gp (inc (a , ∙-invr (merid a)))
          ≡⟨ from-pathp {A = λ i → gp i} (λ i → inc (a , λ j k → ∙-invr-filler (merid a) j k (~ i))) ⟩
        inc (a , refl) ∎
    in rem₂
```

By definition, this proof shows that $\merid$ is an $2(n - 1)$ connected
map, because the $2(n - 1)$-truncations of its fibres are contractible.
We have also essentially already shown our main theorem, since we have
an identification between the fibres of `merid`{.Agda} and those of
`suspend`{.Agda}.

```agda
  merid-is-n-connected : is-n-connected-map merid 2n
  merid-is-n-connected x = n-connected.from (n + suc n) record
    { centre = encode south x
    ; paths  = encode-paths x
    }
```

<!--
```agda
module
  _ {ℓ} {A∙@(A , a₀) : Type∙ ℓ} (n : Nat) (conn : is-n-connected A (2 + n)) where

  open freudenthal A∙ n conn
```
-->

```agda
  suspend-is-n-connected : is-n-connected-map (suspend A∙) (suc n + suc n)
  suspend-is-n-connected = transport
    (λ i → is-n-connected-map (λ z → interpolate a₀ (~ i) z) (suc n + suc n))
    merid-is-n-connected

  freudenthal-equivalence
    : n-Tr∙ A∙ (suc n + suc n) ≃∙ n-Tr∙ (Ωⁿ 1 (Σ¹ A∙)) (suc n + suc n)
  freudenthal-equivalence .fst .fst = _
  freudenthal-equivalence .fst .snd = is-n-connected-map→is-equiv-tr
    _ _ suspend-is-n-connected
  freudenthal-equivalence .snd = ap n-Tr.inc (∙-invr (merid a₀))
```
