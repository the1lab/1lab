<!--
```agda
open import 1Lab.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Group.Ab
open import Algebra.Group

open import Homotopy.Space.Delooping
open import Homotopy.Space.Circle
open import Homotopy.Conjugation
```
-->

```agda
module Homotopy.HSpace where
```

# H-Spaces

:::{.definition #h-space}
An **H-space** structure on a [[pointed type]] $(A, a_0)$ consists of a
binary operation $\mu : A \to A \to A$ equipped with paths $\lambda_x :
\mu(a_0, x) \is x$ and $\rho_x : \mu(x, a_0) \is x$ witnessing left- and
right- unitality of $\mu$, respectively, together with a coherence datum
connecting $\lambda_{a_0} \is \rho_{a_0}$.
:::

```agda
record HSpace {ℓ} (A* : Type∙ ℓ) : Type ℓ where
  open Σ A* renaming (fst to A ; snd to a₀)
  field
    μ : A → A → A

    idl    : ∀ x → μ a₀ x ≡ x
    idr    : ∀ x → μ x a₀ ≡ x
    id-coh : idl a₀ ≡ idr a₀
```

Here, we're interested in the case where each $\mu(-, x)$ is an
[[equivalence]], so we're really discussing **right-invertible
h-spaces.** We note that if $A$ is [[connected]] then
any of its H-space structures is automatically both left- and
right-invertible. This is because, since "being an equivalence" is a
[[proposition]], it would suffice to check invertibility when $x$ is the
basepoint, but in this case $\mu(-,a_0)$ is the identity.

```agda
    inv : ∀ x → is-equiv (λ y → μ y x)
```

Using either unit law (we choose $\lambda$), we can show that $\mu$
extends to a secondary 'composition' operation on the [[loop space]]
$\Omega A$. This operation is also unital on both the left and the
right, with the side we *didn't* choose having a slightly more
complicated argument that involves the coherence $\lambda_{a_0} =
\rho_{a_0}$.

```agda
  _⊗_ : a₀ ≡ a₀ → a₀ ≡ a₀ → a₀ ≡ a₀
  p ⊗ q = conj (idl a₀) (ap₂ μ p q)

  ⊗-idl : ∀ p → refl ⊗ p ≡ p
  ⊗-idl p = square→conj (ap (λ e → ap e p) (funext idl))

  ⊗-idr : ∀ p → p ⊗ refl ≡ p
  ⊗-idr p =
    conj (idl a₀) (ap₂ μ p refl) ≡⟨ ap (λ e → conj e (ap₂ μ p refl)) id-coh ⟩
    conj (idr a₀) (ap₂ μ p refl) ≡⟨ square→conj (ap (λ e → ap e p) (funext idr)) ⟩
    p                            ∎
```

Moreover, this new operation satisfies an 'interchange' law, in that it
preserves path composition in both variables. By an incoherent version
of the [[Eckmann-Hilton argument]], this means that composition of loops
in $\Omega A$ is commutative. This implies that the only connected
[[groupoids]] with H-space structures are the [[deloopings]] of
[[abelian groups]].

```agda
  ⊗-interchange : ∀ a b c d → (a ∙ b) ⊗ (c ∙ d) ≡ (a ⊗ c) ∙ (b ⊗ d)
  ⊗-interchange a b c d =
    conj (idl a₀) (ap₂ μ (a ∙ b) (c ∙ d))
      ≡⟨ ap (conj (idl a₀)) (ap₂-∙ μ a b c d) ⟩
    conj (idl a₀) (ap₂ μ a c ∙ ap₂ μ b d)
      ≡⟨ conj-of-∙ (idl a₀) _ _ ⟩
    (a ⊗ c) ∙ (b ⊗ d)
      ∎
```

<details>
<summary>We omit the proof here because it's the same algebra as in the
case for set-level magmas.</summary>

```agda
  private
    ∙-is-flip-⊗ : (p q : a₀ ≡ a₀) → p ∙ q ≡ q ⊗ p
    ∙-is-flip-⊗ p q =
      p ∙ q                   ≡˘⟨ ap₂ _∙_ (⊗-idl p) (⊗-idr q) ⟩
      (refl ⊗ p) ∙ (q ⊗ refl) ≡⟨ sym (⊗-interchange refl q p refl) ⟩
      (refl ∙ q) ⊗ (p ∙ refl) ≡⟨ ap₂ _⊗_ (∙-idl q) (∙-idr p) ⟩
      q ⊗ p                   ∎

    ∙-is-⊗ : (p q : a₀ ≡ a₀) → p ∙ q ≡ p ⊗ q
    ∙-is-⊗ p q =
      p ∙ q                   ≡˘⟨ ap₂ _∙_ (⊗-idr p) (⊗-idl q) ⟩
      (p ⊗ refl) ∙ (refl ⊗ q) ≡⟨ sym (⊗-interchange p refl refl q) ⟩
      (p ∙ refl) ⊗ (refl ∙ q) ≡⟨ ap₂ _⊗_ (∙-idr p) (∙-idl q) ⟩
      (p ⊗ q)                 ∎

  ∙-comm : (p q : a₀ ≡ a₀) → p ∙ q ≡ q ∙ p
  ∙-comm p q = ∙-is-flip-⊗ p q ∙ sym (∙-is-⊗ q p)
```

</details>

<!--
```agda
open HSpace

module _ {ℓ} (G : Group ℓ) (ab : is-commutative-group G) where
  open Group-on (G .snd)

  private
```
-->

## H-Space structures on deloopings

We can define an H-space structure on the [[delooping]] $\B G$ of an
[[abelian group]] by recursion. First, we fix an element $g : G$ and
define the "path" case, by elimination into sets --- so it suffices to
turn a $g : G$ into a $\rm{base} \is \rm{base}$, and to show that this
is commutative.

```agda
    mul₀ : (x : ⌞ G ⌟) (y : Deloop G) → y ≡ y
    mul₀ g = Deloop-elim-set G _ (λ d → hlevel 2)
      (path g)
      (λ z → commutes→square (Deloop-ab.∙-comm G ab _ _))
```

Now we extend this to when $x$ is an arbitrary element of $\B G$. At the
basepoint, we can simply return the other operand; this ensures identity
on the left is definitional. For the generating paths, we can use the
helper defined above. To show that this respects multiplication, we can
lift the generating triangle `pathᵀ`{.Agda} to `mul₀`{.Agda} by
elimination into propositions. The truncation case is handled automatically.

```agda
    coh : (x y : ⌞ G ⌟) (z : Deloop G) → Square refl (mul₀ x z) (mul₀ (x ⋆ y) z) (mul₀ y z)
    coh x y = Deloop-elim-prop G _ (λ _ → hlevel 1) λ i j → pathᵀ x y i j

    mul : Deloop G → Deloop G → Deloop G
    mul base            x = x
    mul (path x i)      y = mul₀ x y i
    mul (pathᵀ x y i j) z = coh x y z i j
    mul (squash x y p q α β i j k) z = squash (mul x z) (mul y z)
      (λ i → mul (p i) z) (λ i → mul (q i) z)
      (λ i j → mul (α i j) z)
      (λ i j → mul (β i j) z) i j k
```

By elimination into sets we can prove that `mul`{.Agda} is also unital
on the right. For the base case this is once again definitional, and for
the `path`{.Agda} case we're left with filling a degenerate square which
is `path`{.Agda} in one direction.

```agda
    mul-idr : ∀ x → mul x base ≡ x
    mul-idr = Deloop-elim-set G _ (λ _ → hlevel 2) refl (λ z i j → path z i)
```

Finally, for invertibility, it suffices to check `mul`{.Agda} is an
equivalence at the basepoint, in which case our proof above reduces this
to showing the identity function is an equivalence.

```agda
  HSpace-BG : HSpace (Deloop∙ G)
  HSpace-BG .μ      = mul
  HSpace-BG .idl x  = refl
  HSpace-BG .idr    = mul-idr
  HSpace-BG .id-coh = refl
  HSpace-BG .inv    = Deloop-elim-prop G _ (λ _ → hlevel 1) $
    subst is-equiv (sym (funext mul-idr)) id-equiv
```

## On the circle

We can specialise the discussion above to the [[circle]], in which case
we already have many of the components ready. All that remains is to
parametrise `always-loop`{.Agda} by an extra argument of circle type,
promoting it to a 'multiplication'; and to define the 'inverse' map on
$S^1$.

```agda
mulS¹ : S¹ → S¹ → S¹
mulS¹ = S¹-elim (λ x → x) (funext always-loop)

invS¹ : S¹ → S¹
invS¹ base     = base
invS¹ (loop i) = loop (~ i)
```

<!--
```agda
private
  mulS¹-idr : ∀ x → mulS¹ x base ≡ x
  mulS¹-idr = S¹-elim refl (λ i j → loop i)

HSpace-S¹ : HSpace (S¹ , base)
HSpace-S¹ .μ      = mulS¹
HSpace-S¹ .idl x  = refl
HSpace-S¹ .idr    = mulS¹-idr
HSpace-S¹ .id-coh = refl
HSpace-S¹ .inv x =
  is-iso→is-equiv λ where
    .is-iso.from y → mulS¹ (invS¹ x) y
    .is-iso.rinv y → p x y
    .is-iso.linv y → r (invS¹ x) y x ∙ p x y
  where
    p : ∀ x y → mulS¹ (mulS¹ (invS¹ x) y) x ≡ y
    p = S¹-elim mulS¹-idr (funextP (S¹-elim (λ i j → hfill (∂ i) (~ j) (λ { k (k = i0) → base ; k (i = i0) → loop (~ i ∨ k) ; k (i = i1) → loop (~ i ∧ k) })) prop!))

    r : ∀ x y z → mulS¹ x (mulS¹ y z) ≡ mulS¹ (mulS¹ x y) z
    r = S¹-elim (λ y z → refl) (funextP (S¹-elim (funextP (S¹-elim (λ i j → loop i) prop!)) prop!))
```
-->
