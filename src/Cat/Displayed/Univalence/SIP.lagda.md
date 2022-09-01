```agda
open import Cat.Displayed.Univalence
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Fibre
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Univalent
open import Cat.Prelude

module Cat.Displayed.Univalence.SIP where
```

<!--
```agda
open Precategory
open Displayed
open _≅[_]_
```
-->

# The Structure Identity Principle

The HoTT Book's version of the structure identity principle can be seen
as a very early example of displayed category theory. Their notion of
_standard notion of structure_ corresponds exactly to a displayed
category, all of whose fibres are posets. Note that this is not a
category _fibred in_ posets, since the displayed category will not
necessarily be a Cartesian fibration.

```agda
module _
  {o ℓ o′ ℓ′} {B : Precategory o ℓ}
  (S : B .Ob → Type o′)
  (H : ∀ {x y} → B .Hom x y → S x → S y → Prop ℓ′)
  (H-id : ∀ {x} {s : S x} → ∣ H (B .id) s s ∣)
  (H-∘ : ∀ {x y z} {s t u} (f : B .Hom y z) (g : B .Hom x y)
       → ∣ H f t u ∣ → ∣ H g s t ∣ → ∣ H (B ._∘_ f g) s u ∣)
  where
```

The data above conspires to make a category displayed over $\ca{B}$. The
laws are trivial since $H$ is valued in propositions.

```agda
  structures : Displayed B o′ ℓ′
  structures .Ob[_] = S
  structures .Hom[_] f x y = ∣ H f x y ∣
  structures .Hom[_]-set f a b = is-prop→is-set (H f a b .is-tr)
  structures .id′ = H-id
  structures ._∘′_ = H-∘ _ _
  structures .idr′ f′ = is-prop→pathp (λ i → H (B .idr _ i) _ _ .is-tr) _ _
  structures .idl′ f′ = is-prop→pathp (λ i → H (B .idl _ i) _ _ .is-tr) _ _
  structures .assoc′ f′ g′ h′ =
    is-prop→pathp (λ i → H (B .assoc _ _ _ i) _ _ .is-tr) _ _
```

We recall that the $S$-structures can be made into a preorder by setting
$\alpha \le \beta$ iff. the identity morphism is an $H$-homomorphism
from $\alpha$ to $\beta$. And, if this preorder is in fact a partial
order, then the total category of structures is univalent --- the type
of identities between $S$-structured $\ca{B}$-objects is equivalent to
the type of $H$-homomorphic $\ca{B}$-isomorphisms.

```agda
  displayed-SIP
    : is-category B
    → (∀ {x} (α β : S x) → ∣ H (B .id) α β ∣ → ∣ H (B .id) β α ∣ → α ≡ β)
    → is-category (∫ structures)
  displayed-SIP Bcat H-antisym =
    is-category-total structures Bcat $ is-category-fibrewise _ Bcat λ A x y →
      Σ-prop-path
        (λ _ _ _ → ≅[]-path _ (H _ _ _ .is-tr _ _) (H _ _ _ .is-tr _ _))
        (H-antisym _ _
          (subst (λ e → ∣ H e (x .fst) (y .fst) ∣) (B .idl (B .id))
            (H-∘ _ _ (y .snd .to′) (x .snd .from′)))
          (subst (λ e → ∣ H e (y .fst) (x .fst) ∣) (B .idl (B .id))
            (H-∘ _ _ (x .snd .to′) (y .snd .from′))))
```
