```agda
module Data.Map.Base where

open import 1Lab.Prelude
open import Data.Nat.Solver
open import Data.Sum
open import Order.Base
open import Order.Total
```

```agda
module Sorted-trees {o ℓ} {P : Poset o ℓ} (idto : is-decidable-total-order P) where

  open is-decidable-total-order idto

  record II : Type o where
    constructor 〚_,_〛
    field
      l : Ob
      r : Ob

  open II

  record Elt (i : II) : Type (o ⊔ ℓ) where
    constructor elt
    field
      p : Ob
      lp : i .l ≤ p
      pr : p ≤ i .r

  Valid : II → Type ℓ
  Valid i = i .l ≤ i .r

  private variable i : II

  data Tree : II → Type (o ⊔ ℓ)
  size : Tree i → Nat

  data Tree where
    Leaf : Valid i → Tree i
    Node : (p : Ob) (l : Tree 〚 i .l , p 〛) (r : Tree 〚 p , i .r 〛) (n : Nat)
      → (n ≡ 1 + size l + size r) → Tree i

  size (Leaf _) = 0
  size (Node _ _ _ n _) = n

  insert : Tree i → Elt i → Tree i
  size-insert : (t : Tree i) → (e : Elt i) → 1 + size t ≡ size (insert t e)

  insert (Leaf _) (elt p lp pr) = Node p (Leaf lp) (Leaf pr) 1 refl
  insert (Node q l r n pf) (elt p lp pr) with compare p q
  ... | inl pq =
    let e' = elt p lp pq in
    let l' = insert l e' in
    let pf' = 1 + n ≡⟨ ap suc pf ⟩ 1 + (1 + size l + size r)
                    ≡⟨ ap ((λ k → 1 + k + size r)) (size-insert l e') ⟩
                    1 + (size l' + size r) ∎ in
      Node q l' r (1 + n) pf'
  ... | inr qp =
    let e' = elt p qp pr in
    let r' = insert r e' in
    let pf' = 1 + n ≡⟨ ap suc pf ⟩ suc (suc (size l + size r))
                    ≡⟨ nat! ⟩ suc (size l + (suc (size r)))
                    ≡⟨ ap ((λ k → 1 + size l + k)) (size-insert r e') ⟩
                    suc (size l + size r') ∎ in
    Node q l r' (1 + n) pf'

  size-insert (Leaf x) e = refl
  size-insert (Node q _ _ _ _) (elt p _ _) with compare p q
  ... | inl pq = refl
  ... | inr qp = refl
```
