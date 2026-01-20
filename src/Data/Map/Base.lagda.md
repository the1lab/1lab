```agda
module Data.Map.Base where

open import 1Lab.Prelude
open import Data.Nat.Solver
open import Data.Sum
open import Data.Bool
open import Order.Base
open import Order.Total
import Prim.Data.Nat as NP
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

  single-left : (p : Ob) (l : Tree 〚 i .l , p 〛) (r : Tree 〚 p , i .r 〛) (n : Nat)
      → (n ≡ 1 + size l + size r) → Tree i
  single-left a x yz@(Node b y z n n-pf) m m-pf =
    let xy = (Node a x y (1 + size x + size y) refl) in
    let m-pf' = m ≡⟨ m-pf ⟩ suc (size x + size yz)
                  ≡⟨ ap (λ k -> suc (size x + k)) n-pf ⟩ suc (size x + (suc (size y + size z)))
                  ≡⟨ nat! ⟩ suc ((suc (size x + size y)) + size z)
                  ≡⟨ refl ⟩ 1 + size xy + size z ∎ in
    Node b xy z m m-pf'
  single-left a x yz@(Leaf v) m m-pf = Node a x yz m m-pf

  single-right : (p : Ob) (l : Tree 〚 i .l , p 〛) (r : Tree 〚 p , i .r 〛) (n : Nat)
      → (n ≡ 1 + size l + size r) → Tree i
  single-right a xy@(Node b x y n n-pf) z m m-pf =
    let yz = (Node a y z (1 + size y + size z) refl) in
    let m-pf' = m ≡⟨ m-pf ⟩ suc (size xy + size z)
                  ≡⟨ ap (λ k -> suc (k + size z)) n-pf ⟩ suc (suc (size x + size y) + size z)
                  ≡⟨ nat! ⟩ suc (size x + suc (size y + size z))
                  ≡⟨ refl ⟩ 1 + size x + size yz ∎ in
    Node b x yz m m-pf'
  single-right a xy@(Leaf v) z m m-pf = Node a xy z m m-pf

  ratio : Nat
  ratio = 5

  balance : (p : Ob) (l : Tree 〚 i .l , p 〛) (r : Tree 〚 p , i .r 〛) (n : Nat)
      → (n ≡ 1 + size l + size r) → Tree i
  balance a x y n n-pf =
    let xn = size x in
    let yn = size y in
    if (xn + yn NP.< 2) then Node a x y n n-pf
    else if (yn NP.> (ratio * xn)) then
      -- right is too big
      -- we now have to do either a single or double left rotation
      {!!}
    else if (xn NP.> (ratio * yn)) then
      -- left is too big
      -- we now have to do either a single or double right rotation
      {!!}
    else Node a x y n n-pf
```
