```agda
module Data.Map.Base where

open import 1Lab.Prelude
open import Data.Nat.Solver
open import Data.Sum
open import Order.Base
open import Order.Total
```

```agda
module SortedTrees (P : Poset lzero lzero) (idto : is-decidable-total-order P) where

  open is-decidable-total-order idto

  record II : Type where
    constructor 〚_,_〛
    field
      l : Ob
      r : Ob

  open II

  record Elt (i : II) : Type where
    constructor elt
    field
      p : Ob
      lp : i .l ≤ p
      pr : p ≤ i .r

  Valid : II -> Type
  Valid i = i .l ≤ i .r

  variable i : II

  interleaved mutual
    data Tree : II -> Type
    size : Tree i -> Nat

    data _ where
      Leaf : Valid i -> Tree i
      Node : (p : Ob) -> (l : Tree 〚 i .l , p 〛) -> (r : Tree 〚 p , i .r 〛) -> (n : Nat) -> (n ≡ 1 + size l + size r) -> Tree i

    size (Leaf _) = 0
    size (Node _ _ _ n _) = n

  interleaved mutual
    insert : Tree i -> Elt i -> Tree i
    insertSize : (t : Tree i) -> (e : Elt i) -> 1 + size t ≡ size (insert t e)

    insert (Leaf _) (elt p lp pr) = Node p (Leaf lp) (Leaf pr) 1 refl
    insert (Node q l r n pf) (elt p lp pr) with compare p q
    ... | inl pq =
      let e' = elt p lp pq in
      let l' = insert l e' in
      let pf' = 1 + n ≡⟨ ap suc pf ⟩ 1 + (1 + size l + size r)
                      ≡⟨ ap ((λ k -> 1 + k + size r)) (insertSize l e') ⟩ 1 + (size l' + size r) ∎ in
        Node q l' r (1 + n) pf'
    ... | inr qp =
      let e' = elt p qp pr in
      let r' = insert r e' in
      let pf' = 1 + n ≡⟨ ap suc pf ⟩ suc (suc (size l + size r))
                      ≡⟨ nat! ⟩ suc (size l + (suc (size r)))
                      ≡⟨ ap ((λ k -> 1 + size l + k)) (insertSize r e') ⟩ suc (size l + size r') ∎ in
      Node q l r' (1 + n) pf'

    insertSize (Leaf x) e = refl
    insertSize (Node q _ _ _ _) (elt p _ _) with compare p q
    ... | inl pq = refl
    ... | inr qp = refl
```
