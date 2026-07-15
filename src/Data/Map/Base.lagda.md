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
    leaf : Valid i → Tree i
    node
      : (p : Ob) (l : Tree 〚 i .l , p 〛) (r : Tree 〚 p , i .r 〛) (n : Nat)
      → (n ≡ 1 + size l + size r) → Tree i

  size (leaf _) = 0
  size (node _ _ _ n _) = n

  insert : Tree i → Elt i → Tree i
  size-insert : (t : Tree i) → (e : Elt i) → 1 + size t ≡ size (insert t e)

  insert (leaf _) (elt p lp pr) = node p (leaf lp) (leaf pr) 1 refl
  insert (node q l r n pf) (elt p lp pr) with compare p q
  ... | inl pq =
    let e' = elt p lp pq in
    let l' = insert l e' in
    let pf' = ap suc $
              n                       ≡⟨ pf ⟩
              ⌜ 1 + size l ⌝ + size r ≡⟨ ap! (size-insert l e') ⟩
              size l' + size r        ∎ in
      node q l' r (1 + n) pf'
  ... | inr qp =
    let e' = elt p qp pr in
    let r' = insert r e' in
    let pf' = ap suc $
              n                       ≡⟨ pf ⟩
              1 + (size l + size r)   ≡⟨ nat! ⟩
              size l + (1 + size r)   ≡⟨ refl ⟩
              size l + ⌜ 1 + size r ⌝ ≡⟨ ap! (size-insert r e') ⟩
              size l + size r'        ∎ in
    node q l r' (1 + n) pf'

  size-insert (leaf x) e = refl
  size-insert (node q _ _ _ _) (elt p _ _) with compare p q
  ... | inl pq = refl
  ... | inr qp = refl

  single-left
    : (p : Ob) (l : Tree 〚 i .l , p 〛) (r : Tree 〚 p , i .r 〛) (n : Nat)
    → (n ≡ 1 + size l + size r) → Tree i
  single-left a x yz@(node b y z n n-pf) m m-pf =
    let xy = (node a x y (1 + size x + size y) refl) in
    let m-pf' = m                                      ≡⟨ m-pf ⟩
                1 + (size x + ⌜ size yz ⌝)             ≡⟨ ap! n-pf ⟩
                1 + (size x + (1 + size y + size z))   ≡⟨ nat! ⟩
                1 + ((1 + size x + size y) + size z)   ≡⟨ refl ⟩
                1 + size xy + size z                   ∎ in
    node b xy z m m-pf'
  single-left a x yz@(leaf v) m m-pf = node a x yz m m-pf

  single-right
    : (p : Ob) (l : Tree 〚 i .l , p 〛) (r : Tree 〚 p , i .r 〛) (n : Nat)
    → (n ≡ 1 + size l + size r) → Tree i
  single-right a xy@(node b x y n n-pf) z m m-pf =
    let yz = (node a y z (1 + size y + size z) refl) in
    let m-pf' = m                                  ≡⟨ m-pf ⟩
                1 + ⌜ size xy ⌝ + size z           ≡⟨ ap! n-pf ⟩
                1 + (1 + size x + size y) + size z ≡⟨ nat! ⟩
                1 + size x + (1 + size y + size z) ≡⟨ refl ⟩
                1 + size x + size yz               ∎ in
    node b x yz m m-pf'
  single-right a xy@(leaf v) z m m-pf = node a xy z m m-pf

  ratio : Nat
  ratio = 5

  balance
    : (p : Ob) (l : Tree 〚 i .l , p 〛) (r : Tree 〚 p , i .r 〛) (n : Nat)
    → (n ≡ 1 + size l + size r) → Tree i
  balance a x y n n-pf =
    let xn = size x in
    let yn = size y in
    if (xn + yn NP.< 2) then node a x y n n-pf
    else if (yn NP.> (ratio * xn)) then
      -- right is too big
      -- we now have to do either a single or double left rotation
      {!!}
    else if (xn NP.> (ratio * yn)) then
      -- left is too big
      -- we now have to do either a single or double right rotation
      {!!}
    else node a x y n n-pf
```
