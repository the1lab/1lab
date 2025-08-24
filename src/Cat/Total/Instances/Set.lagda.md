<!--
```agda
open import Cat.Instances.Sets.Complete
open import Cat.Diagram.Terminal
open import Cat.Functor.Adjoint
open import  Cat.Functor.Closed
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Prelude
open import Cat.Total
```
-->

```agda
module Cat.Total.Instances.Set {ℓ} where
```
<!--
```agda
open Terminal (Sets-terminal {ℓ}) renaming (top to ★)
open _⊣_
open _=>_
open Functor
private
```
-->

# Total cocompletion of sets

If we are to show that the category of sets is total, we must give a
colimit over the category of elements of every presheaf.

Suppose $P\in \psh(\Sets)$. What would a colimit $c$ of
$\pi_p : \int P \to C$ look like? Let $(U, x)\in \int P$. We require a
universal function $U\to c$. Notice that any element of a set $x\in U$
is equivalent to a subobject $\tilde{x}:\ast\to U$ sending the single
element to $x$. Furthermore, $P$ sends this to a function $P(U)\to
P(\ast)$. Thus, setting $C=P(\ast)$ we have a function
$f(y)=P(\tilde{y})(x)$ from $U$ to $P(\ast)$ as desired.

Now, let $m:(U,x)\to(R,y)$ in the category of elements. Our cocone
commutes as, for any $s\in U$, $P(\tilde{m(s)})(y)=(P(m)\circ
P(\tilde{s}))(y)=P(\tilde{s})(x)$ as $P(m):y\mapsto x$.

```agda
  さ : Functor (PSh ℓ (Sets ℓ)) (Sets ℓ)
  さ = eval-at ★

  has-よ-adj : さ ⊣ よ (Sets ℓ)
  has-よ-adj .unit .η P .η X p s = P ⟪ (λ _ → s) ⟫ p
  has-よ-adj .unit .η P .is-natural x y f = ext λ r s → sym $ unext (P .F-∘ _ _) _
  has-よ-adj .unit .is-natural F G nt  = ext λ X s r →
    G ⟪ (λ _ → r) ⟫ (nt .η X s)                   ≡˘⟨ unext (nt .is-natural  _ _ _) _ ⟩
    (nt .η ★ (F ⟪ (λ _ → r) ⟫ s))                 ≡˘⟨ unext (G .F-id) _ ⟩
    G ⟪ (λ x → x) ⟫ (nt .η ★ (F ⟪ (λ _ → r) ⟫ s)) ∎
  has-よ-adj .counit .η X s = s _
  has-よ-adj .counit .is-natural _ _ _ = refl
  has-よ-adj .zig {F} = F .F-id
  has-よ-adj .zag  = trivial!

Sets-total : is-total (Sets ℓ)
Sets-total .is-total.さ = さ
Sets-total .is-total.has-よ-adj = has-よ-adj
```
