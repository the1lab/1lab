```agda
open import Algebra.Ring.Module
open import Algebra.Group.NAry
open import Algebra.Group.Ab
open import Algebra.Group
open import Algebra.Ring

open import Cat.Displayed.Univalence.Thin
open import Cat.Functor.FullSubcategory
open import Cat.Prelude

open import Data.Fin

module Algebra.Ring.Module.Vec {ℓ} (R : Ring ℓ) where
```

<!--
```agda
private module R = Ring-on (R .snd)
open make-group
open Module hiding (module R ; module G ; G₀)
```
-->

# The module of finite vectors

Fix a ring $R$ and choose $n$ to be your favourite natural number --- or
a natural number you totally despise, that's fine, too. A basic fact
from high school linear algebra is that, for $n$ a natural number,
"lists of $n$ reals" are a _vector space_ over the field of real numbers
$\RR$. Here we prove a generalisation of that fact: lists of $n$
elements of $R$ are a module over $R$.

```agda
Fin-vec-module : ∀ n → Module R
Fin-vec-module n .G = to-abelian-group mg λ x y → funext λ _ → R.+-commutes
  where
    mg : make-group (Fin n → R .fst)
    mg .group-is-set = hlevel!
    mg .unit _ = R.0r
    mg .mul f g i = f i R.+ g i
    mg .inv f i = R.- (f i)
    mg .assoc x y z = funext λ _ → sym R.+-associative
    mg .invl x = funext λ _ → R.+-invl
    mg .invr x = funext λ _ → R.+-invr
    mg .idl x = funext λ _ → R.+-idl
Fin-vec-module n ._⋆_ r f i = r R.* f i
Fin-vec-module n .⋆-id x = funext λ i → R.*-idl
Fin-vec-module n .⋆-add-r r x y = funext λ i → R.*-distribl
Fin-vec-module n .⋆-add-l r s x = funext λ i → R.*-distribr
Fin-vec-module n .⋆-assoc r s x = funext λ i → R.*-associative
```

Furthermore, the module of $n$-ary vectors has the following nice
property: If $v = (s_0, ... s_n)$ is an $n$-ary vector with entries $s_i
: S$ for some other $R$-module $S$, there is a unique linear map $R^n
\to S$ which agrees with our original $v$.  This map is given by
**linear extension**: The vector $v$ gives rise to the map which sends
$f$ to

$$
\sum_{i < n} f_iv_i\text{.}
$$

<!--
```agda
module _ (S : Module R) where
  private
    module S = Module S
    G′ = S.G .object .snd

  ∑-distr : ∀ {n} r (f : Fin n → S.G₀)
          → r S.⋆ ∑ G′ f
          ≡ ∑ G′ λ i → r S.⋆ f i
  ∑-distr {n = zero} r f = S.⋆-group-hom.pres-id _
  ∑-distr {n = suc n} r f =
    r S.⋆ (f fzero S.+ ∑ G′ (λ e → f (fsuc e)))            ≡⟨ S.⋆-add-r r (f fzero) _ ⟩
    (r S.⋆ f fzero) S.+ ⌜ r S.⋆ ∑ G′ (λ e → f (fsuc e)) ⌝  ≡⟨ ap! (∑-distr {n} r (λ e → f (fsuc e))) ⟩
    (r S.⋆ f fzero) S.+ ∑ G′ (λ i → r S.⋆ f (fsuc i))      ∎
```
-->

```agda
  linear-extension : ∀ {n} → (Fin n → S.G₀) → R-Mod.Hom (Fin-vec-module n) S
  linear-extension fun .map x = ∑ G′ λ i → x i S.⋆ fun i
  linear-extension fun .linear r m s n =
    ∑ G′ (λ i → (r R.* m i R.+ s R.* n i) S.⋆ fun i)                          ≡⟨ ap (∑ G′) (funext λ i → S.⋆-add-l (r R.* m i) (s R.* n i) (fun i)) ⟩
    ∑ G′ (λ i → ((r R.* m i) S.⋆ fun i) S.+ ((s R.* n i) S.⋆ fun i))          ≡⟨ ∑-split G′ (S.G .witness) (λ i → (r R.* m i) S.⋆ fun i) (λ i → (s R.* n i) S.⋆ fun i) ⟩
    (∑ G′ λ i → (r R.* m i) S.⋆ fun i) S.+ (∑ G′ λ i → (s R.* n i) S.⋆ fun i) ≡˘⟨ ap₂ S._+_ (ap (∑ G′) (funext λ i → S.⋆-assoc r (m i) (fun i))) (ap (∑ G′) (funext λ i → S.⋆-assoc s (n i) (fun i))) ⟩
    (∑ G′ λ i → r S.⋆ (m i S.⋆ fun i)) S.+ (∑ G′ λ i → s S.⋆ (n i S.⋆ fun i)) ≡˘⟨ ap₂ S._+_ (∑-distr r λ i → m i S.⋆ fun i) (∑-distr s λ i → n i S.⋆ fun i) ⟩
    (r S.⋆ ∑ G′ (λ i → m i S.⋆ fun i)) S.+ (s S.⋆ ∑ G′ (λ i → n i S.⋆ fun i)) ∎
```
