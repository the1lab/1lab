<!--
```agda
open import Algebra.Ring.Module
open import Algebra.Group.NAry
open import Algebra.Group.Ab
open import Algebra.Group
open import Algebra.Ring

open import Cat.Displayed.Univalence.Thin
open import Cat.Diagram.Product.Indexed
open import Cat.Prelude

open import Data.Fin.Base
```
-->

```agda
module Algebra.Ring.Module.Vec {ℓ} (R : Ring ℓ) where
```

<!--
```agda
private module R = Ring-on (R .snd)
open make-abelian-group
open Module-on
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
Fin-vec-module : ∀ n → Module R ℓ
Fin-vec-module n = to-module mk where
  mk : make-module R (Fin n → ⌞ R ⌟)
  mk .make-module.has-is-set = hlevel 2
  mk .make-module._+_ f g i = f i R.+ g i
  mk .make-module.inv f i = R.- f i
  mk .make-module.0g i = R.0r
  mk .make-module._⋆_ f g i = f R.* g i

  mk .make-module.+-assoc f g h    = funext λ i → R.+-associative
  mk .make-module.+-invl f         = funext λ i → R.+-invl
  mk .make-module.+-idl f          = funext λ i → R.+-idl
  mk .make-module.+-comm f g       = funext λ i → R.+-commutes
  mk .make-module.⋆-distribl r x y = funext λ i → R.*-distribl
  mk .make-module.⋆-distribr r x y = funext λ i → R.*-distribr
  mk .make-module.⋆-assoc r s x    = funext λ i → R.*-associative
  mk .make-module.⋆-id x           = funext λ i → R.*-idl
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
module _ {ℓ'} (S : Module R ℓ') where
  private
    module S = Module-on (S .snd)
    G' = Module-on→Group-on (S .snd)

  ∑-distr : ∀ {n} r (f : Fin n → ⌞ S ⌟)
          → r S.⋆ ∑ G' f
          ≡ ∑ G' λ i → r S.⋆ f i
  ∑-distr {n = zero} r f = S.⋆-idr
  ∑-distr {n = suc n} r f =
    r S.⋆ (f fzero S.+ ∑ G' (λ e → f (fsuc e)))            ≡⟨ S.⋆-distribl r (f fzero) _ ⟩
    (r S.⋆ f fzero) S.+ ⌜ r S.⋆ ∑ G' (λ e → f (fsuc e)) ⌝  ≡⟨ ap! (∑-distr {n} r (λ e → f (fsuc e))) ⟩
    (r S.⋆ f fzero) S.+ ∑ G' (λ i → r S.⋆ f (fsuc i))      ∎
```
-->

```agda
  linear-extension : ∀ {n} → (Fin n → ⌞ S ⌟)
                   → Linear-map (Fin-vec-module n) S
  linear-extension fun .map x = ∑ G' λ i → x i S.⋆ fun i
  linear-extension fun .lin .linear r m n =
    ∑ G' (λ i → (r R.* m i R.+ n i) S.⋆ fun i)                            ≡⟨ ap (∑ G')  (funext λ i → S.⋆-distribr (r R.* m i) (n i) (fun i)) ⟩
    ∑ G' (λ i → (r R.* m i) S.⋆ fun i S.+ n i S.⋆ fun i)                  ≡⟨ ∑-split (Module-on→Abelian-group-on (S .snd)) (λ i → (r R.* m i) S.⋆ fun i) _ ⟩
    ⌜ ∑ G' (λ i → (r R.* m i) S.⋆ fun i) ⌝ S.+ ∑ G' (λ i → n i S.⋆ fun i) ≡⟨ ap! (ap (∑ G') (funext λ i → sym (S.⋆-assoc r (m i) _))) ⟩
    ⌜ ∑ G' (λ i → r S.⋆ m i S.⋆ fun i) ⌝ S.+ ∑ G' (λ i → n i S.⋆ fun i)   ≡˘⟨ ap¡ (∑-distr r λ i → m i S.⋆ fun i) ⟩
    (r S.⋆ ∑ G' (λ i → m i S.⋆ fun i) S.+ ∑ G' λ i → n i S.⋆ fun i)       ∎
```

## As products

To reduce how arbitrary the construction above seems, we show that the
module of finite vectors is equivalently the finite product of $R$ with
itself, $n$ times (indirectly justifying the notation $R^n$ while we're
at it). Note that this is a product _in the category $R$-Mod_, not in
the category of rings.

```agda
open is-indexed-product
open Indexed-product

Fin-vec-is-product
  : ∀ {n} → Indexed-product (R-Mod R _) {Idx = Fin n} λ _ → representable-module R
Fin-vec-is-product {n} .ΠF = Fin-vec-module n
Fin-vec-is-product .π i .hom k = k i
Fin-vec-is-product .π i .preserves .linear r m n = refl
Fin-vec-is-product {n} .has-is-ip .tuple {Y} f = assemble where
  assemble : R-Mod.Hom Y (Fin-vec-module n)
  assemble .hom yob ix = f ix # yob
  assemble .preserves .linear r m n = funext λ i → f i .preserves .linear _ _ _
Fin-vec-is-product .has-is-ip .commute = trivial!
Fin-vec-is-product .has-is-ip .unique {h = h} f ps =
  ext λ i ix → ap hom (ps ix) $ₚ i
```
