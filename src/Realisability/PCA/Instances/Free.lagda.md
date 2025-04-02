<!--
```agda
open import 1Lab.Prelude

open import Data.Set.Coequaliser
open import Data.Partial.Total
open import Data.Partial.Base

open import Realisability.PCA.Combinatorial
open import Realisability.PCA
```
-->

```agda
module Realisability.PCA.Instances.Free where
```

# The free total combinatory algebra

```agda
infixl 25 _`·_

data SK : Type where
  S K  : SK
  _`·_ : SK → SK → SK

data _≻_ : SK → SK → Type where
  K-β  : ∀ a b   → K `· a `· b ≻ a
  S-β  : ∀ f g x → S `· f `· g `· x ≻ f `· x `· (g `· x)
  _`·_ : ∀ {f f' x x'} → f ≻ f' → x ≻ x' → f `· x ≻ f' `· x'
  stop : ∀ {f} → f ≻ f

data _≻*_ : SK → SK → Type where
  step : ∀ {f f' f''} → f ≻ f' → f' ≻* f'' → f ≻* f''
  stop : ∀ {f}        → f ≻* f

_∼_ : SK → SK → Type
x ∼ y = ∃[ W ∈ SK ] (x ≻* W × y ≻* W)

open Congruence hiding (_∼_)

inv-≻-k : ∀ {u v} → K `· u ≻ v → Σ[ v' ∈ SK ] (K `· v' ≡ᵢ v × u ≻ v')
inv-≻-k (stop `· a) = _ , reflᵢ , a
inv-≻-k stop = _ , reflᵢ , stop

inv-≻-s : ∀ {f g u} → S `· f `· g ≻ u → Σ[ f' ∈ SK ] Σ[ g' ∈ SK ] (S `· f' `· g' ≡ᵢ u × f ≻ f' × g ≻ g')
inv-≻-s (stop `· a `· b) = _ , _ , reflᵢ , a , b
inv-≻-s (stop `· a) = _ , _ , reflᵢ , stop , a
inv-≻-s stop = _ , _ , reflᵢ , stop , stop

diamond : ∀ {u v v'} → u ≻ v → u ≻ v' → Σ[ W ∈ SK ] (v ≻ W × v' ≻ W)
diamond (K-β v b) (K-β v .b) = v , stop , stop
diamond (K-β v b) a@(α `· β) with inv-≻-k α
... | W , reflᵢ , x = W , x , K-β W _
diamond (K-β v b) stop = v , stop , K-β v b

diamond (S-β f g x) (S-β .f .g .x) = _ , stop , stop
diamond (S-β f g x) (α `· β) with inv-≻-s α
... | f' , g' , reflᵢ , p , q = _ , p `· β `· (q `· β) , S-β f' g' _
diamond (S-β f g x) stop = _ , stop , S-β f g x

diamond (α `· β) (K-β v' _) with inv-≻-k α
... | W , reflᵢ , x = W , K-β W _ , x
diamond (α `· β) (S-β f g _) with inv-≻-s α
... | f' , g' , reflᵢ , p , q = _ , S-β f' g' _ , p `· β `· (q `· β)
diamond (α `· β) (γ `· δ) with diamond α γ | diamond β δ
... | W , a1 , a2 | Z , b1 , b2 = (W `· Z) , (a1 `· b1) , (a2 `· b2)
diamond (α `· β) stop = _ , stop , α `· β

diamond stop q = _ , q , stop

strip : ∀ {x y z} → x ≻ y → x ≻* z → Σ[ W ∈ SK ] (y ≻* W × z ≻ W)
strip p (step a q) with diamond p a
... | W , y→w , f→w with strip f→w q
... | Z , α , β = Z , step y→w α , β
strip p stop = _ , stop , p

confl : ∀ {x y z} → x ≻* y → x ≻* z → Σ[ W ∈ SK ] (y ≻* W × z ≻* W)
confl (step α αs) β with strip α β
... | N , f→n , z→n with confl αs f→n
... | W , p , q = W , p , step z→n q
confl stop β = _ , β , stop

≻*-trans : ∀  {x y z} → x ≻* y → y ≻* z → x ≻* z
≻*-trans (step x p) q = step x (≻*-trans p q)
≻*-trans stop q = q

conv : Congruence SK _
conv .Congruence._∼_ = _∼_
conv .has-is-prop x y = hlevel 1
conv .reflᶜ = inc (_ , stop , stop)
conv ._∙ᶜ_ = rec! λ U x→u y→u V y→v z→v →
  let (W , u→w , v→w) = confl y→u y→v
   in inc (W , ≻*-trans x→u u→w , ≻*-trans z→v v→w)
conv .symᶜ = rec! (λ W p q → inc (W , q , p))

≻*-resp-`· : ∀ {u u' v v'} → u ≻* u' → v ≻* v' → u `· v ≻* u' `· v'
≻*-resp-`· (step x p) (step y q) = step (x `· y) (≻*-resp-`· p q)
≻*-resp-`· (step x p) stop = step (x `· stop) (≻*-resp-`· p stop)
≻*-resp-`· stop (step x q) = step (stop `· x) (≻*-resp-`· stop q)
≻*-resp-`· stop stop = stop

sk-not-equal : ∀ x → K ≻* x → S ≻* x → ⊥
sk-not-equal x (step stop p) q = sk-not-equal x p q
sk-not-equal x stop (step stop q) = sk-not-equal _ stop q

module conv = Congruence conv

appl : conv.quotient → conv.quotient → conv.quotient
appl = conv.op₂ _`·_ resp where abstract
  resp : ∀ u v u' v' → u ∼ u' → v ∼ v' → u `· v ∼ u' `· v'
  resp u v u' v' = rec! λ W u→w u'→w X v→x v'→x → inc (_ , ≻*-resp-`· u→w v→x , ≻*-resp-`· u'→w v'→x)

SK-is-pca : is-pca {A = conv.quotient} λ f x → ⦇ appl f x ⦈
SK-is-pca = has-ski→is-pca record
  { K   = always (inc K)
  ; S   = always (inc S)
  ; K↓  = tt
  ; S↓  = tt
  ; K↓₁ = λ {x} z → (tt , tt) , z
  ; K-β = λ {x} {y} xh yh → part-ext (λ z → xh) (λ z → (tt , (tt , tt) , xh) , yh) λ _ _ → kb (x .elt _) (y .elt _) ∙ ↯-indep x
  ; S↓₁ = λ {f} z → (tt , tt) , z
  ; S↓₂ = λ {f} {g} z z₁ → (tt , (tt , tt) , z) , z₁
  ; S-β = λ {f} {g} {x} hf hg hx → part-ext (λ z → (tt , (tt , hf) , hx) , (tt , hg) , hx) (λ z → (tt , (tt , (tt , tt) , hf) , hg) , hx)
    λ _ _ → sb (f .elt _) (g .elt _) (x .elt _) ∙ ap₂ appl (ap₂ appl (↯-indep f) (↯-indep x)) (ap₂ appl (↯-indep g) (↯-indep x))
  }
  where
    kb : ∀ x y → appl (appl (inc K) x) y ≡ x
    kb = elim! λ f g → quot (inc (f , step (K-β f g) stop , stop))

    sb : ∀ f g x → appl (appl (appl (inc S) f) g) x ≡ appl (appl f x) (appl g x)
    sb = elim! λ f g x → quot (inc (_ , step (S-β f g x) stop , stop))

SK-nontriv : ¬ Path conv.quotient (inc K) (inc S)
SK-nontriv w = case conv.effective w of sk-not-equal
```
