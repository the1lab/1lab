<!--
```agda
open import 1Lab.Path
open import 1Lab.Type

open import Data.List.Base
open import Data.Dec.Base
open import Data.Sum.Base
```
-->

```agda
module Data.List.Membership where
```

## Pointwise Predicates

```agda
data Some {ℓ ℓ'} {A : Type ℓ} (P : A → Type ℓ') : List A → Type (ℓ ⊔ ℓ') where
  here : ∀ {x xs} → P x → Some P (x ∷ xs)
  there : ∀ {x xs} → Some P xs → Some P (x ∷ xs)

data All {ℓ ℓ'} {A : Type ℓ} (P : A → Type ℓ') : List A → Type (ℓ ⊔ ℓ') where
  nowhere : All P []
  everywhere : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)
```

<!--
```agda
private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    P Q : A → Type ℓ'
    x y : A
    xs ys : List A
```
-->

```agda
Some-elim
  : ∀ {P : A → Type ℓ} (R : (xs : List A) → Some P xs → Type ℓ')
  → (∀ {x} {xs} → (p : P x) → R (x ∷ xs) (here p))
  → (∀ {x} {xs} → (p : Some P xs) → R xs p → R (x ∷ xs) (there p))
  → ∀ {xs : List A} (s : Some P xs) → R xs s
Some-elim R h t (here p) = h p
Some-elim R h t (there p) = t p (Some-elim R h t p)

Some-rec
  : ∀ {P : A → Type ℓ} {X : Type ℓ'}
  → (∀ {x} → P x → X)
  → (X → X)
  → ∀ {xs : List A} → Some P xs → X
Some-rec h t (here p) = h p
Some-rec h t (there p) = t (Some-rec h t p)

All-elim
  : ∀ {P : A → Type ℓ} (R : (xs : List A) → All P xs → Type ℓ')
  → R [] nowhere
  → (∀ {x} {xs} → (px : P x) → (pxs : All P xs) → R xs pxs → R (x ∷ xs) (everywhere px pxs))
  → ∀ {xs : List A} (a : All P xs) → R xs a
All-elim R n e nowhere = n
All-elim R n e (everywhere x a) = e x a (All-elim R n e a)

All-rec
  : ∀ {P : A → Type ℓ} {X : Type ℓ'}
  → X
  → (∀ {x} → P x → X → X)
  → ∀ {xs : List A} → All P xs → X
All-rec n e nowhere = n
All-rec n e (everywhere p a) = e p (e p n)
```

```agda
∷-all-head : All P (x ∷ xs) → P x
∷-all-head (everywhere px _) = px

∷-all-tail : All P (x ∷ xs) → All P xs
∷-all-tail (everywhere _ pxs) = pxs

∷-all-× : All P (x ∷ xs) → P x × All P xs
∷-all-× (everywhere px pxs) = px , pxs

¬some-[] : ¬ (Some P [])
¬some-[] ()

∷-some-⊎ : Some P (x ∷ xs) → P x ⊎ Some P xs
∷-some-⊎ (here px) = inl px
∷-some-⊎ (there pxs) = inr pxs

∷-¬some-head : ¬ (Some P (x ∷ xs)) → ¬ (P x)
∷-¬some-head ¬some px = ¬some (here px)

∷-¬some-tail : ¬ (Some P (x ∷ xs)) → ¬ (Some P xs)
∷-¬some-tail ¬some px = ¬some (there px)
```

```agda
some-map : (∀ {x} → P x → Q x) → Some P xs → Some Q xs
some-map f (here px) = here (f px)
some-map f (there pxs) = there (some-map f pxs)

all-map : (∀ {x} → P x → Q x) → All P xs → All Q xs
all-map f nowhere = nowhere
all-map f (everywhere px pxs) = everywhere (f px) (all-map f pxs)

not-some→all-not
  : ¬ (Some P xs)
  → All (λ x → ¬ (P x)) xs
not-some→all-not {xs = []} ¬some = nowhere
not-some→all-not {xs = x ∷ xs} ¬some =
  everywhere (∷-¬some-head ¬some) (not-some→all-not (∷-¬some-tail ¬some))
```



```agda
some?
  : ∀ {P : A → Type ℓ}
  → (∀ x → Dec (P x))
  → (xs : List A) → Dec (Some P xs)
some? P? [] = no ¬some-[]
some? P? (x ∷ xs) with P? x
... | yes px = yes (here px)
... | no ¬px with some? P? xs
... | yes pxs = yes (there pxs)
... | no ¬pxs = no ([ ¬px , ¬pxs ] ∘ ∷-some-⊎)

all?
  : ∀ {P : A → Type ℓ}
  → (∀ x → Dec (P x))
  → (xs : List A) → Dec (All P xs)
all? P? [] = yes nowhere
all? P? (x ∷ xs) with P? x | all? P? xs
... | yes p | yes ps = yes (everywhere p ps)
... | yes p | no ¬ps = no (¬ps ∘ ∷-all-tail)
... | no ¬p | q = no (¬p ∘ ∷-all-head)
```

<!--
```agda
instance
  Dec-Some : ∀ {P : A → Type ℓ} → ⦃ ∀ {x} → Dec (P x) ⦄ → {xs : List A} → Dec (Some P xs)
  Dec-Some {P = P} = some? (λ x → holds? (P x)) _

  Dec-All : ∀ {P : A → Type ℓ} → ⦃ ∀ {x} → Dec (P x) ⦄ → {xs : List A} → Dec (All P xs)
  Dec-All {P = P} = all? (λ x → holds? (P x)) _
```
-->


## Membership in Lists

```agda
_∈ₗ_ : ∀ {ℓ} {A : Type ℓ} → A → List A → Type ℓ
_∈ₗ_ x xs = Some (x ≡_) xs
```

```agda
all-∈ : All P xs → x ∈ₗ xs → P x
all-∈ {P = P} (everywhere px pxs) (here p) =
  subst P (sym p) px
all-∈ (everywhere px pxs) (there x∈xs) =
  all-∈ pxs x∈xs
```


```agda
elem? : ⦃ _ : Discrete A ⦄ (x : A) (xs : List A) → Dec (x ∈ₗ xs)
elem? x xs = some? (x ≡?_) xs
```
