---
description: |
  We establish a correspondence between "fibrewise equivalences" and
  equivalences of total spaces (Σ-types), and define equivalences over.
---
<!--
```agda
open import 1Lab.Equiv.FromPath
open import 1Lab.HLevel.Closure
open import 1Lab.Path.Reasoning
open import 1Lab.Path.Groupoid
open import 1Lab.Type.Sigma
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.Equiv.Fibrewise where
```

# Fibrewise equivalences

:::{.definition #fibrewise-map}
In HoTT, a type family `P : A → Type` can be seen as a [_fibration_]
with total space `Σ P`, with the fibration being the projection
`fst`{.Agda}. Because of this, a function with type `(x : _) → P x → Q
x` can be referred as a **fibrewise map**.
:::

[_fibration_]: https://ncatlab.org/nlab/show/fibration

A function like this can be lifted to a function on total spaces:

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A B : Type ℓ
  P Q : A → Type ℓ
```
-->

```agda
total : ((x : A) → P x → Q x)
      → Σ A P → Σ A Q
total f (x , y) = x , f x y
```

Furthermore, the fibres of `total f` correspond to fibres of f, in the
following manner:

```agda
total-fibres : {f : (x : A) → P x → Q x} {x : A} {v : Q x}
             → Iso (fibre (f x) v) (fibre (total f) (x , v))
total-fibres {A = A} {P = P} {Q = Q} {f = f} {x = x} {v = v} = the-iso where

  to : {x : A} {v : Q x} → fibre (f x) v → fibre (total f) (x , v)
  to (v' , p) = (_ , v') , λ i → _ , p i

  from : {x : A} {v : Q x} → fibre (total f) (x , v) → fibre (f x) v
  from ((x , v) , p) = transport (λ i → fibre (f (p i .fst)) (p i .snd)) (v , refl)

  the-iso : {x : A} {v : Q x} → Iso (fibre (f x) v) (fibre (total f) (x , v))
  the-iso .fst = to
  the-iso .snd .is-iso.from = from
  the-iso .snd .is-iso.rinv ((x , v) , p) =
    J (λ { _ p → to (from ((x , v) , p)) ≡ ((x , v) , p) })
      (ap to (J-refl {A = Σ A Q} (λ { (x , v) _ → fibre (f x) v } ) (v , refl)))
      p
  the-iso .snd .is-iso.linv (v , p) =
    J (λ { _ p → from (to (v , p)) ≡ (v , p) })
      (J-refl {A = Σ A Q} (λ { (x , v) _ → fibre (f x) v } ) (v , refl))
      p
```

:::{.definition #fibrewise-equivalence}
A fibrewise map `f : (x : _) → P x → Q` is a **fibrewise equivalence**
iff. `f x` is an equivalence for all $x$. It follows from the above that
a fibrewise transformation is a fibrewise equivalence iff. it induces an
equivalence of total spaces by `total`.
:::

```agda
total→equiv
  : {f : (x : A) → P x → Q x}
  → is-equiv (total f)
  → {x : A} → is-equiv (f x)
total→equiv eqv {x} .is-eqv y = iso→is-hlevel 0
  (total-fibres .snd .is-iso.from)
  (is-iso.inverse (total-fibres .snd))
  (eqv .is-eqv (x , y))

equiv→total : {f : (x : A) → P x → Q x}
            → ({x : A} → is-equiv (f x))
            → is-equiv (total f)
equiv→total always-eqv .is-eqv y =
  iso→is-hlevel 0
    (total-fibres .fst)
    (total-fibres .snd)
    (always-eqv .is-eqv (y .snd))
```

## Equivalences over {defines="equivalence-over"}

We can generalise the notion of fibrewise equivalence to families
$P : A \to \ty$, $Q : B \to \ty$ over *different* base types,
provided we have an equivalence $e : A \simeq B$. In that case, we
say that $P$ and $Q$ are **equivalent over** $e$ if $P(a) \simeq Q(b)$
whenever $a : A$ and $b : B$ are identified [[over|path over]] $e$.

Using univalence, we can see this as a special case of [[dependent paths]],
where the base type is taken to be the universe and the type family sends
a type $A$ to the type of type families over $A$. However, the
following explicit definition is easier to work with.

<!--
```agda
module _ {ℓa ℓb} {A : Type ℓa} {B : Type ℓb} where
```
-->

```agda
  _≃[_]_ : ∀ {ℓp ℓq} (P : A → Type ℓp) (e : A ≃ B) (Q : B → Type ℓq) → Type _
  P ≃[ e ] Q = ∀ (a : A) (b : B) → e .fst a ≡ b → P a ≃ Q b
```

While this definition is convenient to *use*, we provide helpers that
make it easier to *build* equivalences over.

<!--
```agda
  module _ {ℓp ℓq} {P : A → Type ℓp} {Q : B → Type ℓq} (e : A ≃ B) where
    private module e = Equiv e
```
-->

```agda
    over-left→over : (∀ (a : A) → P a ≃ Q (e.to a)) → P ≃[ e ] Q
    over-left→over e' a b p = e' a ∙e line→equiv (λ i → Q (p i))

    over-right→over : (∀ (b : B) → P (e.from b) ≃ Q b) → P ≃[ e ] Q
    over-right→over e' a b p = line→equiv (λ i → P (e.adjunctl p i)) ∙e e' b

    prop-over-ext
      : (∀ {a} → is-prop (P a))
      → (∀ {b} → is-prop (Q b))
      → (∀ (a : A) → P a → Q (e.to a))
      → (∀ (b : B) → Q b → P (e.from b))
      → P ≃[ e ] Q
    prop-over-ext propP propQ P→Q Q→P a b p = prop-ext propP propQ
      (subst Q p ∘ P→Q a)
      (subst P (sym (e.adjunctl p)) ∘ Q→P b)
```

An equivalence over $e$ induces an equivalence of total spaces:

```agda
    over→total : P ≃[ e ] Q → Σ A P ≃ Σ B Q
    over→total e' = Σ-ap e λ a → e' a (e.to a) refl
```

<!--
```agda
subst-fibrewise
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {B' : A → Type ℓ''} (g : ∀ x → B x → B' x)
  → {x y : A} (p : x ≡ y) (h : B x) → subst B' p (g x h) ≡ g y (subst B p h)
subst-fibrewise {B = B} {B'} g {x} p h = J (λ y p → subst B' p (g x h) ≡ g y (subst B p h)) (transport-refl _ ∙ ap (g x) (sym (transport-refl _))) p

subst₂-fibrewise
  : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Type ℓ} {B : A → Type ℓ'}
  → {C : (x : A) → B x → Type ℓ''} {C' : (x : A) → B x → Type ℓ'''}
  → (g : ∀ x y → C x y → C' x y)
  → {x y : A} (p : x ≡ y) {α : B x} {β : B y} (q : PathP (λ i → B (p i)) α β) (e : C x α)
  → subst₂ C' p q (g x α e) ≡ g y β (subst₂ C p q e)
subst₂-fibrewise {A = A} {B} {C} {C'} g {x} p {α} q e =
  subst-fibrewise {A = Σ A B} {uncurry C} {uncurry C'} (λ (x , y) v → g x y v) (Σ-pathp p q) e

map-over≃fibrewise-map
  : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (f : A → C) (g : B → C)
  → (Σ[ e ∈ (A → B) ] (∀ x → f x ≡ g (e x)))
  ≃ ((c : C) → fibre f c → fibre g c)
map-over≃fibrewise-map {A = A} {B = B} {C = C} f g = Iso→Equiv (to , iso from ri li)
  module map-over≃fibrewise-map where
  T = Σ[ e ∈ (A → B) ] (∀ x → f x ≡ g (e x))

  to : T → (c : C) → fibre f c → fibre g c
  to (e , α) c (x , p) = e x , sym (α x) ∙ p

  from : ((c : C) → fibre f c → fibre g c) → T
  from h = (λ a → h (f a) (a , refl) .fst) , λ x → sym (h (f x) (x , refl) .snd)

  ri : is-right-inverse from to
  ri h = funext λ f → funext λ (x , p) →
    J (λ c p → curry (to (from h) c) x p ≡ curry (h c) x p)
      (Σ-pathp refl (∙-idr _))
      p

  li : is-left-inverse from to
  li f = Σ-pathp refl $ funext λ x → ∙-idr _

equiv-over≃fibrewise-equiv
  : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (f : A → C) (g : B → C)
  → (Σ[ e ∈ (A ≃ B) ] (∀ x → f x ≡ g (e .fst x)))
  ≃ ((c : C) → fibre f c ≃ fibre g c)
equiv-over≃fibrewise-equiv {A = A} {B = B} {C = C} f g = Iso→Equiv (to , iso from ri li) where
  module t = map-over≃fibrewise-map f g
  module f = map-over≃fibrewise-map g f
  T' = Σ[ e ∈ (A ≃ B) ] (∀ x → f x ≡ g (e .fst x))

  to : T' → (c : C) → fibre f c ≃ fibre g c
  to (e , α) c = to' c , done where
    module e = Equiv e

    to' : ∀ c → fibre f c → fibre g c
    to' = t.to (e .fst , α)

    from' : ∀ c → fibre g c → fibre f c
    from' c = f.to (e.from , λ x → ap g (sym (e.ε x)) ∙ sym (α (e.from x))) c

    coh₁ : (x : B) → to' (g x) (from' (g x) (x , refl)) ≡ (x , refl)
    coh₁ x = Σ-pathp (e.ε x) $ commutes→square $ ap (_∙ refl) $ sym $
      sym (α (e.from x)) ∙ sym (ap g (sym (e.ε x)) ∙ sym (α (e.from x))) ∙ refl
        ≡⟨ ap₂ _∙_ refl (∙-idr _ ∙ sym-∙ _ _) ⟩
      sym (α (e.from x)) ∙ α (e.from x) ∙ ap g (e.ε x)
        ≡⟨ ∙-cancell _ _ ⟩
      ap g (e.ε x) ∎

    coh₂ : (x : A) → from' (f x) (to' (f x) (x , refl)) ≡ (x , refl)
    coh₂ x = Σ-pathp (e.η x) $ commutes→square $ ap (_∙ refl) $ sym $
      sym (ap g (sym (e.ε _)) ∙ sym (α (e.from _))) ∙ sym (α x) ∙ refl ≡⟨ ap₂ _∙_ (sym-∙ _ _) (∙-idr _) ⟩
      (α (e.from _) ∙ ap g (e.ε _)) ∙ sym (α x)                        ≡⟨ ap (λ e → (α (e.from _) ∙ ap g e) ∙ sym (α x)) (sym (e.zig x)) ⟩
      (α (e.from _) ∙ ap g (ap (e .fst) (e.η x))) ∙ sym (α x)          ≡⟨ ∙-pullr (sym (homotopy-natural (λ x → sym (α x)) (e.η _))) ⟩
      α (e.from _) ∙ sym (α (e.from _)) ∙ ap f (e.η x)                 ≡⟨ ∙-cancell _ _ ⟩
      ap f (e.η x)                                                     ∎

    done : is-equiv (to' c)
    done = is-iso→is-equiv (iso (from' c)
      (λ (x , p) → J (λ c p → to' c (from' c (x , p)) ≡ (x , p)) (coh₁ x) p)
      (λ (x , p) → J (λ c p → from' c (to' c (x , p)) ≡ (x , p)) (coh₂ x) p))

  from : ((c : C) → fibre f c ≃ fibre g c) → T'
  from e = (to' .fst , done) , to' .snd where
    module e (c : C) = Equiv (e c)
    to' : t.T
    to' = t.from λ c → e.to c

    from' : f.T
    from' = f.from λ c → e.from c

    coh₁ : is-right-inverse (from' .fst) (to' .fst)
    coh₁ x =
      e.to (f (e.from (g x) (x , refl) .fst)) ((e.from (g x) (x , refl) .fst) , refl) .fst
        ≡⟨ ap₂ (λ a b → e.to a (e.from (g x) (x , refl) .fst , b) .fst) _ (λ i j → e.from (g x) (x , refl) .snd (i ∧ j)) ⟩
      e.to (g x) (e.from (g x) (x , refl)) .fst
        ≡⟨ ap fst (e.ε (g x) (x , refl)) ⟩
      x ∎

    coh₂ : is-left-inverse (from' .fst) (to' .fst)
    coh₂ x =
      e.from (g (e.to (f x) (x , refl) .fst)) (e.to (f x) (x , refl) .fst , refl) .fst
        ≡⟨ ap₂ (λ a b → e.from a (e.to (f x) (x , refl) .fst , b) .fst) _ (λ i j → e.to (f x) (x , refl) .snd (i ∧ j)) ⟩
      e.from (f x) (e.to (f x) (x , refl)) .fst
        ≡⟨ ap fst (e.η (f x) _) ⟩
      x ∎

    done : is-equiv (to' .fst)
    done = is-iso→is-equiv (iso (from' .fst) coh₁ coh₂)

  ri : is-right-inverse from to
  ri h = funext λ c → Σ-prop-path is-equiv-is-prop (happly (t.ri (λ c → h c .fst)) c)

  li : is-left-inverse from to
  li f = Σ-pathp (Σ-prop-path is-equiv-is-prop refl) (funext λ x → ∙-idr _)
```
-->
