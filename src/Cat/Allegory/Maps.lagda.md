```agda
open import Cat.Allegory.Base
open import Cat.Prelude

module Cat.Allegory.Maps where
```

# Maps in allegories

Suppose we have an allegory $\ca{A}$ --- for definiteness you could
consider the archetypal allegory $\Rel$ --- but what we really wanted
was to get our hands on an ordinary _category_. That is: we want, given
some category of "sets and relations", to recover the associated
category of "sets and functions". So, let's start by thinking about $\Rel$!

If you have a relation $R \mono A \times B$, when does it correspond to
a function $A \to B$? Well, it must definitely be _functional_: if we
want $R(x, y)$ to represent "$f(x) = y$", then surely if $R(x, y) \land
R(x, z)$, we must have $y = z$. In allegorical language, we would say
$RR^o \le \id{id}$, which we can calculate to mean (in $\Rel$) that, for
all $x, y$,

$$
(\exists z, R(z, x) \land R(z, y)) \to (x = y)\text{.}
$$

It must also be an _entire_ relation: Every $x$ must at least one $y$ it
is related to, and by functionality, _exactly_ one $y$ it is related to.
This is the "value of" the function at $y$.

```agda
module _ {o ℓ h} (A : Allegory o ℓ h) where
  open Allegory A
  record is-map x y (f : Hom x y) : Type h where
    constructor mapping
    field
      functional : f ∘ f ᵒ ≤ id
      entire     : id ≤ f ᵒ ∘ f

module _ {o ℓ h} {A : Allegory o ℓ h} where
  open Allegory A
  open is-map
  instance
    H-Level-is-map : ∀ {x y} {f : Hom x y} {n} → H-Level (is-map A x y f) (suc n)
    H-Level-is-map = prop-instance {T = is-map A _ _ _} λ where
      x y i .functional → ≤-thin (x .functional) (y .functional) i
      x y i .entire     → ≤-thin (x .entire) (y .entire) i
```

We can calculate that a functional entire relation is precisely a
function between sets: Functionality ensures that (fixing a point $a$ in
the domain) the space of "points in the codomain related to $a$" is a
subsingleton, and entireness ensures that it is inhabited; By unique
choice, we can project the value of the function.

```agda
Rel-map→function
  : ∀ {ℓ} {x y : Set ℓ} {f : Allegory.Hom (Rel ℓ) x y}
  → is-map (Rel ℓ) x y f
  → ∣ x ∣ → ∣ y ∣
Rel-map→function {x = x} {y} {rel} map elt =
  ∥-∥-rec {P = Σ ∣ y ∣ λ b → ∣ rel elt b ∣}
    (λ { (x , p) (y , q) → Σ-prop-path (λ _ → hlevel!) (functional′ p q) })
    (λ x → x)
    (entire′ elt) .fst
  where
    module map = is-map map
    functional′ : ∀ {a b c} → ∣ rel a b ∣ → ∣ rel a c ∣ → b ≡ c
    functional′ r1 r2 = map.functional _ _ (inc (_ , r1 , r2))

    entire′ : ∀ a → ∃ ∣ y ∣ λ b → ∣ rel a b ∣
    entire′ a =
      ∥-∥-rec squash (λ { (x , y , R) → inc (x , R) })
        (map.entire a a refl)
```

## The category of maps

Given an allegory $\ca{A}$, we can form a category $\id{Map}(\ca{A})$
with the same objects as $\ca{A}$, but considering only the maps (rather
than arbitrary relations).

```agda
module _ {o ℓ h} (A : Allegory o ℓ h) where
  private module A = Allegory A
  open is-map
  open Precategory

  Maps[_] : Precategory _ _
  Maps[_] .Ob  = A.Ob
  Maps[_] .Hom x y = Σ (A.Hom x y) (is-map A x y)
  Maps[_] .Hom-set x y = hlevel 2
```

Proving that maps compose is a bit annoying, but it follows from the
properties of the duality involution. By the way: This is essentially
the proof that adjunctions compose! This is because, sneakily, the
property "being a map" is defined to be $f \dashv f^o$, but without
using those words.

```agda
  Maps[_] .id = A.id , mapping
    (subst (A._≤ A.id) (sym (A.idl _ ∙ dual-id A)) A.≤-refl)
    (subst (A.id A.≤_) (sym (A.idr _ ∙ dual-id A)) A.≤-refl)

  Maps[_] ._∘_ (f , m) (g , m′) = f A.∘ g , mapping
    (subst (A._≤ A.id) (sym ( ap ((f A.∘ g) A.∘_) A.dual-∘
                           ·· sym (A.assoc _ _ _)
                           ·· ap (f A.∘_) (A.assoc _ _ _)))
      (A.≤-trans (A.≤-refl A.◆ (m′ .functional A.◆ A.≤-refl))
        (subst (A._≤ A.id) (sym (ap (f A.∘_) (A.idl _)))
          (m .functional))))
    (A.≤-trans (m′ .entire)
      (transport (sym
        (ap₂ A._≤_
          (ap₂ A._∘_ refl (sym (A.idl _)))
          (  ap₂ A._∘_ A.dual-∘ refl
          ·· sym (A.assoc _ _ _)
          ·· ap (g A.ᵒ A.∘_) (A.assoc _ _ _))))
        (A.≤-refl A.◆ (m .entire A.◆ A.≤-refl))))

  Maps[_] .idr f = Σ-prop-path (λ _ → hlevel 1) (A.idr _)
  Maps[_] .idl f = Σ-prop-path (λ _ → hlevel 1) (A.idl _)
  Maps[_] .assoc f g h = Σ-prop-path (λ _ → hlevel 1) (A.assoc _ _ _)
```
