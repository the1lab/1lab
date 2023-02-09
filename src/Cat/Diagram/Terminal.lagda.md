```agda
open import Cat.Diagram.Limit.Base
open import Cat.Functor.Kan.Base
open import Cat.Instances.Shape.Initial
open import Cat.Prelude

module Cat.Diagram.Terminal {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
open import Cat.Reasoning C
```
-->

# Terminal objects

An object $\top$ of a category $\mathcal{C}$ is said to be **terminal**
if it admits a _unique_ map from any other object. We can concisely
define this as the [limit] of the [empty diagram].

[limit]: Cat.Diagram.Limit.Base.html
[empty diagram]: Cat.Instances.Shape.Initial.html

```agda
is-terminal : Ob → Type _
is-terminal x = is-limit {C = C} ¡F x ¡nt

Terminal : Type _
Terminal = Limit {C = C} ¡F
```

## Concretely

We use this definition as it is abstract: it allows us to use general
theorems about limits when working with terminal objects! However,
it is also abstract, which means that working with a _specific_ terminal
object becomes a lot more difficult. To work around this, we provide
an auxiliary record `make-is-terminal` that describes terminal objects
more concretely.

```agda
record make-is-terminal (t : Ob) : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    ! : ∀ {x} → Hom x t
    !-unique : ∀ {x} → (f : Hom x t) → f ≡ !

  !-unique₂ : ∀ {x} {f g : Hom x t} → f ≡ g
  !-unique₂ = !-unique _ ∙ sym (!-unique _)

  ⊤-id : ∀ (f : Hom t t) → f ≡ id
  ⊤-id _ = !-unique₂

  !-contr : ∀ {x} → is-contr (Hom x t)
  !-contr = contr ! λ f → sym (!-unique f)
```

If we have this data, then we can make a value of `is-terminal`{.Agda}.

```agda
to-is-terminal : ∀ {t} → make-is-terminal t → is-terminal t
to-is-terminal {t = t} mkterm = isl where
  open make-is-terminal mkterm
  open is-ran
  open _=>_

  isl : is-limit ¡F t ¡nt
  isl .σ _ .η _ = !
  isl .σ _ .is-natural _ _ _ = !-unique₂
  isl .σ-comm = Nat-path (λ ())
  isl .σ-uniq p = Nat-path λ _ → sym $ !-unique _
```

To use the data of `is-terminal`, we provide a function for *un*making
a terminal object.

```agda
unmake-is-terminal : ∀ {t} → is-terminal t → make-is-terminal t
unmake-is-terminal {t = t} lim = term module unmake-terminal where
  open make-is-terminal
  module lim = is-limit lim

  term : make-is-terminal t 
  term .! = lim.universal (λ ()) (λ ())
  term .!-unique f = lim.unique (λ ()) (λ ()) f (λ ())
```

<!--
```agda
module is-terminal {t} (term : is-terminal t) where
  open make-is-terminal (unmake-is-terminal term) public
```
-->

We do a similar construction for the bundled form of terminal objects.

```agda
record make-terminal : Type (o ⊔ ℓ) where
  no-eta-equality
  field
    top : Ob
    has-is-terminal : make-is-terminal top

  open make-is-terminal has-is-terminal public
```

<!--
```agda
to-terminal : make-terminal → Terminal
to-terminal mt = to-limit (to-is-terminal has-is-terminal)
  where open make-terminal mt

module Terminal (t : Terminal) where
  open Limit t
  open is-ran
  open Functor
  open _=>_

  top : Ob
  top = apex

  has-is-terminal : is-terminal top
  has-is-terminal =
    to-is-limitp (unmake-limit has-limit) (λ { {()} })

  open is-terminal has-is-terminal public
 
open Terminal
```
-->

## Uniqueness

If a category has two terminal objects $t_1$ and $t_2$, then there is a
unique isomorphism $t_1 \cong t_2$. This follows directly from [uniqueness
of limits]!

[uniqueness of limits]: Cat.Diagram.Limit.Base#uniqueness

```agda
!-inverses : (t1 t2 : Terminal) → Inverses (t1 .!) (t2 .!)
!-inverses t1 t2 =
  limits→inversesp
    (has-is-terminal t1)
    (has-is-terminal t2)
    (λ { {()} }) (λ { {()} })

!-invertible : (t1 t2 : Terminal) → is-invertible (t1 .! {x = top t2})
!-invertible t1 t2 =
  limits→invertiblep
  (has-is-terminal t1)
  (has-is-terminal t2)
  (λ { {()} })

⊤-unique : (t1 t2 : Terminal) → top t1 ≅ top t2
⊤-unique t1 t2 =
  limits-unique 
    (has-is-terminal t2)
    (has-is-terminal t1)
```

If $C$ is additionally a category, it has a propositional space of
terminal objects.

```agda
Terminal-is-prop : is-category C → is-prop Terminal
Terminal-is-prop = Limit-is-prop
```

Furtheremore, if there is *any* invertible morphism out of a terminal
object, then the codomain must also be a terminal object.

```agda
is-invertible→is-terminal
  : ∀ {x y} {f : Hom x y}
  → is-invertible f
  → is-terminal x
  → is-terminal y
is-invertible→is-terminal {f = f} invert term =
  is-invertible→is-limitp term
    (λ ()) (λ ()) (λ { {()} })
    (make-invertible f
      (term.⊤-id _)
      (ap (f ∘_) (sym (term.!-unique _)) ∙ invert.invl))
  where
    module term = is-terminal term
    module invert = is-invertible invert
```

This implies that any object that is isomorphic to a terminal object
must also be a terminal object.

```agda
iso→is-terminal : ∀ {x y} → x ≅ y → is-terminal x → is-terminal y
iso→is-terminal f term =
  is-invertible→is-terminal (iso→invertible f) term
```
