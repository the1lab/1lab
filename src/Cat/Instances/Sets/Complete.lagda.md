```agda
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Terminal
open import Cat.Prelude

module Cat.Instances.Sets.Complete where
```

# Sets is complete

We prove that the category of $o$-sets is $(\iota,\kappa)$-complete for
any universe levels $\iota \le o$ and $\kappa \le o$. Inverting this to
speak of maxima rather than ordering, to admit all $(\iota,\kappa)$-limits,
we must be in _at least_ the category of $(\iota \sqcup \kappa)$-sets,
but any extra adjustment $o$ is also acceptable. So, suppose we have an
indexing category $\ca{D}$ and a diagram $F : \ca{D} \to \sets$; Let's
build a limit for it!

```agda
Sets-is-complete : ∀ {ι κ o} → is-complete ι κ (Sets (ι ⊔ κ ⊔ o))
Sets-is-complete {D = D} F = lim where
  module D = Precategory D
  module F = Functor F

  comm-prop : ∀ f → is-prop (∀ x y (g : D.Hom x y) → F.₁ g (f x) ≡ (f y))
  comm-prop f = Π-is-hlevel 1 λ _ → Π-is-hlevel 1 λ _ → Π-is-hlevel 1 λ _ →
                F.₀ _ .is-tr _ _
```

Since `Set`{.Agda} is closed under (arbitrary) `products`{.Agda
ident=Π-is-level}, we can build the limit of an arbitrary diagram $F$
--- which we will write $\lim F$ --- by first taking the product
$\prod_{j : \ca{D}} F(j)$ (which is a set of dependent functions), then
restricting ourselves to the subset of those for which $F(g) \circ f(x)
= f(y)$, i.e., those which are cones over $F$.

```agda
  f-apex : Set _
  f-apex .∣_∣   = Σ[ f ∈ ((j : D.Ob) → ∣ F.₀ j ∣) ]
                    (∀ x y (g : D.Hom x y) → F.₁ g (f x) ≡ (f y))

  f-apex .is-tr = Σ-is-hlevel 2 (Π-is-hlevel 2 (λ x → F.₀ x .is-tr))
                    (λ f → is-prop→is-set (comm-prop f))
```

To form a cone, given an object $x : \ca{D}$, and an inhabitant $(f,p)$
of the type underlying `f-apex`{.Agda}, we must cough up (for
`ψ`{.Agda}) an object of $F(x)$; But this is exactly what $f(x)$ gives
us. Similarly, since $p$ witnesses that $\psi$ `commutes`{.Agda}, we can
project it directly.

```agda
  open Cone
  cone : Cone F
  cone .Cone.apex    = f-apex
  cone .ψ x          = λ { (f , p) → f x }
  cone .commutes o   = funext λ { (_ , p) → p _ _ o }
```

Given some other cone $K$, to build a cone homomorphism $K \to \lim F$,
recall that $K$ comes equipped with its own function $\psi : \prod_{x :
\ca{D}} K \to F(x)$, which we can simply flip around to get a function
$K \to \prod_{x : \ca{D}} F(x)$; This function is in the subset carved
out by $\lim F$ since $K$ is a cone, hence $F(f) \circ \psi(x) =
\psi(y)$, as required.

```agda
  open Terminal
  lim : Limit F
  lim .top = cone
  lim .has⊤ K = contr map map-unique where
    module K = Cone K
    open Cone-hom
    map : Cone-hom F K cone
    map .hom x = (λ j → K.ψ j x) , λ x y f → happly (K.commutes f) _
    map .commutes _ = refl

    map-unique : ∀ m → map ≡ m
    map-unique m = Cone-hom-path _ (funext λ x →
      Σ-prop-path comm-prop (funext λ y i → m .commutes y (~ i) x))
```

<!--
```agda
module _ {ℓ} where
  open import Cat.Diagram.Equaliser (Sets ℓ)
  open import Cat.Diagram.Pullback (Sets ℓ)
  open import Cat.Diagram.Product (Sets ℓ)
  open import Cat.Reasoning (Sets ℓ)

  private variable
    A B : Set ℓ
    f g : Hom A B

  open Terminal
  open is-product
  open Product
  open is-pullback
  open Pullback
  open is-equaliser
  open Equaliser
```
-->

## Finite set-limits

For expository reasons, we present the computation of the most famous
shapes of finite limit (terminal objects, products, pullbacks, and
equalisers) in the category of sets. All the definitions below are
redundant, since finite limits are always small, and thus the category
of sets of _any_ level $\ell$ admits them.

```agda
  Sets-terminal : Terminal (Sets ℓ)
  Sets-terminal .top = Lift _  ⊤ , is-prop→is-set (λ _ _ → refl)
  Sets-terminal .has⊤ _ = fun-is-hlevel 0 (contr (lift tt) λ x i → lift tt)
```

Products are given by product sets:

```agda
  Sets-products : (A B : Set ℓ) → Product A B
  Sets-products A B .apex = (∣ A ∣ × ∣ B ∣) , ×-is-hlevel 2 (A .is-tr) (B .is-tr)
  Sets-products A B .π₁ = fst
  Sets-products A B .π₂ = snd
  Sets-products A B .has-is-product .⟨_,_⟩ f g x = f x , g x
  Sets-products A B .has-is-product .π₁∘factor = refl
  Sets-products A B .has-is-product .π₂∘factor = refl
  Sets-products A B .has-is-product .unique o p q i x = p i x , q i x
```

Equalisers are given by carving out the subset of $A$ where $f$ and $g$ agree
using $\Sigma$:

```agda
  Sets-equalisers : (f g : Hom A B) → Equaliser {A = A} {B = B} f g
  Sets-equalisers {A = A} {B = B} f g = eq where
    eq : Equaliser f g
    eq .apex = Σ[ x ∈ ∣ A ∣ ] (f x ≡ g x)
             , Σ-is-hlevel 2 (A .is-tr) λ _ → is-prop→is-set (B .is-tr _ _)
    eq .equ = fst
    eq .has-is-eq .equal = funext snd
    eq .has-is-eq .limiting {e′ = e′} p x = e′ x , happly p x
    eq .has-is-eq .universal = refl
    eq .has-is-eq .unique {p = p} q =
      funext λ x → Σ-prop-path (λ _ → B .is-tr _ _) (happly (sym q) x)
```

Pullbacks are the same, but carving out a subset of $A \times B$.

```agda
  Sets-pullbacks : ∀ {A B C} (f : Hom A C) (g : Hom B C)
                → Pullback {X = A} {Y = B} {Z = C} f g
  Sets-pullbacks {A = A} {B = B} {C = C} f g = pb where
    pb : Pullback f g
    pb .apex .∣_∣ = Σ[ x ∈ ∣ A ∣ ] Σ[ y ∈ ∣ B ∣ ] (f x ≡ g y)
    pb .apex .is-tr =
      Σ-is-hlevel 2 (A .is-tr) λ _ →
      Σ-is-hlevel 2 (B .is-tr) λ _ →
      is-prop→is-set (C .is-tr _ _)
    pb .p₁ (x , _ , _) = x
    pb .p₂ (_ , y , _) = y
    pb .has-is-pb .square = funext (snd ⊙ snd)
    pb .has-is-pb .limiting {p₁' = p₁'} {p₂'} p a = p₁' a , p₂' a , happly p a
    pb .has-is-pb .p₁∘limiting = refl
    pb .has-is-pb .p₂∘limiting = refl
    pb .has-is-pb .unique {p = p} {lim' = lim'} q r i x =
      q i x , r i x ,
      λ j → is-set→squarep (λ i j → C .is-tr)
        (λ j → f (q j x)) (λ j → lim' x .snd .snd j) (happly p x) (λ j → g (r j x)) i j
```

Hence, `Sets`{.Agda} is finitely complete:

```agda
  open Finitely-complete

  Sets-finitely-complete : Finitely-complete (Sets ℓ)
  Sets-finitely-complete .terminal = Sets-terminal
  Sets-finitely-complete .products = Sets-products
  Sets-finitely-complete .equalisers = Sets-equalisers
  Sets-finitely-complete .pullbacks = Sets-pullbacks
```
