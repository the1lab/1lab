```agda
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
    map .commutes = refl

    map-unique : ∀ m → map ≡ m
    map-unique m = Cone-hom-path _ (funext λ x →
      Σ-prop-path comm-prop (funext (λ j i → m .commutes (~ i) x)))
```
