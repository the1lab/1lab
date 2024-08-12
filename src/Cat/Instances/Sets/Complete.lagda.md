<!--
```agda
open import Cat.Diagram.Limit.Finite
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Equaliser
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Prelude
```
-->

```agda
module Cat.Instances.Sets.Complete where
```

# Sets is complete

We prove that the category of $o$-sets is $(\iota,\kappa)$-complete for
any universe levels $\iota \le o$ and $\kappa \le o$. Inverting this to
speak of maxima rather than ordering, to admit all $(\iota,\kappa)$-limits,
we must be in _at least_ the category of $(\iota \sqcup \kappa)$-sets,
but any extra adjustment $o$ is also acceptable. So, suppose we have an
indexing category $\cD$ and a diagram $F : \cD \to \Sets$; Let's
build a limit for it!

```agda
Sets-is-complete : ∀ {ι κ o} → is-complete ι κ (Sets (ι ⊔ κ ⊔ o))
Sets-is-complete {J = D} F = to-limit (to-is-limit lim) module Sets-is-complete where
  module D = Precategory D
  module F = Functor F
  open make-is-limit
```

Since `Set`{.Agda} is closed under (arbitrary) [[products]], we can build
the limit of an arbitrary diagram $F$ --- which we will write $\lim F$
--- by first taking the product $\prod_{j : \cD} F(j)$ (which is a
set of dependent functions), then restricting ourselves to the subset of
those for which $F(g) \circ f(x) = f(y)$, i.e., those which are cones
over $F$.

```agda
  apex : Set _
  apex = el! $
    Σ[ f ∈ ((j : D.Ob) → ∣ F.₀ j ∣) ]
      (∀ x y (g : D.Hom x y) → F.₁ g (f x) ≡ (f y))
```

To form a cone, given an object $x : \cD$, and an inhabitant $(f,p)$
of the type underlying `f-apex`{.Agda}, we must cough up (for
`ψ`{.Agda}) an object of $F(x)$; But this is exactly what $f(x)$ gives
us. Similarly, since $p$ witnesses that $\psi$ `commutes`{.Agda}, we can
project it directly.

Given some other cone $K$, to build a cone homomorphism $K \to \lim F$,
recall that $K$ comes equipped with its own function $\psi : \prod_{x :
\cD} K \to F(x)$, which we can simply flip around to get a function
$K \to \prod_{x : \cD} F(x)$; This function is in the subset carved
out by $\lim F$ since $K$ is a cone, hence $F(f) \circ \psi(x) =
\psi(y)$, as required.

```agda
  -- open Terminal
  lim : make-is-limit F apex
  lim .ψ x (f , p) = f x
  lim .commutes f = funext λ where
    (_ , p) → p _ _ f
  lim .universal eta p x =
    (λ j → eta j x) , λ x y f → p f $ₚ _
  lim .factors _ _ = refl
  lim .unique eta p other q = funext λ x →
    Σ-prop-path! (funext λ j → q j $ₚ x)
```

<!--
```agda
module _ {ℓ} where
  open Precategory (Sets ℓ)

  private variable
    A B : Set ℓ
    f g : ⌞ A ⌟ → ⌞ B ⌟

  open Terminal
  open is-product
  open Binary-products
  open Equalisers
  open Pullbacks
```
-->

## Finite set-limits

For expository reasons, we present the computation of the most famous
shapes of [[finite limit]] ([[terminal objects]], [[products]], [[pullbacks]],
and [[equalisers]]) in the category of sets. All the definitions below
are redundant, since finite limits are always small, and thus the
category of sets of _any_ level $\ell$ admits them.

```agda
  Sets-terminal : Terminal (Sets ℓ)
  Sets-terminal .top = el! (Lift _ ⊤)
  Sets-terminal .has⊤ _ = hlevel 0
```

Products are given by product sets:

```agda
  Sets-products : Binary-products (Sets ℓ)
  Sets-products ._⊗₀_ A B = el! (∣ A ∣ × ∣ B ∣)
  Sets-products .π₁ = fst
  Sets-products .π₂ = snd
  Sets-products .⟨_,_⟩ f g x = f x , g x
  Sets-products .π₁∘⟨⟩ = refl
  Sets-products .π₂∘⟨⟩ = refl
  Sets-products .⟨⟩-unique p q i x = p i x , q i x
```

Equalisers are given by carving out the subset of $A$ where $f$ and $g$ agree
using $\Sigma$:

```agda
  Sets-equalisers : Equalisers (Sets ℓ)
  Sets-equalisers .Equ {X} {Y} f g = el! (Σ[ x ∈ X ] (f x ≡ g x))
  Sets-equalisers .equ f g = fst
  Sets-equalisers .equal = funext snd
  Sets-equalisers .equalise e p x = e x , p $ₚ x
  Sets-equalisers .equ∘equalise = refl
  Sets-equalisers .equalise-unique p =
      funext λ x → Σ-prop-path! (p $ₚ x)
```

Pullbacks are the same, but carving out a subset of $A \times B$.

```agda
  Sets-pullbacks : Pullbacks (Sets ℓ)
  Sets-pullbacks .Pb {X} {Y} {Z} f g = el! (Σ[ x ∈ X ] Σ[ y ∈ Y ] (f x ≡ g y))
  Sets-pullbacks .p₁ f g (x , _ , _) = x
  Sets-pullbacks .p₂ f g (_ , y , _) = y
  Sets-pullbacks .square = funext (snd ⊙ snd)
  Sets-pullbacks .pb p1 p2 sq x = p1 x , p2 x , sq $ₚ x
  Sets-pullbacks .p₁∘pb = refl
  Sets-pullbacks .p₂∘pb = refl
  Sets-pullbacks .pb-unique p q =
    funext λ x → Σ-pathp (p $ₚ x) (Σ-pathp (q $ₚ x) prop!)
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
