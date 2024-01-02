<!--
```agda
open import Cat.Instances.Sets.Complete
open import Cat.Displayed.Cocartesian
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Doctrine
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Prelude

open import Order.Frame
open import Order.Base

import Cat.Reasoning as Cat

import Order.Frame.Reasoning as Frm

open Regular-hyperdoctrine
open Cocartesian-fibration
open Cartesian-fibration
open Cocartesian-lift
open Cartesian-lift
open is-cocartesian
open is-cartesian
open is-product
open Displayed
open Terminal
open Product
```
-->

```agda
module Cat.Displayed.Doctrine.Frame where
```

# Indexed frames

An example of [[regular hyperdoctrine]] that is not the [[poset of
subobjects]] of a [[regular category]] is given by the canonical
indexing of a [[frame]] $F$, the [[bifibration]] corresponding through
the Grothendieck construction to $\hom(-,X)$. We will construct this in
very explicit stages.

```agda
Indexed-frame : ∀ {o ℓ κ} → Frame o ℓ → Regular-hyperdoctrine (Sets κ) (o ⊔ κ) (ℓ ⊔ κ)
Indexed-frame {o = o} {ℓ} {κ} F = idx where
```

<!--
```agda
  module F = Frm (F .snd)

  private opaque
    isp : ∀ {x : Type κ} {f g : x → ⌞ F ⌟} → is-prop (∀ x → f x F.≤ g x)
    isp = Π-is-hlevel 1 λ _ → F.≤-thin
```
-->

## The indexing

As the underlying [[displayed category]] of our hyperdoctrine, we'll
fibre the [[slice category]] $\Sets/F$ over $\Sets$: The objects over a
set $S$ are the functions $S \to F$. However, rather than a discrete
fibration, we have a fibration into posets: the ordering at each fibre
is pointwise, and we can extend this to objects in different fibres by
the equivalence $(x \le_f y) \equiv (x \le_{\id} f^*y)$ of maps into a
[[Cartesian lift]] of the codomain.

```agda
  disp : Displayed (Sets κ) (o ⊔ κ) (ℓ ⊔ κ)
  disp .Ob[_] S          = ⌞ S ⌟ → ⌞ F ⌟
  disp .Hom[_]     f g h = ∀ x → g x F.≤ h (f x)
  disp .Hom[_]-set f g h = is-prop→is-set isp

  disp .id'      x = F.≤-refl
  disp ._∘'_ p q x = F.≤-trans (q x) (p _)
```

<!--
```agda
  disp .idr' f'         = isp _ _
  disp .idl' f'         = isp _ _
  disp .assoc' f' g' h' = isp _ _
```
-->

Since our ordering at each fibre is the pointwise ordering, it follows
that our limits are also pointwise limits: the meet $f \cap g$ is the
function $x \mapsto f(x) \cap g(x)$, and the terminal object is the
function which is constantly the top element.

```agda
  prod : ∀ {S : Set κ} (f g : ⌞ S ⌟ → ⌞ F ⌟) → Product (Fibre disp S) f g
  prod f g .apex x = f x F.∩ g x
  prod f g .π₁ i   = F.∩≤l
  prod f g .π₂ i   = F.∩≤r
  prod f g .has-is-product .⟨_,_⟩ α β i = F.∩-universal _ (α i) (β i)
```

<!--
```agda
  prod f g .has-is-product .π₁∘factor    = isp _ _
  prod f g .has-is-product .π₂∘factor    = isp _ _
  prod f g .has-is-product .unique _ _ _ = isp _ _
```
-->

```agda
  term : ∀ S → Terminal (Fibre disp S)
  term S .top  _ = F.top
  term S .has⊤ f = is-prop∙→is-contr isp (λ i → F.!)
```

## As a fibration

As we have _defined_ the ordering by exploiting the existence of
Cartesian lifts, it should not be surprising that the lift $f^*g$ a
function $Y \to F$ along a function $X \to Y$ is simply the composite
$gf : X \to F$.

```agda
  cart : Cartesian-fibration disp
  cart .has-lift f g .x' x = g (f x)
  cart .has-lift f g .lifting i = F.≤-refl
  cart .has-lift f g .cartesian = record
    { universal = λ m p x → p x
    ; commutes  = λ m h'  → isp _ _
    ; unique    = λ m p   → isp _ _
    }
```

However, the *co*cartesian lifts are a lot more interesting, and their
construction involves a pretty heavy dose of [[propositional resizing]].
In ordinary predicative type theory, each frame is associated with a
particular level for which it admits arbitrary joins. But our
construction of the hyperdoctrine associated with a frame works for
indexing a frame over an _arbitrary_ category of sets! How does that
work?

The key observation is that the join $\bigcup_I f$ of a family $f : I
\to F$ can be replaced by the join $\bigcup_{\im f} \pi_1$ of its
_image_; and since $\im f$ can be made to exist at the same level as $F$
regardless of how large $I$ is, this replacement allows us to compute
joins of arbitrary families. More relevantly, it'll let us compute the
cocartesian lift of a function $g : X \to F$ along a function $X \to Y$.

```agda
  cocart : Cocartesian-fibration disp
  cocart .has-lift {x = X} {y = Y} f g = lifted module cocart where
```

At each $y : Y$, we would like to take the join

$$
\bigcup_{x : f^*(y)} g(x)
$$

indexed by the fibre of $f$ over $y$. But since we do not control the
size of that type, we can replace this by the join over the subset

$$
\{ e : \exists_{x : X} f(x) = y \land g(x) = e \}
$$

which is the image of $g$ as a function $f^*(y) \to F$.

```agda
    img : ⌞ Y ⌟ → Type _
    img y = Σ[ e ∈ ⌞ F ⌟ ] □ (Σ[ x ∈ ⌞ X ⌟ ] ((f x ≡ y) × (g x ≡ e)))

    exist : ⌞ Y ⌟ → ⌞ F ⌟
    exist y = F.⋃ {I = img y} fst
```

That this satisfies the universal property of a cocartesian lift is then
a calculation:

```agda
    lifted : Cocartesian-lift disp f g
    lifted .y' y      = exist y
    lifted .lifting i = F.⋃-inj (g i , inc (i , refl , refl))
    lifted .cocartesian .universal {u' = u'} m h' i = F.⋃-universal _ λ (e , b) →
      □-rec! (λ { (x , p , q) →
        e            F.=⟨ sym q ⟩
        g x          F.≤⟨ h' x ⟩
        u' (m (f x)) F.=⟨ ap u' (ap m p) ⟩
        u' (m i)     F.≤∎ }) b
    lifted .cocartesian .commutes m h = isp _ _
    lifted .cocartesian .unique   m x = isp _ _
```

## Putting it together

We're ready to put everything together. By construction, we have a
"category displayed in posets",

```agda
  idx : Regular-hyperdoctrine (Sets κ) _ _
  idx .ℙ                = disp
  idx .has-is-set  x    = Π-is-hlevel 2 λ _ → F.Ob-is-set
  idx .has-is-thin f g  = isp
  idx .has-univalence S = set-identity-system
    (λ _ _ _ _ → Cat.≅-path (Fibre disp _) (isp _ _))
    λ im → funextP λ i → F.≤-antisym (Cat.to im i) (Cat.from im i)
```

which is both a fibration and an opfibration over $\Sets$,

```agda
  idx .cartesian   = cart
  idx .cocartesian = cocart
```

with finite fibrewise limits preserved by reindexing,

```agda
  idx .fibrewise-meet x' y' = prod x' y'
  idx .fibrewise-top  S     = term S
  idx .subst-& f x' y'      = refl
  idx .subst-aye f          = refl
```

which satisfies Frobenius reciprocity and the Beck-Chevalley condition.
Frobenius reciprocity follows by some pair mangling and the infinite
distributive law in $F$:

```agda
  idx .frobenius {X} {Y} f {α} {β} = funext λ i → F.≤-antisym
    ( exist α i F.∩ β i                         F.=⟨ F.⋃-distribr _ _ ⟩
      F.⋃ {I = img α i} (λ (x , _) → x F.∩ β i) F.≤⟨
        F.⋃-universal _ (λ img → F.⋃-inj
          ( img .fst F.∩ β i
          , □-map (λ { (x , p , q) → x , p , ap₂ F._∩_ q (ap β p) }) (img .snd)))
      ⟩
      exist (λ x → α x F.∩ β (f x)) i           F.≤∎ )
    ( exist (λ x → α x F.∩ β (f x)) i           F.≤⟨
        F.⋃-universal _ (λ (e , p) → □-rec! (λ { (x , p , q) →
          e                                         F.=⟨ sym q ⟩
          α x F.∩ β (f x)                           F.=⟨ ap (α x F.∩_) (ap β p) ⟩
          α x F.∩ β i                               F.≤⟨ F.⋃-inj (α x , inc (x , p , refl)) ⟩
          F.⋃ {I = img α i} (λ (x , _) → x F.∩ β i) F.≤∎ }) p)
      ⟩
      F.⋃ {I = img α i} (λ (x , _) → x F.∩ β i) F.=⟨ sym (F.⋃-distribr _ _) ⟩
      exist α i F.∩ β i                         F.≤∎)
    where open cocart {X} {Y} f
```

And the Beck-Chevalley condition follows from the observation that a
pullback square induces an equivalence between $f^*(i)$ and $g^*(f i)$
which sends $\alpha(k x)$ to $\alpha$, so that the joins which define
both possibilities for quantification or substitution agree:

```agda
  idx .beck-chevalley {A} {B} {C} {D} {f} {g} {h} {k} ispb {α} =
    funext λ i → F.⋃-apⁱ (Iso→Equiv (eqv i))
    where
    module c X Y = cocart {X} {Y}
    module pb = is-pullback ispb
    open is-iso

    eqv : ∀ i → Iso (c.img D A h (λ x → α (k x)) i) (c.img B C g α (f i))
    eqv i .fst      (e , p) = e , □-map (λ { (d , p , q) → k d , sym (pb.square $ₚ _) ∙ ap f p , q }) p
    eqv i .snd .inv (e , p) = e , □-map (λ { (b , p , q) →
      let
        it : ⌞ D ⌟
        it = pb.universal {P' = el! (Lift _ ⊤)}
          {p₁' = λ _ → i} {p₂' = λ _ → b} (funext (λ _ → sym p)) (lift tt)
      in it , (pb.p₁∘universal $ₚ lift tt) , ap α (pb.p₂∘universal $ₚ lift tt) ∙ q }) p
    eqv i .snd .rinv (x , _) = refl ,ₚ squash _ _
    eqv i .snd .linv (x , _) = refl ,ₚ squash _ _
```
