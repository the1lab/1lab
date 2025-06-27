<!--
```agda
open import 1Lab.Path.Reasoning

open import Cat.Functor.Properties
open import Cat.Prelude

import Cat.Functor.Reasoning.FullyFaithful as Ffr
import Cat.Reasoning
```
-->

```agda
module Cat.Univalent.Rezk.HIT {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
open Cat.Reasoning C

private
  module P = Precategory
  variable x y z : ⌞ C ⌟
```
-->

# Higher inductive Rezk completions

We can define the [[Rezk completion]] of a [[precategory]] $\cC$
directly as a higher inductive type, without passing through
[replacement]. Importantly, under this construction, the resulting
universal functor $\cC \to \widehat{\cC}$ becomes *definitionally* fully
faithful.

[replacement]: Data.Image.html

The type of objects of $\widehat{\cC}$ looks a lot like the
[[delooping]] of a group, but with an inclusion $\cC \to \widehat{\cC}$
rather than a single basepoint: indeed, we can think of it as delooping
all the [[automorphism groups]] of $\cC$ at once. Completely
analogously, we have a constructor turning [[isomorphisms]] in $\cC$
into paths in $\widehat{\cC}$; and we have a generating triangle saying
that this constructor respects composition, filling the diagram

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  {\rm{inc}\ x} \&\& {\rm{inc}\ y} \\
  \\
  \&\& {\rm{inc}\ z\text{.}}
  \arrow["{\rm{glue}\ f}", equals, from=1-1, to=1-3]
  \arrow[""{name=0, anchor=center, inner sep=0}, "{\rm{glue}\ (g \circ f)}"', equals, from=1-1, to=3-3]
  \arrow["{\rm{glue}\ g}", equals, from=1-3, to=3-3]
  \arrow["{\rm{glue}^T\ f\ g}"{description}, draw=none, from=0, to=1-3]
\end{tikzcd}\]
~~~

```agda
data C^ : Type (o ⊔ ℓ) where
  inc  : ⌞ C ⌟ → C^
  glue : ∀ {x y} → x ≅ y → inc x ≡ inc y
  glueᵀ
    : ∀ {x y z} (f : x ≅ y) (g : y ≅ z)
    → Triangle (glue f) (glue (g ∘Iso f)) (glue g)
  squash : is-groupoid C^
```

Note that, as in the case for simple deloopings, this generating
triangle is sufficient to ensure that `glue`{.Agda} is functorial.

```agda
glue-∘
  : (e : x ≅ y) (e' : y ≅ z)
  → Path (Path C^ (inc x) (inc z)) (glue e ∙ glue e') (glue (e' ∘Iso e))
glue-∘ e e' = sym (triangle→commutes (glueᵀ e e'))

glue-id : Path (Path C^ (inc x) (inc x)) (glue id-iso) refl
glue-id =
  glue id-iso                                     ≡⟨ ∙-intror (∙-invr _) ⟩
  glue id-iso ∙ glue id-iso ∙ sym (glue id-iso)   ≡⟨ ∙-pulll (glue-∘ _ _ ∙ ap C^.glue (ext (idl _))) ⟩
  glue id-iso ∙ sym (glue id-iso)                 ≡⟨ ∙-invr _ ⟩
  refl                                            ∎
```

We will need an elimination principle for `C^`{.Agda} into [[sets]],
saying that it suffices to handle the point inclusions and the
generating paths; the generating triangle is handled automatically, as
is the truncation. Of course, we can also eliminate `C^`{.Agda} into
[[propositions]], in which case the generating paths are *also* handled
automatically.

```agda
C^-elim-set
  : ∀ {ℓ} {P : C^ → Type ℓ} ⦃ _ : ∀ {x} → H-Level (P x) 2 ⦄
  → (pi : ∀ x → P (inc x))
  → (pg : ∀ {x y} (e : x ≅ y) → PathP (λ i → P (glue e i)) (pi x) (pi y))
  → ∀ x → P x
C^-elim-set pi pg (inc x) = pi x
C^-elim-set pi pg (glue x i) = pg x i
C^-elim-set {P = P} pi pg (glueᵀ {x} f g i j) =
  is-set→squarep (λ i j → hlevel {T = P (glueᵀ f g i j)} 2)
    (λ i → pi x) (λ i → pg f i) (λ i → pg (g ∘Iso f) i) (λ i → pg g i) i j
C^-elim-set {P = P} pi pg (squash x y p q α β i j k) =
  is-hlevel→is-hlevel-dep 2 (λ x → is-hlevel-suc 2 (hlevel {T = P x} 2))
    (go x) (go y) (λ i → go (p i)) (λ i → go (q i))
    (λ i j → go (α i j)) (λ i j → go (β i j)) (squash x y p q α β) i j k
  where go = C^-elim-set {P = P} pi pg
```

<!--
```agda
abstract
  C^-elim-prop
    : ∀ {ℓ} {P : C^ → Type ℓ} ⦃ _ : ∀ {x} → H-Level (P x) 1 ⦄
    → (∀ x → P (inc x))
    → ∀ x → P x
  C^-elim-prop pi = C^-elim-set ⦃ hlevel-instance (is-prop→is-set (hlevel 1)) ⦄
      pi (λ e → prop!)

instance
  H-Level-C^ : ∀ {n} → H-Level C^ (3 + n)
  H-Level-C^ = basic-instance 3 squash

  Inductive-C^
    : ∀ {ℓ ℓm} {P : C^ → Type ℓ} ⦃ i : Inductive (∀ x → P (inc x)) ℓm ⦄
    → ⦃ _ : ∀ {x} → H-Level (P x) 1 ⦄
    → Inductive (∀ x → P x) ℓm
  Inductive-C^ ⦃ i ⦄ = record
    { methods = i .Inductive.methods
    ; from    = λ f → C^-elim-prop (i .Inductive.from f)
    }
```
-->

## Defining spans over `C^`

We now turn to the problem of defining the $\hom$-family
$\widehat{\cC}(x, y)$. This turns out to have a lot of "cases", but we
can break them down intuitively as follows: to define a function
$\widehat{f} : \widehat{\cC} \to \widehat{\cC} \to P$, where $P$ is a
[[groupoid]], we can start by giving a function $f : \cC \to \cC \to P$;

```agda
record C^-corr {ℓ'} (P : Type ℓ') : Type (o ⊔ ℓ ⊔ ℓ') where
  field
    has-is-groupoid : is-groupoid P

    base : ⌞ C ⌟ → ⌞ C ⌟ → P
```

Then, we must give actions of the isomorphisms $x \cong_\cC x'$ on both
the left and the right of $f$, making it into a sort of "profunctor";
and, correspondingly, these actions must be "profunctorial". In
particular, they should respect composition and commute past each other,
which we can state concisely in terms of triangles and squares.

```agda
    lmap : ∀ {x x' y} (e : x ≅ x') → base x y ≡ base x' y
    rmap : ∀ {x y y'} (e : y ≅ y') → base x y ≡ base x y'

    lcoh : ∀ {x x' x'' y} (e : x ≅ x') (e' : x' ≅ x'')
         → Triangle (lmap {y = y} e) (lmap (e' ∘Iso e)) (lmap e')

    rcoh : ∀ {x y y' y''} (e : y ≅ y') (e' : y' ≅ y'')
         → Triangle (rmap {x = x} e) (rmap (e' ∘Iso e)) (rmap e')

    comm : ∀ {x x' y y'} (e : x ≅ x') (e' : y ≅ y')
         → Square (rmap e) (lmap e') (lmap e') (rmap e)
```

<details>
<summary>This is sufficient to discharge all the cases when writing a
binary function from $\widehat{\cC}$ into a groupoid; we leave the
formalisation in this `<details>`{.html} block because it is rather
fiddly.</summary>

```agda
  private
    instance
      _ : H-Level P 3
      _ = hlevel-instance has-is-groupoid

    go₀ : (x : ⌞ C ⌟) (y : C^) → P
    go₀ ξ (inc x)              = base ξ x
    go₀ ξ (glue x i)           = rmap {ξ} x i
    go₀ ξ (glueᵀ f g i j)      = rcoh {ξ} f g i j
    go₀ ξ (squash x y p q α β i j k) =
      let go = go₀ ξ in is-hlevel→is-hlevel-dep 2 (λ _ → hlevel 3)
        (go x) (go y) (λ i → go (p i)) (λ i → go (q i))
        (λ i j → go (α i j)) (λ i j → go (β i j))
        (squash x y p q α β) i j k

    lmap' : ∀ {x x'} (e : x ≅ x') → go₀ x ≡ go₀ x'
    lmap' e = funextP $ C^-elim-set (λ _ → lmap e) λ e' → comm e' e

    lcoh'
      : ∀ {w x y : ⌞ C ⌟} (e : w ≅ x) (e' : x ≅ y)
      → Triangle (lmap' e) (lmap' (e' ∘Iso e)) (lmap' e')
    lcoh' e e' = funext-square $ C^-elim-prop λ x → lcoh e e'

  C^-rec₂ : (x y : C^) → P
  C^-rec₂ (inc x)          z = go₀ x z
  C^-rec₂ (glue x i)       z = lmap' x i z
  C^-rec₂ (glueᵀ x y i j)  z = lcoh' x y i j z
  C^-rec₂ (squash x y p q α β i j k) z =
    let
      go : C^ → P
      go x = C^-rec₂ x z
    in is-hlevel→is-hlevel-dep 2 (λ _ → hlevel 3)
      (go x) (go y) (λ i → go (p i)) (λ i → go (q i))
      (λ i j → go (α i j)) (λ i j → go (β i j))
      (squash x y p q α β) i j k
```

</details>

<!--
```agda
open C^-corr
private
```
-->

Since $\hom_\cC$ is already a profunctor over $\cC$, we can show
straightforwardly that it extends to a binary type family
$\widehat{\hom}$ over $\widehat{\cC}$.

```agda
  hom^ : C^ → C^ → Type ℓ
  hom^ x y = ⌞ C^-rec₂ methods x y ⌟ where
    methods : C^-corr (Set ℓ)
    methods .has-is-groupoid = hlevel 3
    methods .base x y = el! (Hom x y)

    methods .lmap e = n-ua (dom-iso→hom-equiv e)
    methods .rmap e = n-ua (cod-iso→hom-equiv e)

    methods .lcoh e e' = n-ua-triangle (ext λ h → assoc _ _ _)
    methods .rcoh e e' = n-ua-triangle (ext λ h → sym (assoc _ _ _))
    methods .comm e e' = n-ua-square   (ext λ h → sym (assoc _ _ _))
```

<!--
```agda
-- To make sure that composition in Rzk is injective in the objects, we
-- wrap the hom^ family defined above in a record.

record Hom^ (x y : C^) : Type ℓ where
  constructor lift
  field
    lower : hom^ x y

open Hom^ public

instance
  H-Level-Hom^ : ∀ {x y n} → H-Level (Hom^ x y) (2 + n)
  H-Level-Hom^ = basic-instance 2 (Iso→is-hlevel 2 (Hom^.lower , (iso lift (λ x → refl) (λ x → refl))) (hlevel 2))

  Inductive-Hom^
    : ∀ {x y ℓ ℓm} {P : Hom^ x y → Type ℓ} ⦃ i : Inductive (∀ h → P (lift h)) ℓm ⦄
    → Inductive (∀ x → P x) ℓm
  Inductive-Hom^ ⦃ i ⦄ = record { methods = i .Inductive.methods ; from = λ { m (lift x) → i .Inductive.from m x } }

private
  lifthom^ : ∀ {x y} → hom^ x y → Hom^ x y
  lifthom^ = lift
```
-->

## Making a category

Since our $\widehat{\hom}$-family is valued in sets, we can use the
eliminator defined above to construct the identity morphisms and the
composition operation by $\widehat{\cC}$-recursion. These will consist
of lifting the corresponding operation from $\cC$ and then showing that
they respect the action of `glue`{.Agda} on `hom^`{.Agda}, which we have
defined to be pre- and post-composition with the given isomorphism.
Therefore, while there is a lot of code motion to put these together,
they are conceptually very simple.

For a worked-out example, the necessary coherence for lifting the
identity morphisms from $\cC$ to $\widehat{\cC}$ asks simply that if $j
: x \cong y$, then we have $j \circ \id \circ j\inv = \id$, which is a short
calculation.

```agda
  id^ : ∀ x → hom^ x x
  id^ = C^-elim-set (λ _ → id) coh where abstract
    coh : ∀ {x y} (j : x ≅ y) → PathP (λ i → hom^ (glue j i) (glue j i)) id id
    coh z = path→ua-pathp _ $
      z .to ∘ id ∘ z .from  ≡⟨ ap (z .to ∘_) (idl _) ⟩
      z .to ∘ z .from       ≡⟨ z .invl ⟩
      id                    ∎
```

<details>
<summary>Lifting the composition operation is similar, but more
involved, since we now have to do recursion on `C^`{.Agda}
*thrice*.</summary>

```agda
  ∘^ : ∀ x y z → hom^ y z → hom^ x y → hom^ x z
  ∘^ = C^-elim-set f₁ coh₂ where mutual
    f₀ : ∀ x y z → hom^ (inc y) z → hom^ (inc x) (inc y) → hom^ (inc x) z
    f₀ x y = C^-elim-set (λ z → _∘_) (coh₀ x y)

    f₁ : ∀ x (y z : C^) → hom^ y z → hom^ (inc x) y → hom^ (inc x) z
    f₁ x = C^-elim-set (f₀ x) (coh₁ x)

    abstract
      coh₀ : ∀ x y {z z'} (j : z ≅ z') → PathP (λ i → hom^ (inc y) (glue j i) → hom^ (inc x) (inc y) → hom^ (inc x) (glue j i)) _∘_ _∘_
      coh₀ x y j = ua→ (λ f → funextP λ g → path→ua-pathp _ (assoc _ _ _))

      coh₁ : ∀ x {y z} (j : y ≅ z) → PathP (λ i → (y : C^) → hom^ (glue j i) y → hom^ (inc x) (glue j i) → hom^ (inc x) y) (f₀ x y) (f₀ x z)
      coh₁ x j = funextP (C^-elim-prop (λ z → ua→ λ h → ua→ λ i → ap (h ∘_) (insertl (j .invr)) ∙ pulll refl))

      coh₂ : ∀ {x y} (j : x ≅ y) → PathP (λ i → (y z : C^) → hom^ y z → hom^ (glue j i) y → hom^ (glue j i) z) (f₁ x) (f₁ y)
      coh₂ j = funextP $ elim! λ y → funextP $ elim! λ z → funextP λ f → ua→ λ g → path→ua-pathp _ (sym (assoc _ _ _))
```

</details>

To show that this forms a precategory, it suffices to lift the
corresponding *proofs* also from $\cC$. Since we're showing a
proposition, this is very straightforward: it's just some un/wrapping.

```agda
Rzk : Precategory (o ⊔ ℓ) ℓ
Rzk .P.Ob  = C^
Rzk .P.Hom x y = Hom^ x y
Rzk .P.Hom-set x y = hlevel 2
Rzk .P.id  {x}             = lift (id^ x)
Rzk .P._∘_ {w} {x} {y} f g = lift (∘^ w x y (f .lower) (g .lower))

Rzk .P.idr {x} {y} (lift f) = ap lift (idr^ x y f) where abstract
  idr^ : ∀ x y (f : hom^ x y) → ∘^ x x y f (id^ x) ≡ f
  idr^ = elim! λ x y f → idr f

Rzk .P.idl {x} {y} (lift f) = ap lift (idl^ x y f) where abstract
  idl^ : ∀ x y (f : hom^ x y) → ∘^ x y y (id^ y) f ≡ f
  idl^ = elim! λ x y f → idl f

Rzk .P.assoc {w} {x} {y} {z} (lift f) (lift g) (lift h) =
  ap lift (assoc^ w x y z f g h) where abstract
  assoc^ : ∀ w x y z (f : hom^ y z) (g : hom^ x y) (h : hom^ w x)
         → ∘^ w y z f (∘^ w x y g h) ≡ ∘^ w x z (∘^ x y z f g) h
  assoc^ = elim! λ w x y z f g h → assoc f g h
```

<!--
```agda
module Rzk = Cat.Reasoning Rzk
```
-->

We can give the Rezk completion functor.

```agda
complete : Functor C Rzk
complete .Functor.F₀      = inc
complete .Functor.F₁ f    = lift f
complete .Functor.F-id    = refl
complete .Functor.F-∘ f g = refl

complete-is-ff : is-fully-faithful complete
complete-is-ff = is-iso→is-equiv (iso Hom^.lower (λ x → refl) λ x → refl)

complete-is-eso : is-eso complete
complete-is-eso = elim! λ x → inc (x , Rzk.id-iso)
```

<!--
```agda
module hat = Ffr complete complete-is-ff
```
-->

## Univalence of the Rezk completion

To show that $\widehat{\cC}$ is [[univalent|univalent category]], we do
one last monster induction, to show that, for a fixed $a :
\widehat{\cC}$, the space of "isomorphs of $a$" is contractible. This
automatically handles one coherence, since contractibility is a
proposition; however, when actually lifting the `glue`{.Agda}
constructor, we do still have one coherence to show.

```agda
to-path^ : (a : C^) → is-contr (Σ[ b ∈ C^ ] a Rzk.≅ b)
to-path^ = C^-elim-set
  (λ x → record { paths = λ (b , e) → wrap x b e })
  (λ e → prop!)
  where module _ (a : ⌞ C ⌟) where
    T : C^ → Type _
    T x = (e : inc a Rzk.≅ x)
        → Path (Σ[ b ∈ C^ ] inc a Rzk.≅ b) (inc a , Rzk.id-iso) (x , e)

    glue' : (x : ⌞ C ⌟) → T (inc x)
    glue' x e = glue (hat.iso.from e) ,ₚ
      Rzk.≅-pathp _ _ (apd (λ i → lifthom^) (path→ua-pathp _ (idr _)))
```

However, this coherence is essentially the generating triangle
`glueᵀ`{.Agda}, and so the proof goes through without much stress.

```agda
    coh : {x y : Ob} (e : x ≅ y)
        → PathP (λ i → T (glue e i)) (glue' x) (glue' y)
    coh e = funext-dep λ {x₀} {x₁} α →
      let
        open Rzk using (to)

        α' : glue (e ∘Iso hat.iso.from x₀) ≡ glue (hat.iso.from x₁)
        α' = ap C^.glue (ext (ua-pathp→path _ (apd (λ _ x → x .to .lower) α)))
      in Σ-set-square (λ _ → hlevel 2) $ glueᵀ (hat.iso.from x₀) e ▷ α'

    wrap : ∀ b → T b
    wrap = C^-elim-set glue' coh

Rzk-is-category : is-category Rzk
Rzk-is-category = contr→identity-system (λ {a} → to-path^ a)
```
