<!--
```agda
open import Cat.Diagram.Exponential
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Functor.Adjoint
open import Cat.Cartesian
open import Cat.Prelude

import Cat.CartesianClosed.Lambda as L
import Cat.Reasoning
```
-->

```agda
module Cat.CartesianClosed.Solver
  {o ℓ} {C : Precategory o ℓ} (cart : Cartesian-category C)
  (cc : Cartesian-closed C cart)
  where
```

<!--
```agda
open Cartesian-category cart
open Cartesian-closed cc
private open module L' = L C cart cc

open L' using (Ty ; module Ty ; `_ ; _`×_ ; _`⇒_ ; `⊤) public

private variable
  Γ Δ Θ : Cx
  τ σ ρ : Ty
```
-->

# Solver for Cartesian closed categories

We can write a *solver* for a [[Cartesian closed]] category $\cC$--- a
metaprogram which identifies two morphisms when they differ only by
applications of the CCC laws--- re-using the infrastructure for our
implementation of *normalisation by evaluation* for [[simply-typed
lambda calculus]].

The idea is to write a faithful representation of the way morphisms in a
CCC appear in equational goals (in terms of identities, compositions,
the evaluation morphism, and so on), then define a sound normalisation
function for these. Note that since this is a *meta*program, our syntax
for morphisms does not need to actually respect the laws of a CCC (i.e.
it does not need to be a higher inductive type). It's just a big
*indexed* inductive type with constructors for all the 'primitive'
morphism formers for a [[terminal object]], [[products]], and
[[exponential objects]], with an additional constructor for *morphisms
from the base category*.

```agda
data Mor : Ty → Ty → Type (o ⊔ ℓ) where
  -- Generators:
  `_   : ∀ {x y} → Hom ⟦ x ⟧ᵗ ⟦ y ⟧ᵗ → Mor x y

  -- A CCC is a category:
  `id  : Mor σ σ
  _`∘_ : Mor σ ρ → Mor τ σ → Mor τ ρ

  -- A CCC has a terminal object:
  `!   : Mor τ `⊤

  -- A CCC has products:
  `π₁  : Mor (τ `× σ) τ
  `π₂  : Mor (τ `× σ) σ
  _`,_ : Mor τ σ → Mor τ ρ → Mor τ (σ `× ρ)

  -- A CCC has exponentials:
  `ev  : Mor ((τ `⇒ σ) `× τ) σ
  `ƛ   : Mor (τ `× σ) ρ → Mor τ (σ `⇒ ρ)
```

<!--
```agda
infixr 20 _`∘_
infixr 19 _`,_ _`⊗₁_
infix 25 `_

pattern _`⊗₁_ f g = f `∘ `π₁ `, g `∘ `π₂
pattern `unlambda f = `ev `∘ (f `⊗₁ `id)
```
-->

We can interpret a formal morphism from $\tau$ to $\sigma$ as a map in
$\cC$, and this interpretation *definitionally* sends each constructor
to its corresponding operation. This is the benefit of writing a syntax
for literal morphisms, re-using only the semantics, instead of trying to
reuse also the syntax for lambda terms.

```agda
⟦_⟧ᵐ : Mor τ σ → Hom ⟦ τ ⟧ᵗ ⟦ σ ⟧ᵗ
⟦ ` x     ⟧ᵐ = x
⟦ `id     ⟧ᵐ = id
⟦ m `∘ m₁ ⟧ᵐ = ⟦ m ⟧ᵐ ∘ ⟦ m₁ ⟧ᵐ
⟦ `π₁     ⟧ᵐ = π₁
⟦ `π₂     ⟧ᵐ = π₂
⟦ m `, m₁ ⟧ᵐ = ⟨ ⟦ m ⟧ᵐ , ⟦ m₁ ⟧ᵐ ⟩
⟦ `ev     ⟧ᵐ = ev
⟦ `ƛ m    ⟧ᵐ = ƛ ⟦ m ⟧ᵐ
⟦ `!      ⟧ᵐ = !
```

Formal morphisms from $\tau$ to $\sigma$ then have semantics as *natural
transformations* between the semantic presheaves of types $\tau$ and
$\sigma$ --- we are encoding morphisms as their action by
precomposition. First, we need to handle the case for a generator, a map
coming from $\cC$. While we have a constructor `hom`{.Agda} which
constructs neutrals from generators, this is only at base types, while
here generators can occur at arbitrary types. We thus have to perform
type-directed $\eta$-expansion of the generator. Since the constructor
for generators is a backtick `` `_ ``{.Agda}, we call this semantic
action `tickᵖ`{.Agda}.

```agda
private
  tickᵖ : ∀ {x y h} (m : Hom ⟦ x ⟧ᵗ ⟦ y ⟧ᵗ) → Tyᵖ x Γ h → Tyᵖ y Γ (m ∘ h)
  tickᵖ {x = x} {y = L.`⊤}  m a = lift tt
  tickᵖ {x = x} {y = L.` τ} m a =
    hom {Δ = ∅ , x} (m ∘ π₂) (∅ , reifyᵖ a) ,
    pullr π₂∘⟨⟩ ∙ ap (m ∘_) (reifyᵖ-correct a)
```

Note that the $\eta$-expansion procedure at product and function types
needs to modify the underlying morphism, wrapping them in further CCC
operations. In general, modifying the generators runs the risk of making
our solver useless, since the normal form of a generator could in theory
depend on the details of the evaluation process, but here the
modification is entirely dependent on the *types*, which do not change
under evaluation.

```agda
  tickᵖ {y = τ L.`× σ} m a =
      tyᵖ⟨ pullr refl ⟩ (tickᵖ (π₁ ∘ m) a)
    , tyᵖ⟨ pullr refl ⟩ (tickᵖ (π₂ ∘ m) a)

  tickᵖ {x = x} {y = τ L.`⇒ σ} m a ρ y =
    tyᵖ⟨ pullr (⟨⟩-unique (pulll π₁∘⟨⟩ ∙ extendr π₁∘⟨⟩) (pulll π₂∘⟨⟩ ∙ π₂∘⟨⟩)) ⟩
    (tickᵖ {x = x `× τ} (ev ∘ ⟨ m ∘ π₁ , π₂ ⟩)
      (tyᵖ⟨ sym π₁∘⟨⟩ ⟩ (ren-tyᵖ ρ a) , tyᵖ⟨ sym π₂∘⟨⟩ ⟩ y))
```

The semantics for general formal morphisms are then built in terms of
the existing infrastructure. We handled the case for generators above.

```agda
  morᵖ : ∀ {h} (e : Mor τ σ) (ρ : Tyᵖ τ Γ h) → Tyᵖ σ Γ (⟦ e ⟧ᵐ ∘ h)
  morᵖ (` x) = tickᵖ x
```

The semantic actions of identity and composition are given by the
identity and composition in $\Sets$, i.e. re-using the argument and
sequential evaluation, up to an adjustment in the types:

```agda
  morᵖ `id      ρ = tyᵖ⟨ introl refl ⟩ ρ
  morᵖ (f `∘ g) ρ = tyᵖ⟨ pulll refl ⟩ (morᵖ f (morᵖ g ρ))
```

The semantic interpretation of the terminal object is the unit type, so
there's no choice there. The interpretation for products is, again,
given pointwise by products in $\Sets$. Note that the definition of our
semantic presheaves of types guarantees that the projections are already
type-correct, but the pairing needs slight corrections.

```agda
  morᵖ `!       ρ = lift tt
  morᵖ `π₁      ρ = ρ .fst
  morᵖ `π₂      ρ = ρ .snd
  morᵖ (e `, f) ρ = record
    { fst = tyᵖ⟨ sym (pulll π₁∘⟨⟩) ⟩ (morᵖ e ρ)
    ; snd = tyᵖ⟨ sym (pulll π₂∘⟨⟩) ⟩ (morᵖ f ρ)
    }
```

The semantics of the evaluation morphism and currying are the ones that
need the most change.

```agda
  morᵖ `ev (f , x) = tyᵖ⟨ ap (ev ∘_) (sym (⟨⟩-unique (intror refl) refl)) ⟩
    (f stop x)

  morᵖ {h = h} (`ƛ e) t r {h'} a = tyᵖ⟨ sym p ⟩ (morᵖ e
      ( tyᵖ⟨ sym π₁∘⟨⟩ ⟩ (ren-tyᵖ r t)
      , tyᵖ⟨ sym π₂∘⟨⟩ ⟩ a ))
```

<!--
```agda
    where
    p =
      ev ∘ ⟨ ((ƛ ⟦ e ⟧ᵐ) ∘ h) ∘ ⟦ r ⟧ʳ , h' ⟩
        ≡⟨ ap (ev ∘_) (sym (⟨⟩-unique (pulll π₁∘⟨⟩ ∙ pullr π₁∘⟨⟩ ∙ pulll refl) (pulll π₂∘⟨⟩ ∙ pullr π₂∘⟨⟩ ∙ idl _))) ⟩
      ev ∘ (ƛ ⟦ e ⟧ᵐ ⊗₁ id) ∘ ⟨ h ∘ ⟦ r ⟧ʳ , h' ⟩
        ≡⟨ pulll (commutes _) ⟩
      ⟦ e ⟧ᵐ ∘ ⟨ h ∘ ⟦ r ⟧ʳ , h' ⟩
        ∎
```
-->

We can then use our existing NbE infrastructure, in the form of
`reifyᵖ`{.Agda} and `reflectᵖ`{.Agda}, to get a soundness proof for
free. Note that the normal form of a formal morphism from $\tau$ to
$\sigma$ lives in the context containing only the type $\tau$--- but
this is interpreted as a product with the terminal object, and not as
the literal type, so we need a small correction. This does not affect
the usability of the solver.

```agda
  mor-nf : Mor τ σ → Nf (∅ , τ) σ
  mor-nf m = reifyᵖ (morᵖ m (reflectᵖ (var stop)))

  mor-nf-sound : (m : Mor τ σ) → ⟦ m ⟧ᵐ ≡ ⟦ mor-nf m ⟧ₙ ∘ ⟨ ! , id ⟩
  mor-nf-sound m = sym $
    ⟦ mor-nf m ⟧ₙ ∘ ⟨ ! , id ⟩ ≡⟨ pushl (reifyᵖ-correct (morᵖ m (reflectᵖ (var stop)))) ⟩
    ⟦ m ⟧ᵐ ∘ π₂ ∘ ⟨ ! , id ⟩   ≡⟨ elimr π₂∘⟨⟩ ⟩
    ⟦ m ⟧ᵐ                     ∎

abstract
  solve : (m n : Mor τ σ) → mor-nf m ≡ mor-nf n → ⟦ m ⟧ᵐ ≡ ⟦ n ⟧ᵐ
  solve m n p =
    ⟦ m ⟧ᵐ                     ≡⟨ mor-nf-sound m ⟩
    ⟦ mor-nf m ⟧ₙ ∘ ⟨ ! , id ⟩ ≡⟨ ap₂ _∘_ (ap ⟦_⟧ₙ p) refl ⟩
    ⟦ mor-nf n ⟧ₙ ∘ ⟨ ! , id ⟩ ≡⟨ sym (mor-nf-sound n) ⟩
    ⟦ n ⟧ᵐ                     ∎
```

<!--
```agda
private module _ {W X Y Z} (f : Hom X Y) (g : Hom X Z) (h : Hom W X) where
  `W `X `Y `Z : Ty
  `W = ` W ; `X = ` X ; `Y = ` Y ; `Z = ` Z

  `f : Mor `X `Y
  `f = ` f

  `g : Mor `X `Z
  `g = ` g

  `h : Mor `W `X
  `h = ` h
```
-->

We can then test that the solver subsumes the [solver for products],
handles $\eta$ for the terminal object, and can handle both $\beta$ and
$\eta$ when it comes to the Cartesian closed structure.

[solver for products]: Cat.Diagram.Product.Solver.html

```agda
  test-πη : (pair : Hom X (Y ⊗₀ Z)) → pair ≡ ⟨ π₁ ∘ pair , π₂ ∘ pair ⟩
  test-πη p = solve {τ = `X} {`Y `× `Z} `p (`π₁ `∘ `p `, `π₂ `∘ `p) refl
    where `p = ` p

  test-πβ₁ : π₁ ∘ ⟨ f , g ⟩ ≡ f
  test-πβ₁ = solve (`π₁ `∘ (`f `, `g)) `f refl

  test-πβ₂ : π₂ ∘ ⟨ f , g ⟩ ≡ g
  test-πβ₂ = solve (`π₂ `∘ (`f `, `g)) `g refl

  test-⟨⟩∘ : ⟨ f ∘ h , g ∘ h ⟩ ≡ ⟨ f , g ⟩ ∘ h
  test-⟨⟩∘ = solve (`f `∘ `h `, `g `∘ `h) ((`f `, `g) `∘ `h) refl

  test-ƛβ : (f : Hom X [ Y , Z ]) → f ≡ ƛ (unlambda f)
  test-ƛβ fn = solve `fn (`ƛ (`unlambda `fn)) refl
    where `fn : Mor `X (`Y `⇒ `Z) ; `fn = ` fn

  test-ƛh : (o : Hom (X ⊗₀ Y) Z) → o ≡ unlambda (ƛ o)
  test-ƛh o = solve `o (`unlambda (`ƛ `o)) refl
    where `o : Mor (`X `× `Y) `Z ; `o = ` o

  test-!η : (f g : Hom X top) → f ≡ g
  test-!η f g = solve {τ = `X} {σ = `⊤} (` f) (` g) refl
```
