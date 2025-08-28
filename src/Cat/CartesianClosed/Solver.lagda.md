<!--
```agda
open import Cat.CartesianClosed.Free.Signature using (module types)
open import Cat.Diagram.Exponential
open import Cat.Cartesian
open import Cat.Prelude

import Cat.Functor.Bifunctor as Bifunctor
```
-->

```agda
module Cat.CartesianClosed.Solver
```

# Solver for Cartesian closed categories

<!--
```agda
  {o ℓ} {C : Precategory o ℓ} (cart : Cartesian-category C) (cc : Cartesian-closed C cart)
        where

open Cartesian-category cart
open Cartesian-closed cc
open types Ob public
```
-->

We can write a *solver* for a [[Cartesian closed]] category $\cC$ --- a
metaprogram which identifies two morphisms when they differ only by
applications of the CCC laws --- by re-using the idea for our
implementation of *normalisation by evaluation* for [[free Cartesian
closed categories]]: in order to identify two morphisms in $\cC$, it
suffices to identify their "quoted" versions in the free CCC on $\cC$,
which we can do automatically by normalising them.

The reason we don't directly re-use the *implementation* is that the
underlying graph of an arbitrary CCC does not form a
[[$\lambda$-signature]] unless the category is [[strict|strict category]],
which is too limiting an assumption. In turn, the requirement that the
objects form a set is necessary to obtain proper *presheaves* of normals
and neutrals. Instead, this module takes a slightly "wilder" approach,
omitting a lot of unnecessary coherence. We also work with an
*unquotiented* representation of morphisms.

First, recall the definition of [[simple types]]: they are generated from
the objects of $\cC$ by freely adding product types, function types, and
a unit type. We define contexts as lists of simple types.

```agda
data Cx : Type o where
  ∅   : Cx
  _,_ : Cx → Ty → Cx
```

<!--
```agda
private variable
  Γ Δ Θ : Cx
  τ σ ρ : Ty
```
-->

Using the Cartesian closed structure of $\cC$, we can interpret types
and contexts in terms of the structural morphisms: for
example, the empty context is interpreted by the terminal object.

<!--
```agda
⟦_⟧ᵗ : Ty → Ob
⟦_⟧ᶜ : Cx → Ob
```
-->

```agda
⟦ X `× Y ⟧ᵗ = ⟦ X ⟧ᵗ ⊗₀ ⟦ Y ⟧ᵗ
⟦ X `⇒ Y ⟧ᵗ = [ ⟦ X ⟧ᵗ , ⟦ Y ⟧ᵗ ]
⟦ `⊤  ⟧ᵗ    = top
⟦ ` X ⟧ᵗ    = X

⟦ Γ , τ ⟧ᶜ = ⟦ Γ ⟧ᶜ ⊗₀ ⟦ τ ⟧ᵗ
⟦ ∅ ⟧ᶜ     = top
```

The idea is then to write a faithful representation of the way morphisms
in a CCC appear in equational goals (in terms of identities, compositions,
the evaluation morphism, and so on), then define a sound normalisation
function for these. Note that since this is a *meta*program, our syntax
for morphisms does not need to actually respect the laws of a CCC (i.e.
it does not need to be a higher inductive type). It's just a big
*indexed* inductive type with constructors for all the "primitive"
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
to its corresponding operation.

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

<details>
<summary>
The bulk of this module is the implementation of normalisation by
evaluation for the representation of morphisms above. We refer the
reader to the same construction for [[free Cartesian closed categories]]
over a $\lambda$-signature for more details.
</summary>

```agda
data Var : Cx → Ty → Type o where
  stop : Var (Γ , τ) τ
  pop  : Var Γ τ → Var (Γ , σ) τ

⟦_⟧ⁿ : Var Γ τ → Hom ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ
⟦ stop ⟧ⁿ  = π₂
⟦ pop x ⟧ⁿ = ⟦ x ⟧ⁿ ∘ π₁

data Ren : Cx → Cx → Type (o ⊔ ℓ) where
  stop : Ren Γ Γ
  drop : Ren Γ Δ → Ren (Γ , τ) Δ
  keep : Ren Γ Δ → Ren (Γ , τ) (Δ , τ)

_∘ʳ_ : ∀ {Γ Δ Θ} → Ren Γ Δ → Ren Δ Θ → Ren Γ Θ
stop   ∘ʳ ρ      = ρ
drop σ ∘ʳ ρ      = drop (σ ∘ʳ ρ)
keep σ ∘ʳ stop   = keep σ
keep σ ∘ʳ drop ρ = drop (σ ∘ʳ ρ)
keep σ ∘ʳ keep ρ = keep (σ ∘ʳ ρ)

ren-var : ∀ {Γ Δ τ} → Ren Γ Δ → Var Δ τ → Var Γ τ
ren-var stop     v       = v
ren-var (drop σ) v       = pop (ren-var σ v)
ren-var (keep σ) stop    = stop
ren-var (keep σ) (pop v) = pop (ren-var σ v)

⟦_⟧ʳ : Ren Γ Δ → Hom ⟦ Γ ⟧ᶜ ⟦ Δ ⟧ᶜ
⟦ stop   ⟧ʳ = id
⟦ drop r ⟧ʳ = ⟦ r ⟧ʳ ∘ π₁
⟦ keep r ⟧ʳ = ⟦ r ⟧ʳ ⊗₁ id

data Nf           : Cx → Ty → Type (o ⊔ ℓ)
data Ne           : Cx → Ty → Type (o ⊔ ℓ)
data Sub (Γ : Cx) : Cx → Type (o ⊔ ℓ)

data Nf where
  lam  : Nf (Γ , τ) σ       → Nf Γ (τ `⇒ σ)
  pair : Nf Γ τ → Nf Γ σ    → Nf Γ (τ `× σ)
  unit :                      Nf Γ `⊤
  ne   : ∀ {x} → Ne Γ (` x) → Nf Γ (` x)

data Ne where
  var  : Var Γ τ → Ne Γ τ
  app  : Ne Γ (τ `⇒ σ) → Nf Γ τ → Ne Γ σ
  fstₙ : Ne Γ (τ `× σ) → Ne Γ τ
  sndₙ : Ne Γ (τ `× σ) → Ne Γ σ
  hom  : ∀ {Δ a} → Hom ⟦ Δ ⟧ᶜ a → Sub Γ Δ → Ne Γ (` a)

data Sub Γ where
  ∅   : Sub Γ ∅
  _,_ : Sub Γ Δ → Nf Γ τ → Sub Γ (Δ , τ)

ren-ne  : ∀ {Γ Δ τ} → Ren Δ Γ → Ne  Γ τ → Ne  Δ τ
ren-nf  : ∀ {Γ Δ τ} → Ren Δ Γ → Nf  Γ τ → Nf  Δ τ
ren-sub : ∀ {Γ Δ Θ} → Ren Δ Γ → Sub Γ Θ → Sub Δ Θ

ren-ne σ (hom h a) = hom h (ren-sub σ a)

ren-ne σ (var v)   = var  (ren-var σ v)
ren-ne σ (app f a) = app  (ren-ne σ f) (ren-nf σ a)
ren-ne σ (fstₙ a)  = fstₙ (ren-ne σ a)
ren-ne σ (sndₙ a)  = sndₙ (ren-ne σ a)

ren-nf σ (lam n)    = lam  (ren-nf (keep σ) n)
ren-nf σ (pair a b) = pair (ren-nf σ a) (ren-nf σ b)
ren-nf σ (ne x)     = ne   (ren-ne σ x)
ren-nf σ unit       = unit

ren-sub ρ ∅       = ∅
ren-sub ρ (σ , x) = ren-sub ρ σ , ren-nf ρ x

⟦_⟧ₙ  : Nf  Γ τ → Hom ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ
⟦_⟧ₛ  : Ne  Γ τ → Hom ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ
⟦_⟧ᵣ  : Sub Γ Δ → Hom ⟦ Γ ⟧ᶜ ⟦ Δ ⟧ᶜ

⟦ lam h    ⟧ₙ = ƛ ⟦ h ⟧ₙ
⟦ pair a b ⟧ₙ = ⟨ ⟦ a ⟧ₙ , ⟦ b ⟧ₙ ⟩
⟦ ne x     ⟧ₙ = ⟦ x ⟧ₛ
⟦ unit     ⟧ₙ = !

⟦ var x   ⟧ₛ = ⟦ x ⟧ⁿ
⟦ app f x ⟧ₛ = ev ∘ ⟨ ⟦ f ⟧ₛ , ⟦ x ⟧ₙ ⟩
⟦ fstₙ h  ⟧ₛ = π₁ ∘ ⟦ h ⟧ₛ
⟦ sndₙ h  ⟧ₛ = π₂ ∘ ⟦ h ⟧ₛ
⟦ hom h a ⟧ₛ = h ∘ ⟦ a ⟧ᵣ

⟦ ∅     ⟧ᵣ = !
⟦ σ , n ⟧ᵣ = ⟨ ⟦ σ ⟧ᵣ , ⟦ n ⟧ₙ ⟩

⟦⟧-∘ʳ   : (ρ : Ren Γ Δ) (σ : Ren Δ Θ) → ⟦ ρ ∘ʳ σ ⟧ʳ ≡ ⟦ σ ⟧ʳ ∘ ⟦ ρ ⟧ʳ

ren-⟦⟧ⁿ : (ρ : Ren Δ Γ) (v : Var Γ τ) → ⟦ ren-var ρ v ⟧ⁿ ≡ ⟦ v ⟧ⁿ ∘ ⟦ ρ ⟧ʳ
ren-⟦⟧ₛ : (ρ : Ren Δ Γ) (t : Ne Γ τ)  → ⟦ ren-ne ρ t  ⟧ₛ ≡ ⟦ t ⟧ₛ ∘ ⟦ ρ ⟧ʳ
ren-⟦⟧ₙ : (ρ : Ren Δ Γ) (t : Nf Γ τ)  → ⟦ ren-nf ρ t  ⟧ₙ ≡ ⟦ t ⟧ₙ ∘ ⟦ ρ ⟧ʳ
ren-⟦⟧ᵣ : (ρ : Ren Δ Γ) (σ : Sub Γ Θ) → ⟦ ren-sub ρ σ ⟧ᵣ ≡ ⟦ σ ⟧ᵣ ∘ ⟦ ρ ⟧ʳ

⟦⟧-∘ʳ stop σ = intror refl
⟦⟧-∘ʳ (drop ρ) σ = pushl (⟦⟧-∘ʳ ρ σ)
⟦⟧-∘ʳ (keep ρ) stop = introl refl
⟦⟧-∘ʳ (keep ρ) (drop σ) = pushl (⟦⟧-∘ʳ ρ σ) ∙ sym (pullr π₁∘⟨⟩)
⟦⟧-∘ʳ (keep ρ) (keep σ) = sym $ ⟨⟩-unique
  (pulll π₁∘⟨⟩ ∙ pullr π₁∘⟨⟩ ∙ pulll (sym (⟦⟧-∘ʳ ρ σ)))
  (pulll π₂∘⟨⟩ ∙ pullr π₂∘⟨⟩ ∙ idl _)

ren-⟦⟧ⁿ stop v           = intror refl
ren-⟦⟧ⁿ (drop ρ) v       = pushl (ren-⟦⟧ⁿ ρ v)
ren-⟦⟧ⁿ (keep ρ) stop    = sym (π₂∘⟨⟩ ∙ idl _)
ren-⟦⟧ⁿ (keep ρ) (pop v) = pushl (ren-⟦⟧ⁿ ρ v) ∙ sym (pullr π₁∘⟨⟩)

ren-⟦⟧ₛ ρ (var x) = ren-⟦⟧ⁿ ρ x
ren-⟦⟧ₛ ρ (app f x) = ap₂ _∘_ refl
  (ap₂ ⟨_,_⟩ (ren-⟦⟧ₛ ρ f) (ren-⟦⟧ₙ ρ x) ∙ sym (⟨⟩∘ _))
  ∙ pulll refl
ren-⟦⟧ₛ ρ (fstₙ t) = pushr (ren-⟦⟧ₛ ρ t)
ren-⟦⟧ₛ ρ (sndₙ t) = pushr (ren-⟦⟧ₛ ρ t)
ren-⟦⟧ₛ ρ (hom x a) = pushr (ren-⟦⟧ᵣ ρ a)

ren-⟦⟧ₙ ρ (lam t) =
    ap ƛ (ren-⟦⟧ₙ (keep ρ) t)
  ∙ sym (unique _ (ap₂ _∘_ refl rem₁ ∙ pulll (commutes ⟦ t ⟧ₙ)))
  where
  rem₁ : (⟦ lam t ⟧ₙ ∘ ⟦ ρ ⟧ʳ) ⊗₁ id ≡ (⟦ lam t ⟧ₙ ⊗₁ id) ∘ ⟦ ρ ⟧ʳ ⊗₁ id
  rem₁ = Bifunctor.first∘first ×-functor

ren-⟦⟧ₙ ρ (pair a b) = ap₂ ⟨_,_⟩ (ren-⟦⟧ₙ ρ a) (ren-⟦⟧ₙ ρ b) ∙ sym (⟨⟩∘ _)
ren-⟦⟧ₙ ρ (ne x) = ren-⟦⟧ₛ ρ x
ren-⟦⟧ₙ ρ unit   = !-unique _

ren-⟦⟧ᵣ ρ ∅       = !-unique _
ren-⟦⟧ᵣ ρ (σ , n) = ap₂ ⟨_,_⟩ (ren-⟦⟧ᵣ ρ σ) (ren-⟦⟧ₙ ρ n) ∙ sym (⟨⟩∘ _)

Tyᵖ : (τ : Ty) (Γ : Cx) → Hom ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ → Type (o ⊔ ℓ)
Tyᵖ (τ `× σ) Γ h = Tyᵖ τ Γ (π₁ ∘ h) × Tyᵖ σ Γ (π₂ ∘ h)
Tyᵖ `⊤ Γ h = Lift _ ⊤
Tyᵖ (τ `⇒ σ) Γ h =
  ∀ {Δ} (ρ : Ren Δ Γ) {a}
  → Tyᵖ τ Δ a
  → Tyᵖ σ Δ (ev ∘ ⟨ h ∘ ⟦ ρ ⟧ʳ , a ⟩)
Tyᵖ (` x)    Γ h = Σ (Ne Γ (` x)) λ n → ⟦ n ⟧ₛ ≡ h

data Subᵖ : ∀ Γ Δ → Hom ⟦ Δ ⟧ᶜ ⟦ Γ ⟧ᶜ → Type (o ⊔ ℓ) where
  ∅   : ∀ {i} → Subᵖ ∅ Δ i
  _,_ : ∀ {h} → Subᵖ Γ Δ (π₁ ∘ h) → Tyᵖ σ Δ (π₂ ∘ h) → Subᵖ (Γ , σ) Δ h

tyᵖ⟨_⟩ : ∀ {τ Γ h h'} → h ≡ h' → Tyᵖ τ Γ h → Tyᵖ τ Γ h'
tyᵖ⟨_⟩ {τ `× σ} p (a , b)   = tyᵖ⟨ ap (π₁ ∘_) p ⟩ a , tyᵖ⟨ ap (π₂ ∘_) p ⟩ b
tyᵖ⟨_⟩ {τ `⇒ σ} p ν ρ x     = tyᵖ⟨ ap (λ e → ev ∘ ⟨ e ∘ ⟦ ρ ⟧ʳ , _ ⟩) p ⟩ (ν ρ x)
tyᵖ⟨_⟩ {` x} p (n , q) .fst = n
tyᵖ⟨_⟩ {` x} p (n , q) .snd = q ∙ p
tyᵖ⟨_⟩ {`⊤}  p (lift tt)    = lift tt

subᵖ⟨_⟩ : ∀ {Γ Δ h h'} → h ≡ h' → Subᵖ Γ Δ h → Subᵖ Γ Δ h'
subᵖ⟨_⟩ p ∅       = ∅
subᵖ⟨_⟩ p (r , x) = subᵖ⟨ ap (π₁ ∘_) p ⟩ r , tyᵖ⟨ ap (π₂ ∘_) p ⟩ x

ren-tyᵖ  : ∀ {Δ Γ τ m} (ρ : Ren Δ Γ) → Tyᵖ τ Γ m  → Tyᵖ  τ Δ (m ∘ ⟦ ρ ⟧ʳ)
ren-subᵖ : ∀ {Δ Γ Θ m} (ρ : Ren Θ Δ) → Subᵖ Γ Δ m → Subᵖ Γ Θ (m ∘ ⟦ ρ ⟧ʳ)

ren-tyᵖ {τ = τ `× σ} r (a , b)   =
    tyᵖ⟨ sym (assoc _ _ _) ⟩ (ren-tyᵖ r a)
  , tyᵖ⟨ sym (assoc _ _ _) ⟩ (ren-tyᵖ r b)
ren-tyᵖ {τ = τ `⇒ σ} r t {Θ} ρ {α} a =
  tyᵖ⟨ ap (λ e → ev ∘ ⟨ e , α ⟩) (pushr (⟦⟧-∘ʳ ρ r)) ⟩ (t (ρ ∘ʳ r) a)
ren-tyᵖ {τ = ` x} r (f , p) = ren-ne r f , ren-⟦⟧ₛ r f ∙ ap₂ _∘_ p refl
ren-tyᵖ {τ = `⊤} r (lift tt) = lift tt

ren-subᵖ r ∅       = ∅
ren-subᵖ r (c , x) =
    subᵖ⟨ sym (assoc _ _ _) ⟩ (ren-subᵖ r c)
  , tyᵖ⟨ sym (assoc _ _ _) ⟩ (ren-tyᵖ r x)

reifyᵖ         : ∀ {h}                 → Tyᵖ τ Γ h → Nf Γ τ
reflectᵖ       : (n : Ne Γ τ)          → Tyᵖ τ Γ ⟦ n ⟧ₛ
reifyᵖ-correct : ∀ {h} (v : Tyᵖ τ Γ h) → ⟦ reifyᵖ v ⟧ₙ ≡ h

reifyᵖ {τ = τ `× s} (a , b) = pair (reifyᵖ a) (reifyᵖ b)
reifyᵖ {τ = τ `⇒ s} f       = lam (reifyᵖ (f (drop stop) (reflectᵖ (var stop))))
reifyᵖ {τ = ` x} d          = ne (d .fst)
reifyᵖ {τ = `⊤} d           = unit

reflectᵖ {τ = τ `× σ} n     = reflectᵖ (fstₙ n) , reflectᵖ (sndₙ n)
reflectᵖ {τ = τ `⇒ σ} n ρ a = tyᵖ⟨ ap₂ (λ e f → ev ∘ ⟨ e , f ⟩) (ren-⟦⟧ₛ ρ n) (reifyᵖ-correct a) ⟩
  (reflectᵖ (app (ren-ne ρ n) (reifyᵖ a)))
reflectᵖ {τ = ` x}    n     = n , refl
reflectᵖ {τ = `⊤}     _     = lift tt

reifyᵖ-correct {τ = τ `× σ} (a , b) = sym $
  ⟨⟩-unique (sym (reifyᵖ-correct a)) (sym (reifyᵖ-correct b))
reifyᵖ-correct {τ = τ `⇒ σ} {h = h} ν =
  ƛ ⟦ reifyᵖ (ν (drop stop) (reflectᵖ (var stop))) ⟧ₙ
    ≡⟨ ap ƛ (reifyᵖ-correct (ν (drop stop) (reflectᵖ (var stop)))) ⟩
  ƛ (ev ∘ ⟨ h ∘ id ∘ π₁ , π₂ ⟩)
    ≡⟨ ap₂ (λ a b → ƛ (ev ∘ ⟨ a , b ⟩)) (pulll (elimr refl)) (introl refl) ⟩
  ƛ (unlambda h)
    ≡˘⟨ unique _ refl ⟩
  h ∎
reifyᵖ-correct {τ = ` x} d = d .snd
reifyᵖ-correct {τ = `⊤}  d = !-unique _

private
  tickᵖ : ∀ {x y h} (m : Hom ⟦ x ⟧ᵗ ⟦ y ⟧ᵗ) → Tyᵖ x Γ h → Tyᵖ y Γ (m ∘ h)
  tickᵖ {x = x} {y = `⊤}  m a = lift tt
  tickᵖ {x = x} {y = ` τ} m a =
    hom {Δ = ∅ , x} (m ∘ π₂) (∅ , reifyᵖ a) ,
    pullr π₂∘⟨⟩ ∙ ap (m ∘_) (reifyᵖ-correct a)

  tickᵖ {y = τ `× σ} m a =
      tyᵖ⟨ pullr refl ⟩ (tickᵖ (π₁ ∘ m) a)
    , tyᵖ⟨ pullr refl ⟩ (tickᵖ (π₂ ∘ m) a)

  tickᵖ {x = x} {y = τ `⇒ σ} m a ρ y =
    tyᵖ⟨ pullr (⟨⟩-unique (pulll π₁∘⟨⟩ ∙ extendr π₁∘⟨⟩) (pulll π₂∘⟨⟩ ∙ π₂∘⟨⟩)) ⟩
    (tickᵖ {x = x `× τ} (ev ∘ ⟨ m ∘ π₁ , π₂ ⟩)
      (tyᵖ⟨ sym π₁∘⟨⟩ ⟩ (ren-tyᵖ ρ a) , tyᵖ⟨ sym π₂∘⟨⟩ ⟩ y))

  morᵖ : ∀ {h} (e : Mor τ σ) (ρ : Tyᵖ τ Γ h) → Tyᵖ σ Γ (⟦ e ⟧ᵐ ∘ h)
  morᵖ (` x) = tickᵖ x

  morᵖ `id      ρ = tyᵖ⟨ introl refl ⟩ ρ
  morᵖ (f `∘ g) ρ = tyᵖ⟨ pulll refl ⟩ (morᵖ f (morᵖ g ρ))

  morᵖ `!       ρ = lift tt
  morᵖ `π₁      ρ = ρ .fst
  morᵖ `π₂      ρ = ρ .snd
  morᵖ (e `, f) ρ = record
    { fst = tyᵖ⟨ sym (pulll π₁∘⟨⟩) ⟩ (morᵖ e ρ)
    ; snd = tyᵖ⟨ sym (pulll π₂∘⟨⟩) ⟩ (morᵖ f ρ)
    }

  morᵖ `ev (f , x) = tyᵖ⟨ ap (ev ∘_) (sym (⟨⟩-unique (intror refl) refl)) ⟩
    (f stop x)

  morᵖ {h = h} (`ƛ e) t r {h'} a = tyᵖ⟨ sym p ⟩ (morᵖ e
      ( tyᵖ⟨ sym π₁∘⟨⟩ ⟩ (ren-tyᵖ r t)
      , tyᵖ⟨ sym π₂∘⟨⟩ ⟩ a ))
    where
    p =
      ev ∘ ⟨ ((ƛ ⟦ e ⟧ᵐ) ∘ h) ∘ ⟦ r ⟧ʳ , h' ⟩
        ≡⟨ ap (ev ∘_) (sym (⟨⟩-unique (pulll π₁∘⟨⟩ ∙ pullr π₁∘⟨⟩ ∙ pulll refl) (pulll π₂∘⟨⟩ ∙ pullr π₂∘⟨⟩ ∙ idl _))) ⟩
      ev ∘ (ƛ ⟦ e ⟧ᵐ ⊗₁ id) ∘ ⟨ h ∘ ⟦ r ⟧ʳ , h' ⟩
        ≡⟨ pulll (commutes _) ⟩
      ⟦ e ⟧ᵐ ∘ ⟨ h ∘ ⟦ r ⟧ʳ , h' ⟩
        ∎
```
</details>

Putting the NbE pieces together, we get a normalisation function together
with a proof of soundness, which allows us to write a `solve`{.Agda}
function.

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
