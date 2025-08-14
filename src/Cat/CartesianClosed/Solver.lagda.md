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

To use contexts, we introduce _variables_. A variable $v : \Gamma \ni
\tau$ gives an index in $\Gamma$ where something of type $\tau$ can be
found. It can either be right here, in which case we `stop`{.Agda}, or
it can be further back in the context, and we must `pop`{.Agda} the top
variable off to get to it.

```agda
data Var : Cx → Ty → Type o where
  stop : Var (Γ , τ) τ
  pop  : Var Γ τ → Var (Γ , σ) τ
```

Using the Cartesian closed structure of $\cC$, we can interpret types,
contexts and variables in terms of the structural morphisms: for
example, the empty context is interpreted by the terminal object,
and, since contexts are built by extension on the _right_, the zeroth
variable is given by the second projection map $\Gamma \times A \to A$.

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

⟦_⟧ⁿ : Var Γ τ → Hom ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ
⟦ stop ⟧ⁿ  = π₂
⟦ pop x ⟧ⁿ = ⟦ x ⟧ⁿ ∘ π₁
```

The idea is then to write a faithful representation of the way morphisms
in a CCC appear in equational goals (in terms of identities, compositions,
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

## Context inclusions

We will implement our semantics using *normalisation by evaluation*, by
embedding our expressions into a domain where the judgemental equalities
of the object-level are also judgemental at the meta-level. We choose
presheaves on a category of *inclusions*, where the objects are contexts
and the maps $\Gamma \to \Delta$ indicate that, starting from $\Gamma$,
you can get to $\Delta$ by *dropping* some of the variables, and keeping
everything else in-order.

```agda
data Ren : Cx → Cx → Type (o ⊔ ℓ) where
  stop : Ren Γ Γ
  drop : Ren Γ Δ → Ren (Γ , τ) Δ
  keep : Ren Γ Δ → Ren (Γ , τ) (Δ , τ)
```

Here we must confess to another crime: Since our (types, hence our)
contexts include objects of the base category, they do not form a set:
therefore, neither does the type `Ren`{.Agda} of context inclusions.
This means that we can not use `Ren`{.Agda} as the morphisms in a
(pre)category. This could be remedied by instead working relative to a
given set of base types, which are equipped with a map into semantic
objects. This does not significantly alter the development, but it would
be an additional inconvenience.

Regardless, we can define composition of context inclusions by
recursion, and, if necessary, we could prove that this is associative
and unital. However, since we are not building an actual category of
presheaves (only gesturing towards one), we omit these proofs.

```agda
_∘ʳ_ : ∀ {Γ Δ Θ} → Ren Γ Δ → Ren Δ Θ → Ren Γ Θ
stop   ∘ʳ ρ      = ρ
drop σ ∘ʳ ρ      = drop (σ ∘ʳ ρ)
keep σ ∘ʳ stop   = keep σ
keep σ ∘ʳ drop ρ = drop (σ ∘ʳ ρ)
keep σ ∘ʳ keep ρ = keep (σ ∘ʳ ρ)
```

If we fix a type $\tau$, then the family $- \ni \tau$ which sends a
context to the variables in that context is actually a presheaf. Put
less pretentiously, renamings act on variables:

```agda
ren-var : ∀ {Γ Δ τ} → Ren Γ Δ → Var Δ τ → Var Γ τ
ren-var stop     v       = v
ren-var (drop σ) v       = pop (ren-var σ v)
ren-var (keep σ) stop    = stop
ren-var (keep σ) (pop v) = pop (ren-var σ v)
```

Finally, we can define an interpretation of renamings into our model
CCC. Note that this interpretation lands in monomorphisms.

```agda
⟦_⟧ʳ : Ren Γ Δ → Hom ⟦ Γ ⟧ᶜ ⟦ Δ ⟧ᶜ
⟦ stop   ⟧ʳ = id
⟦ drop r ⟧ʳ = ⟦ r ⟧ʳ ∘ π₁
⟦ keep r ⟧ʳ = ⟦ r ⟧ʳ ⊗₁ id
```

## Normals and neutrals

To define evaluation, we need a type of normal forms: In our setting,
these include lambda abstractions and pairs, along with morphisms of the
base category. However, we are not working with evaluation, rather with
_normalisation_, where reduction takes place in arbitrary contexts.
Therefore, there are expressions that we can not *give a value to*, but
for which no further normalisation can happen: for example, applying a
variable. Therefore, we define mutually inductive types of **normal
forms** and **neutral forms**.

```agda
data Nf           : Cx → Ty → Type (o ⊔ ℓ)
data Ne           : Cx → Ty → Type (o ⊔ ℓ)
data Sub (Γ : Cx) : Cx → Type (o ⊔ ℓ)
```

A **normal form** is indeed one for which no more reduction is possible:
lambda expressions and pairs. A neutral form is also normal. These come
primarily from non-empty contexts. Neutral forms are, essentially,
variables together with a stack of *pending eliminations* (applications
or projections that will be reduced in the future). However, in our
setting, we also consider the base terms as neutral _at base types_.

```agda
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
```

Note that, for our practical applications, we need renaming neutrals to
preserve any morphisms from the base category definitionally. To this
end, neutrals at base type are implemented as *closures*: they contain
the base morphism as it was in its original context $\Delta$, and a
*substitution* $\Gamma \vdash \Delta$ from the original context to the
current context--- a list of $\Gamma$-terms for each type in
$\Delta$---, which we think of as "the captured variables". Renaming a
neutral in $\operatorname{Ne}(\Gamma, \tau)$ along $\rho : \Theta \vdash
\Gamma$ can then preserve the included morphism and act only on the
substitution.

```agda
data Sub Γ where
  ∅   : Sub Γ ∅
  _,_ : Sub Γ Δ → Nf Γ τ → Sub Γ (Δ , τ)
```

By a fairly obvious recursion, we can extend renamings to act on
neutrals, normals, and substitutions. This makes each of
$\operatorname{Ne}(-,\tau)$, $\operatorname{Nf}(-,\tau)$ and
$\operatorname{Sub}(-,\Theta)$ into presheaves on renamings.

```agda
ren-ne  : ∀ {Γ Δ τ} → Ren Δ Γ → Ne  Γ τ → Ne  Δ τ
ren-nf  : ∀ {Γ Δ τ} → Ren Δ Γ → Nf  Γ τ → Nf  Δ τ
ren-sub : ∀ {Γ Δ Θ} → Ren Δ Γ → Sub Γ Θ → Sub Δ Θ
```

The only case that requires attention is that for neutrals at base type,
i.e. morphisms from the base category. As mentioned above, we leave the
morphism intact--- its context is not required to match the context of
the neutral--- and act on the substitution instead.

```agda
ren-ne σ (hom h a) = hom h (ren-sub σ a)
```

<!--
```agda
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
```
-->

Normals and neutrals also have a straightforward denotation given by the
Cartesian closed structure.

```agda
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
```

We also have to prove a few hateful lemmas about how renamings, and its
action on variables, neutrals and normals, interact with the denotation
brackets. These lemmas essentially say that $\sem{f[\rho]} =
\sem{f}\sem{\rho}$, so that it doesn't matter whether we first pass to
the semantics in $\cC$ or apply a renaming.

```agda
⟦⟧-∘ʳ   : (ρ : Ren Γ Δ) (σ : Ren Δ Θ) → ⟦ ρ ∘ʳ σ ⟧ʳ ≡ ⟦ σ ⟧ʳ ∘ ⟦ ρ ⟧ʳ

ren-⟦⟧ⁿ : (ρ : Ren Δ Γ) (v : Var Γ τ) → ⟦ ren-var ρ v ⟧ⁿ ≡ ⟦ v ⟧ⁿ ∘ ⟦ ρ ⟧ʳ
ren-⟦⟧ₛ : (ρ : Ren Δ Γ) (t : Ne Γ τ)  → ⟦ ren-ne ρ t  ⟧ₛ ≡ ⟦ t ⟧ₛ ∘ ⟦ ρ ⟧ʳ
ren-⟦⟧ₙ : (ρ : Ren Δ Γ) (t : Nf Γ τ)  → ⟦ ren-nf ρ t  ⟧ₙ ≡ ⟦ t ⟧ₙ ∘ ⟦ ρ ⟧ʳ
ren-⟦⟧ᵣ : (ρ : Ren Δ Γ) (σ : Sub Γ Θ) → ⟦ ren-sub ρ σ ⟧ᵣ ≡ ⟦ σ ⟧ᵣ ∘ ⟦ ρ ⟧ʳ
```

<details>
<summary>If you want, you can choose to read the proofs of these
substitution correctness lemmas by clicking on this `<details>`{.html}
tag.
</summary>

```agda
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
```
</details>

## Normalization

We would like to write a map of type `Expr Γ τ → Nf Γ τ`. However, *by
design*, this is not straightforward: the type of normal forms is...
$\beta$-normal.^[It is not, however, $\eta$-long.] However, note that,
since both `Nf` and `Ne` are "presheaves" on the "category of
renamings", we can use the Cartesian closed structure *of presheaves* to
interpret the lambda calculus. The idea here is that presheaves, being
functors into $\Sets$, have a computational structure on the relevant
connectives that closely matches that of $\Sets$ itself: for example,
composing the first projection with a pairing, in the category of
presheaves, is (componentwise) definitionally equal to the first
component of the pair. It's a boosted up version of exactly the same
idea used for [the category solver].

[the category solver]: Cat.Solver.html

Then, as long as we can *reify* these presheaves back to normal forms,
we have a normalisation procedure! Expressions are interpreted as
sections of the relevant presheaves, then reified into normal forms.
And, to be clear, we only need to reflect the presheaves that actually
represent types: these can be built by recursion (on the type!) so that
they are very easy to reify.

However, that still leaves the question of _correctness_ for the NbE
algorithm. Given an expression $\Gamma \vdash e : \tau$, we will have
two wildly different approaches to interpreting $e$ as a morphism
$\sem{\Gamma} \to \sem{\tau}$. There's the naïve denotation
`⟦_⟧ᵉ`{.Agda}, which interprets an expression directly using the
relevant connections; But now we can also interpret an expression
$\Gamma \vdash e : \tau$ into a section $v : \cR^\tau(\Gamma)$, then
reify that to a normal form $n : \operatorname{Nf}(\Gamma, \tau)$, and
take the denotation $\sem{n} : \sem{\Gamma} \to \sem{\tau}$.
Normalisation _should_ compute a $\beta$-normal form, and $\beta$ is
validated by CCCs, so $\sem{n}$ and $\sem{e}$ should be the same. How do
we ensure this?

It would be totally possible to do this in two passes - first define the
algorithm, then prove it correct. But the proof of correctness would
mirror the structure of the algorithm almost 1:1! Can we define the
algorithm in a way that is _forced_ into correctness? It turns out
that we can! The idea here is an adaptation of the **gluing** method in
the semantics of type theory. Rather than have a mere presheaf
$\cR^\tau(-)$ to represent the semantic values in $\tau$, our full
construction `Tyᵖ`{.Agda} has _three_ arguments: The type $\tau$, the
context $\Gamma$ (over which it is functorial), and a _denotation_ $h :
\sem{\Gamma} \to \sem{\tau}$ --- and in prose, we'll write `Tyᵖ`{.Agda}
as $\cR^\tau_{h}(\Gamma)$; we say that $s$ **tracks** $h$ when $s :
\cR^\tau_{h}(\Gamma)$.

Since all our operations on semantic values will be written against a
type _indexed by_ their denotations, the core of the algorithm will
_have to_ be written in a way that evidently preserves denotations ---
the type checker is doing most of the work. Our only actual correctness
theorem boils down to showing that, given $s : \cR^\tau_{h}(\Gamma)$, we
have $\sem{\reify s} = h$ in $\hom(\sem{\Gamma}, \sem{\tau})$.

To summarize all the parts, we have:

- **Expressions** $\Gamma \vdash e : \tau$ --- the user writes these, and
  they may have redices.

- **Denotations** $\sem{e} : \sem{\Gamma} \to \sem{\tau}$. Since a CCC
  has "structural" morphisms corresponding to each kind of expression, we
  can directly read off a morphism from an expression.

- **Neutrals** $n : \Ne(\Gamma, \tau)$ and **normals** $n : \Nf(\Gamma, \tau)$.
  A neutral is something that wants to reduce but can't (e.g. a
  projection applied to a variable), and a normal is something that
  definitely won't reduce anymore (e.g. a lambda expression). Normals
  and neutrals also have denotations, so we may also write $\sem{n}$
  when $n : \Nf(-,-)$ or $n : \Ne(-,-)$.

- **Semantic values**, $\cR^\tau_h(\Gamma)$. The presheaf
  $\cR^\tau_{h}(\Gamma)$ is computed by recursion on $\tau$ so that its
  sections have a good computational representation. As mentioned above, it's
  indexed by a denotation $h : \sem{\Gamma} \to \sem{\tau}$, forcing the
  core of the algorithm to preserve denotations.

- The **reification and reflection** transformations $\reify :
\cR^\tau_{-}(\Gamma) \to \Nf(\Gamma, \tau)$, which turns a semantic
value into a normal form, and $\reflect : \Ne(\Gamma, \tau) \to
\cR^\tau_{-}(\Gamma)$ which witnesses that the semantic values include
the neutrals.

Our main objective is a normalisation function $\operatorname{expr}$
that maps expressions $\Gamma \vdash e : \tau$ to semantic values
$\operatorname{expr}(e) : \cR^\tau_{\sem{e}}(\Gamma)$. Let's get
started.

### Semantic values

```agda
Tyᵖ : (τ : Ty) (Γ : Cx) → Hom ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ → Type (o ⊔ ℓ)
```

We define $\cR^{\tau}_{-}(-)$ by recursion on $\tau$, and its
definition is mostly unsurprising: at each case, we use the Cartesian
closed structure of presheaf categories to interpret the given type into
a presheaf that has the right universal property, but is "definitionally
nicer". Let's go through it case-by-case. When faced with a product type
in the object language, we can simply return a meta-language product
type. However, we must also preserve the tracking information: if a
section of a product type is to track $h$, what should each component
track? Well, we know that $h = \langle \pi_1h, \pi_2h \rangle$, by the
uniqueness property of Cartesian products. So the first component should
track $\pi_1h$, and the second $\pi_2h$!

```agda
Tyᵖ (τ `× σ) Γ h = Tyᵖ τ Γ (π₁ ∘ h) × Tyᵖ σ Γ (π₂ ∘ h)
```

Again following this pointwise logic, the semantic presheaf for the unit
type takes values the unit type everywhere.

```agda
Tyᵖ `⊤ Γ h = Lift _ ⊤
```

For a function type, we once again appeal to the construction in
presheaves. The components of the exponential $(Q^P)(\Gamma)$ are
[defined] to be the natural transformations $\yo(\Gamma) \times P \To
Q$, which, pointwise at $\Delta$, are given by maps $\hom(\Gamma,
\Delta) \times P(\Delta) \to Q(\Delta)$. A function value must preserve
tracking information: A function which tracks $h$, if given an argument
tracking $a$, it must return a value which tracks the application of $h$
to $a$, relative to the renaming $\rho$. In a CCC, this application is
given by
$$
\operatorname{ev} \langle h \circ \rho , a \rangle
$$,
and so that is precisely what we ask for.

[defined]: Cat.Instances.Presheaf.Exponentials.html

```agda
Tyᵖ (τ `⇒ σ) Γ h =
  ∀ {Δ} (ρ : Ren Δ Γ) {a}
  → Tyᵖ τ Δ a
  → Tyᵖ σ Δ (ev ∘ ⟨ h ∘ ⟦ ρ ⟧ʳ , a ⟩)
```

Finally, we have the case of base types, for which the corresponding
presheaf is that of neutral forms. Here, we can finally discharge the
tracking information: a neutral $n$ tracks $h$ iff. $\sem{n} = h$.

```agda
Tyᵖ (` x)    Γ h = Σ (Ne Γ (` x)) λ n → ⟦ n ⟧ₛ ≡ h
```

Finally, since we want to interpret terms in any context, we will need a
semantic presheaf of substitutions, tracking a morphism between
contexts. Much like ordinary substitutions are lists of neutrals, these
semantic substitutions are lists of semantic values.

```agda
data Subᵖ : ∀ Γ Δ → Hom ⟦ Δ ⟧ᶜ ⟦ Γ ⟧ᶜ → Type (o ⊔ ℓ) where
  ∅   : ∀ {i} → Subᵖ ∅ Δ i
  _,_ : ∀ {h} → Subᵖ Γ Δ (π₁ ∘ h) → Tyᵖ σ Δ (π₂ ∘ h) → Subᵖ (Γ , σ) Δ h
```

<!--
```agda
tyᵖ⟨_⟩ : ∀ {τ Γ h h'} → h ≡ h' → Tyᵖ τ Γ h → Tyᵖ τ Γ h'
tyᵖ⟨_⟩ {τ `× σ} p (a , b)   = tyᵖ⟨ ap (π₁ ∘_) p ⟩ a , tyᵖ⟨ ap (π₂ ∘_) p ⟩ b
tyᵖ⟨_⟩ {τ `⇒ σ} p ν ρ x     = tyᵖ⟨ ap (λ e → ev ∘ ⟨ e ∘ ⟦ ρ ⟧ʳ , _ ⟩) p ⟩ (ν ρ x)
tyᵖ⟨_⟩ {` x} p (n , q) .fst = n
tyᵖ⟨_⟩ {` x} p (n , q) .snd = q ∙ p
tyᵖ⟨_⟩ {`⊤}  p (lift tt)    = lift tt

subᵖ⟨_⟩ : ∀ {Γ Δ h h'} → h ≡ h' → Subᵖ Γ Δ h → Subᵖ Γ Δ h'
subᵖ⟨_⟩ p ∅       = ∅
subᵖ⟨_⟩ p (r , x) = subᵖ⟨ ap (π₁ ∘_) p ⟩ r , tyᵖ⟨ ap (π₂ ∘_) p ⟩ x
```
-->

As always, we must show that these have an action by renamings.
Renamings act on the semantic component, too: if $v$ tracks $h$, then
$v[\rho]$ tracks $h\sem{\rho}$.

```agda
ren-tyᵖ  : ∀ {Δ Γ τ m} (ρ : Ren Δ Γ) → Tyᵖ τ Γ m  → Tyᵖ  τ Δ (m ∘ ⟦ ρ ⟧ʳ)
ren-subᵖ : ∀ {Δ Γ Θ m} (ρ : Ren Θ Δ) → Subᵖ Γ Δ m → Subᵖ Γ Θ (m ∘ ⟦ ρ ⟧ʳ)
```

<!--
```agda
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
```
-->

### Reification and reflection

We can now define the reification and reflection functions. Reflection
embeds a neutral form into semantic values; Reification turns semantic
values into normal forms. Since we have defined the semantic values by
recursion, we can exploit the good computational behaviour of Agda types
in our reification/reflection functions: for example, when reifying at a
product type, we know that we have an honest-to-god product of semantic
values at hand.

```agda
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
```

The interesting cases deal with function types: To reify a lambda ---
which is semantically represented by a *function* that operates on (a
renaming and) the actual argument --- we produce a `lam`{.Agda}
constructor, but we must then somehow reify "all possible bodies".

However, since the semantic value of a function takes arguments and
returns results in an arbitrary extension of the given context, we can
introduce a new variable --- thus a new neutral --- and apply the body
_to that_. Evaluation keeps going, but anything that actually depends on
the body will be blocked on this new neutral!

Conversely, reflection starts from a neutral, and must build a semantic
value that captures all the pending applications. At the case of a
lambda, we have a neutral $n : \Gamma \vdash A \to B$, a renaming $\rho
: \Delta \to \Gamma$, and an argument $a : \Delta \vdash A$. We can thus
build the stuck application $n[\rho]\; a : \Delta \vdash B$.

This is also where we encounter the only correctness lemma that is not
forced on us by the types involved, since the type of normal forms
$\Nf(\Gamma, \tau)$ is not indexed by a denotation in $\cC$. We must
write an external function `reifyᵖ-correct`{.Agda}, actually
establishing that $\sem{\reify v} = h$ when $v$ tracks $h$.

```agda
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
```

### Interpreting formal morphisms

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
  tickᵖ {x = x} {y = `⊤}  m a = lift tt
  tickᵖ {x = x} {y = ` τ} m a =
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
  tickᵖ {y = τ `× σ} m a =
      tyᵖ⟨ pullr refl ⟩ (tickᵖ (π₁ ∘ m) a)
    , tyᵖ⟨ pullr refl ⟩ (tickᵖ (π₂ ∘ m) a)

  tickᵖ {x = x} {y = τ `⇒ σ} m a ρ y =
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

## Assembling the solver

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
