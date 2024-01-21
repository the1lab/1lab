<!--
```agda
open import Cat.Diagram.Limit.Finite
open import Cat.Displayed.Doctrine
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Displayed.Base
open import Cat.Prelude hiding (_ʻ_)

import Cat.Displayed.Reasoning as Disp
import Cat.Reasoning as Cat

import Order.Reasoning
```
-->

```agda
module Cat.Displayed.Doctrine.Logic
```

<!--
```agda
  {o ℓ o' ℓ'} {B : Precategory o ℓ}
  (fc : Finitely-complete B)
  (P : Regular-hyperdoctrine B o' ℓ')
  where

open Regular-hyperdoctrine P
open Finitely-complete fc hiding (_⊗₀_)
open Binary-products B products
open Displayed ℙ
open Cat B

private module P {x} = Order.Reasoning (≤-Poset {x})
```
-->

# The internal logic of a regular hyperdoctrine {defines="logic-in-a-hyperdoctrine"}

Fix a [[regular hyperdoctrine]] $\bP$ over a [[finitely complete
category]] $\cB$. We've claimed that the data of $\bP$ is enough to
interpret regular logic relative to $\cB$, but that proof was deferred.
This module actually finishes this claim, but because syntax is always
fiddly, it's _quite_ long.

## Terms

The first thing we'll do is strictify $\cB$ a bit. Instead of working
directly with arbitrary morphisms, it's slightly better --- for the
computational behaviour of substitution --- to have a syntactic
presentation of the terms of our logic. We start with the **types**,
built inductively using `` _`×_ ``{.Agda}, and with an injection from
the objects of $\cB$. We also single out a class of objects which are
built from repeated pairing onto the terminal object to be the
**contexts**.

```agda
data Ty : Typeω where
  ↑    : Ob → Ty
  _`×_ : Ty → Ty → Ty

data Cx : Typeω where
  []  : Cx
  _ʻ_ : Cx → Ty → Cx
```

<!--
```agda
infixl 15 _ʻ_
infixl 17 _`∧_ _`×_

private variable
  Γ Δ Θ : Cx
  τ σ   : Ty
```
-->

These two classes can be interpreted into objects in the base category.
Throughout this entire module, we'll write $\sem{x}$ for the semantic
interpretation of a syntactic object; In the formalisation, the brackets
are always superscript with an indicator of what is being interpreted.

```agda
⟦_⟧ᵗ : Ty → Ob
⟦ ↑ x    ⟧ᵗ = x
⟦ t `× s ⟧ᵗ = ⟦ t ⟧ᵗ ⊗₀ ⟦ s ⟧ᵗ

⟦_⟧ᶜ : Cx → Ob
⟦ []    ⟧ᶜ = Terminal.top terminal
⟦ Γ ʻ x ⟧ᶜ = ⟦ Γ ⟧ᶜ ⊗₀ ⟦ x ⟧ᵗ
```

Next we have the syntax of _variables_: A variable $v : \Gamma \ni \tau$
encodes a projection $\sem{v}$, which, because of the structure of our
contexts, is always of the form $\pi_2 \pi_1 \pi_1 \dots$. Put
syntactically, we can always access the latest variable, and we can also
weaken variables by one.

```agda
data _∋_ : Cx → Ty → Typeω where
  stop : (Γ ʻ τ) ∋ τ
  pop  : Γ ∋ τ → (Γ ʻ σ) ∋ τ
```

Finally, we can define the class of terms: A term is a variable, or lies
in the fragment dealing with Cartesian products, or comes from applying
a function $\sem{\tau} \to \sem{\sigma}$ from the base category to an
argument $\Gamma \vdash \tau$; this is required if we want our logic to
be applicable to more than variables and products!

```agda
data Tm : Cx → Ty → Typeω where
  var : Γ ∋ τ → Tm Γ τ

  _,_ : Tm Γ τ → Tm Γ σ → Tm Γ (τ `× σ)
  `π₁ : Tm Γ (τ `× σ) → Tm Γ τ
  `π₂ : Tm Γ (τ `× σ) → Tm Γ σ

  fun : Hom ⟦ τ ⟧ᵗ ⟦ σ ⟧ᵗ → Tm Γ τ → Tm Γ σ

-- Superscript n for "name", e for "expression"
⟦_⟧ⁿ : Γ ∋ τ → Hom ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ
⟦ stop ⟧ⁿ  = π₂
⟦ pop x ⟧ⁿ = ⟦ x ⟧ⁿ ∘ π₁

⟦_⟧ᵉ : Tm Γ τ → Hom ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ
⟦ var x ⟧ᵉ   = ⟦ x ⟧ⁿ
⟦ x , y ⟧ᵉ   = ⟨ ⟦ x ⟧ᵉ , ⟦ y ⟧ᵉ ⟩
⟦ `π₁ x ⟧ᵉ   = π₁ ∘ ⟦ x ⟧ᵉ
⟦ `π₂ x ⟧ᵉ   = π₂ ∘ ⟦ x ⟧ᵉ
⟦ fun f t ⟧ᵉ = f ∘ ⟦ t ⟧ᵉ
```

## Renamings and substitutions

Even after we have a good grasp on the morphisms in $\cB$ that we want
to call _terms_, there are still two classes of maps, now between pairs
of contexts, that we must single out. A **renaming** $\rho : \Gamma \to
\Delta$ maps variables in $\Delta$ to variables in $\Gamma$: there's an
identity renaming, and you can either choose to keep or drop variables
from $\Delta$.

If we allow ourselves to map variables in $\Delta$ to _terms_ in
$\Gamma$, we get the class of **substitutions**. Now, instead of keeping
a variable as-is, we can instead use an arbitrary term:

```agda
data Ren : Cx → Cx → Typeω where
  stop : Ren Γ Γ
  drop : Ren Γ Δ → Ren (Γ ʻ τ) Δ
  keep : Ren Γ Δ → Ren (Γ ʻ τ) (Δ ʻ τ)

data Sub : Cx → Cx → Typeω where
  stop : Sub Γ Γ
  _,_  : Tm Γ τ  → Sub Γ Δ → Sub Γ (Δ ʻ τ)
  drop : Sub Γ Δ → Sub (Γ ʻ τ) Δ
```

```agda
-- Superscript r for "renaming", s for "substitution"
⟦_⟧ʳ : Ren Γ Δ → Hom ⟦ Γ ⟧ᶜ ⟦ Δ ⟧ᶜ
⟦ stop ⟧ʳ = id
⟦ drop r ⟧ʳ = ⟦ r ⟧ʳ ∘ π₁
⟦ keep r ⟧ʳ = ⟦ r ⟧ʳ ⊗₁ id

⟦_⟧ˢ : Sub Γ Δ → Hom ⟦ Γ ⟧ᶜ ⟦ Δ ⟧ᶜ
⟦ stop    ⟧ˢ = id
⟦ x , s   ⟧ˢ = ⟨ ⟦ s ⟧ˢ , ⟦ x ⟧ᵉ ⟩
⟦ drop ρ  ⟧ˢ = ⟦ ρ ⟧ˢ ∘ π₁
```

One substitution which deserves special attention is the "terminating"
substitution, which maps from an arbitrary $\Gamma$ to the empty
context.

```agda
!ˢ : ∀ {Γ} → Sub Γ []
!ˢ {[]}    = Sub.stop
!ˢ {Γ ʻ x} = Sub.drop !ˢ
```

Now comes the fiddly part of dealing with syntax: the endless recursive
functions for the action of renamings and substitutions on _everything_,
and all the correctness lemmas that guarantee we're doing the right
thing.

```agda
_∘ʳ_    : Ren Γ Δ → Ren Δ Θ → Ren Γ Θ
ren-var : Ren Γ Δ → Δ ∋ τ → Γ ∋ τ
ren-tm  : Ren Γ Δ → Tm Δ τ → Tm Γ τ
sub-var : Sub Γ Δ → Δ ∋ τ → Tm Γ τ
sub-tm  : Sub Γ Δ → Tm Δ τ → Tm Γ τ

ren-var-correct
  : (ρ : Ren Γ Δ) (v : Δ ∋ τ) → ⟦ ren-var ρ v ⟧ⁿ ≡ ⟦ v ⟧ⁿ ∘ ⟦ ρ ⟧ʳ
sub-var-correct
  : (ρ : Sub Γ Δ) (t : Δ ∋ τ) → ⟦ sub-var ρ t ⟧ᵉ ≡ ⟦ t ⟧ⁿ ∘ ⟦ ρ ⟧ˢ

ren-tm-correct
  : (ρ : Ren Γ Δ) (v : Tm Δ τ) → ⟦ ren-tm ρ v ⟧ᵉ ≡ ⟦ v ⟧ᵉ ∘ ⟦ ρ ⟧ʳ
sub-tm-correct
  : (ρ : Sub Γ Δ) (t : Tm Δ τ) → ⟦ sub-tm ρ t ⟧ᵉ ≡ ⟦ t ⟧ᵉ ∘ ⟦ ρ ⟧ˢ
```

<details>
<summary>For the sake of the reader's sanity, we've chosen to display
only the type signatures, and all the implementations are in this
`<details>`{.html} block.</summary>

```agda
stop   ∘ʳ ρ     = ρ
drop σ ∘ʳ ρ     = drop (σ ∘ʳ ρ)

keep σ ∘ʳ stop   = keep σ
keep σ ∘ʳ drop ρ = drop (σ ∘ʳ ρ)
keep σ ∘ʳ keep ρ = keep (σ ∘ʳ ρ)

ren-var stop     v       = v
ren-var (drop σ) v       = pop (ren-var σ v)
ren-var (keep σ) stop    = stop
ren-var (keep σ) (pop v) = pop (ren-var σ v)

ren-tm ρ (var x)    = var (ren-var ρ x)
ren-tm ρ (t , s)    = ren-tm ρ t , ren-tm ρ s
ren-tm ρ (`π₁ t)    = `π₁ (ren-tm ρ t)
ren-tm ρ (`π₂ t)    = `π₂ (ren-tm ρ t)
ren-tm ρ (fun x t)  = fun x (ren-tm ρ t)

sub-var stop v          = var v
sub-var (x , ρ) stop    = x
sub-var (x , ρ) (pop v) = sub-var ρ v
sub-var (drop ρ) v      = ren-tm (drop stop) (sub-var ρ v)

sub-tm ρ (var x)    = sub-var ρ x
sub-tm ρ (t , s)    = sub-tm ρ t , sub-tm ρ s
sub-tm ρ (`π₁ tm)   = `π₁ (sub-tm ρ tm)
sub-tm ρ (`π₂ tm)   = `π₂ (sub-tm ρ tm)
sub-tm ρ (fun x tm) = fun x (sub-tm ρ tm)

ren-var-correct stop v = sym (idr _)
ren-var-correct (drop ρ) v = ap (_∘ π₁) (ren-var-correct ρ v) ∙ sym (assoc _ _ _)
ren-var-correct (keep ρ) stop    = sym (π₂∘⟨⟩ ∙ idl _)
ren-var-correct (keep ρ) (pop v) =
  pushl (ren-var-correct ρ v) ∙ sym (pullr π₁∘⟨⟩)

ren-tm-correct ρ (var x)   = ren-var-correct ρ x
ren-tm-correct ρ (v , v₁)  = sym (⟨⟩∘ _ ∙ sym (ap₂ ⟨_,_⟩ (ren-tm-correct ρ v) (ren-tm-correct ρ v₁)))
ren-tm-correct ρ (`π₁ v)   = pushr (ren-tm-correct ρ v)
ren-tm-correct ρ (`π₂ v)   = pushr (ren-tm-correct ρ v)
ren-tm-correct ρ (fun x v) = pushr (ren-tm-correct ρ v)

sub-var-correct stop    t       = sym (idr _)
sub-var-correct (x , ρ) stop    = sym π₂∘⟨⟩
sub-var-correct (x , ρ) (pop t) = sym (pullr π₁∘⟨⟩ ∙ sym (sub-var-correct ρ t))
sub-var-correct (drop ρ) v      =
  ren-tm-correct (drop stop) (sub-var ρ v)
    ∙ extendl (idr _ ∙ sub-var-correct ρ v)

sub-tm-correct ρ (var x) = sub-var-correct ρ x
sub-tm-correct ρ (t , s) =
  sym (⟨⟩∘ _ ∙ ap₂ ⟨_,_⟩ (sym (sub-tm-correct ρ t)) (sym (sub-tm-correct ρ s)))
sub-tm-correct ρ (`π₁ t) = ap (π₁ ∘_) (sub-tm-correct ρ t) ∙ assoc _ _ _
sub-tm-correct ρ (`π₂ t) = ap (π₂ ∘_) (sub-tm-correct ρ t) ∙ assoc _ _ _
sub-tm-correct ρ (fun x t) = ap (x ∘_) (sub-tm-correct ρ t) ∙ assoc _ _ _
```

</details>

## Formulae

Finally, we have a syntactic description of the objects in $\bP(\Gamma)$
that concern regular logic: they are built from the following grammar.
Each fibre has a top element and conjunction. We single out the
existential quantification along the latest variable

$$
\exists_\pi : \bP(\Gamma,x) \to \bP(\Gamma)\text{.}
$$

Moreover, we can define equality $t = s$ of terms $t, s : \Gamma \vdash
\tau$ in terms of existential quantification, though not along a
variable, so it gets its own constructor; and finally, if you have a
predicate on a _type_ $P : \bP(\tau)$ and a term $t : \Gamma \vdash
\tau$, then you can from $P(t) : \bP(\Gamma)$.

```agda
data Formula : Cx → Typeω where
  `⊤   : Formula Γ
  _`∧_ : Formula Γ → Formula Γ → Formula Γ

  `∃   : Formula (Γ ʻ τ) → Formula Γ

  _=ᵖ_ : Tm Γ τ → Tm Γ τ → Formula Γ

  pred : ℙ.Ob[ ⟦ τ ⟧ᵗ ] → Tm Γ τ → Formula Γ
```

The formulas over $\Gamma$ become objects over $\Gamma$ in the way that
was implied in the definition of hyperdoctrine: in particular, the
inclusion of semantic predicates is interpreted into substitution, and
the equality predicate is interpreted by the formula

$$
(\exists_\delta \top)[\langle t, s \rangle]\text{.}
$$

```agda
⟦_⟧ᵖ : Formula Γ → ℙ.Ob[ ⟦ Γ ⟧ᶜ ]
⟦ x `∧ y    ⟧ᵖ = ⟦ x ⟧ᵖ & ⟦ y ⟧ᵖ
⟦ `⊤        ⟧ᵖ = aye
⟦ `∃ x      ⟧ᵖ = exists π₁ ⟦ x ⟧ᵖ
⟦ pred p tm ⟧ᵖ = p [ ⟦ tm ⟧ᵉ ]
⟦ t =ᵖ s    ⟧ᵖ = exists ⟨ id , id ⟩ aye [ ⟨ ⟦ t ⟧ᵉ , ⟦ s ⟧ᵉ ⟩ ]
```

Once again we have the strictified presentation of substitution, though
this time it's short enough to present inline:

```agda
sub-prop : Sub Γ Δ → Formula Δ → Formula Γ
sub-prop ρ (φ `∧ ψ)   = sub-prop ρ φ `∧ sub-prop ρ ψ
sub-prop ρ (t =ᵖ s)   = sub-tm ρ t =ᵖ sub-tm ρ s
sub-prop ρ `⊤         = `⊤
sub-prop ρ (`∃ φ)     = `∃ (sub-prop (var stop , Sub.drop ρ) φ)
sub-prop ρ (pred x t) = pred x (sub-tm ρ t)
```

Unfortunately, we also have to prove that this is sent by $\sem{-}$ to
the semantic substitution:

```agda
sub-prop-correct
  : (ρ : Sub Γ Δ) (φ : Formula Δ)
  → ⟦ sub-prop ρ φ ⟧ᵖ ≡ ⟦ φ ⟧ᵖ [ ⟦ ρ ⟧ˢ ]

sub-prop-correct ρ (φ `∧ ψ) = sym $
  (⟦ φ ⟧ᵖ & ⟦ ψ ⟧ᵖ) [ ⟦ ρ ⟧ˢ ]           ≡⟨ subst-& _ _ _ ⟩
  ⟦ φ ⟧ᵖ [ ⟦ ρ ⟧ˢ ] & ⟦ ψ ⟧ᵖ [ ⟦ ρ ⟧ˢ ]  ≡˘⟨ ap₂ _&_ (sub-prop-correct ρ φ) (sub-prop-correct ρ ψ) ⟩
  ⟦ sub-prop ρ (φ `∧ ψ) ⟧ᵖ               ∎

sub-prop-correct ρ `⊤       = sym (subst-aye _)

sub-prop-correct {Γ = Γ} ρ (`∃ {Γ = Δ} {τ = τ} φ) =
  exists π₁ ⟦ sub-prop (var stop , drop ρ) φ ⟧ᵖ   ≡⟨ ap (exists _) (sub-prop-correct _ φ) ⟩
  exists π₁ (⟦ φ ⟧ᵖ [ ⟨ ⟦ ρ ⟧ˢ ∘ π₁ , π₂ ⟩ ])     ≡⟨ beck-chevalley rem₁ ⟩
  (exists π₁ ⟦ φ ⟧ᵖ) [ ⟦ ρ ⟧ˢ ]                   ∎
  where
```

The most interesting case is the one above, for existential
quantification, where we use Beck-Chevalley applied to the pullback
square

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  {\Gamma, x :\tau} \&\& {\Delta, x : \tau} \\
  \\
  \Gamma \&\& \Delta
  \arrow["{\pi_1}"', from=1-1, to=3-1]
  \arrow["{\rho, x}", from=1-1, to=1-3]
  \arrow["{\pi_1}", from=1-3, to=3-3]
  \arrow["\rho"', from=3-1, to=3-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

to commute

$$
\exists_{\pi_1} (\phi [ \rho\pi_1 , \pi_2 ]) = (\exists_{\pi_1} \phi) [ \rho ]
$$

<!--
```agda
    open is-pullback
    rem₁ : is-pullback B (π₁ {b = ⟦ τ ⟧ᵗ}) ⟦ ρ ⟧ˢ ⟨ ⟦ ρ ⟧ˢ ∘ π₁ , π₂ ⟩ π₁
    rem₁ .square = sym π₁∘⟨⟩
    rem₁ .universal {p₁' = p₁'} {p₂'} prf = ⟨ p₁' , π₂ ∘ p₂' ⟩
    rem₁ .p₁∘universal = π₁∘⟨⟩
    rem₁ .p₂∘universal {p = p} =
        ⟨⟩∘ _
      ·· ap₂ ⟨_,_⟩ (pullr π₁∘⟨⟩ ∙ p) π₂∘⟨⟩
      ·· sym (⟨⟩∘ _)
      ∙ eliml (sym (⟨⟩-unique id (idr _) (idr _)))
    rem₁ .unique q r = ⟨⟩-unique _ q (sym (ap (π₂ ∘_) (sym r) ∙ pulll π₂∘⟨⟩))
```
-->

```agda
sub-prop-correct ρ (pred P t) =
  ap₂ _[_] refl (sub-tm-correct ρ t) ∙ sym (subst-∘ _ _)

sub-prop-correct ρ (s =ᵖ t) =
  exists ⟨ id , id ⟩ aye [ ⟨ ⟦ sub-tm ρ s ⟧ᵉ , ⟦ sub-tm ρ t ⟧ᵉ ⟩ ]
    ≡⟨ ap₂ _[_] refl (ap₂ ⟨_,_⟩ (sub-tm-correct ρ s) (sub-tm-correct ρ t)) ⟩
  exists ⟨ id , id ⟩ aye [ ⟨ ⟦ s ⟧ᵉ ∘ ⟦ ρ ⟧ˢ , ⟦ t ⟧ᵉ ∘ ⟦ ρ ⟧ˢ ⟩ ]
    ≡⟨ ap₂ _[_] refl (sym (⟨⟩∘ _)) ⟩
  exists ⟨ id , id ⟩ aye [ ⟨ ⟦ s ⟧ᵉ , ⟦ t ⟧ᵉ ⟩ ∘ ⟦ ρ ⟧ˢ ]
    ≡⟨ sym (subst-∘ _ _) ⟩
  (exists ⟨ id , id ⟩ aye [ ⟨ ⟦ s ⟧ᵉ , ⟦ t ⟧ᵉ ⟩ ]) [ ⟦ ρ ⟧ˢ ]
    ∎
```

<!--
```agda
sub-prop-∘
  : ∀ {Φ} (ρ : Sub Γ Δ) (σ : Sub Δ Φ) (φ : Formula Φ)
  → ⟦ sub-prop ρ (sub-prop σ φ) ⟧ᵖ ≡  ⟦ φ ⟧ᵖ [ ⟦ σ ⟧ˢ ∘ ⟦ ρ ⟧ˢ ]
sub-prop-∘ ρ σ φ = sub-prop-correct ρ (sub-prop σ φ)
                ·· ap (_[ ⟦ ρ ⟧ˢ ]) (sub-prop-correct σ φ)
                ·· subst-∘ _ _

private variable
  Φ Ψ φ ψ θ φ' ψ' : Formula Γ
  t t₁ s s₁ : Tm Γ τ

wk : ∀ {Γ} (φ : Formula Γ) {τ : Ty} → Formula (Γ ʻ τ)
wk φ = sub-prop (drop stop) φ
```
-->

## A sequent calculus

We now turn to the problem of proving that our interpretation above
satisfies the rules of regular logic. We will start by defining the
**entailment relation** $\phi \vDash \psi$ between _syntactic_ formulae
which is equivalent to $\sem{\phi} \le \sem{\psi}$: $\phi$ entails
$\psi$ iff $\bP$ thinks that the interpretation of $\phi$ implies that
of $\psi$.

```agda
infix 10 _⊨_

opaque
  _⊨_ : ∀ {Γ} → (φ ψ : Formula Γ) → Type ℓ'
  _⊨_ φ ψ = ⟦ φ ⟧ᵖ ≤ ⟦ ψ ⟧ᵖ

  from-entails : φ ⊨ ψ → ⟦ φ ⟧ᵖ ≤ ⟦ ψ ⟧ᵖ
  from-entails p = p

  instance
    H-Level-⊨ : ∀ {n} → H-Level (φ ⊨ ψ) (suc n)
    H-Level-⊨ = prop-instance (has-is-thin _ _)
```

<!--
```agda
private
  entails : ∀ {Γ} → (φ ψ : Formula Γ) → Type ℓ'
  entails = _⊨_
```
-->

Having defined entailment, we can now build a deductive calculus on top
of $\phi \vDash \psi$ by constructing combinators corresponding to each
proof rule. Most of the proofs are formalised straightforwardly, so we
will restrict ourselves to pointing out _which_ rule is being
formalised.

<!--
```agda
opaque
  unfolding _⊨_
```
-->

The **cut rule** corresponds to transitivity of semantic entailment:

$$
\frac{\phi \vDash \psi \quad \psi \vDash \theta}{\phi \vDash \theta}\text{cut}
$$

```agda
  cut : φ ⊨ ψ
      → ψ ⊨ θ
      → φ ⊨ θ
  cut p q = ≤-trans p q
```

The **substitution rule** follows from our previous correctness lemmas:

$$
\frac{\phi \vDash \psi}{\phi[\rho] \vDash \theta[\rho]}\text{subst}
$$

```agda
  sub-entail
    : (ρ : Sub Γ Δ) {φ ψ : Formula Δ}
    → φ ⊨ ψ
    → sub-prop ρ φ ⊨ sub-prop ρ ψ
  sub-entail ρ {φ} {ψ} α =
    ⟦ sub-prop ρ φ ⟧ᵖ  P.=⟨ sub-prop-correct ρ φ ⟩
    ⟦ φ ⟧ᵖ [ ⟦ ρ ⟧ˢ ]  P.≤⟨ subst-≤ ⟦ ρ ⟧ˢ α ⟩
    ⟦ ψ ⟧ᵖ [ ⟦ ρ ⟧ˢ ]  P.=˘⟨ sub-prop-correct ρ ψ ⟩
    ⟦ sub-prop ρ ψ ⟧ᵖ  P.≤∎
```

The three **rules for conjunction** follow at once from the definition
of fibrewise meets:

<div class=mathpar>

$$
\frac{\Phi \vDash \phi \quad \Phi \vDash \psi}{\Phi \vdash \phi \land \psi}\land\text{-intro}
$$

$$
\frac{\Phi \vDash \phi \land \psi}{\Phi \vdash \phi}\land\text{-eliml}
$$

$$
\frac{\Phi \vDash \phi \land \psi}{\Phi \vdash \psi}\land\text{-elimr}
$$

</div>

```agda
  `∧-intro
    : Φ ⊨ φ
    → Φ ⊨ ψ
    → Φ ⊨ φ `∧ ψ
  `∧-intro α β = &-univ α β

  `∧-elimₗ
    : Φ ⊨ φ `∧ ψ
    → Φ ⊨ φ
  `∧-elimₗ α = ≤-trans α (fibrewise-meet.π₁ _ _)

  `∧-elimᵣ
    : Φ ⊨ φ `∧ ψ
    → Φ ⊨ ψ
  `∧-elimᵣ α = ≤-trans α (fibrewise-meet.π₂ _ _)
```

The **rules for existentials** are slightly fiddly, but they follow from
the universal properties of co/cartesian lifts and Frobenius
reciprocity:

<div class=mathpar>

$$
\frac{\Phi \vDash \exists \phi \quad \Phi \land \phi \vDash \psi}{\Phi \vDash \psi}
  \exists\text{-elim}
$$

$$
\frac{\Phi \vDash_{x} \phi[t/x]}{\Phi \vDash \exists \phi}\exists\text{-intro}
$$

</div>

```agda
  `∃-elim
    : Φ         ⊨ `∃ φ
    → wk Φ `∧ φ ⊨ wk ψ
    → Φ         ⊨ ψ

  `∃-intro
    : ∀ {Γ} {Φ ψ} {t : Tm Γ τ}
    → Φ ⊨ sub-prop (t , stop) ψ
    → Φ ⊨ `∃ ψ
```

<details>
<summary>The proofs here have a bit more "unfortunately, proof
assistants" than the others, so we'll keep them in `<details>`{.html}
too.</summary>

```agda
  `∃-elim {Φ = Φ} {φ = φ} {ψ = ψ} Φ⊢exists φ⊢ψ =
    ⟦ Φ ⟧ᵖ                              P.≤⟨ &-univ Φ⊢exists P.≤-refl ⟩
    ⟦ `∃ φ ⟧ᵖ & ⟦ Φ ⟧ᵖ                  P.=⟨ frobenius π₁ ⟩
    exists π₁ (⟦ φ ⟧ᵖ & ⟦ Φ ⟧ᵖ [ π₁ ])  P.=⟨ ap (exists π₁) &-comm ⟩
    exists π₁ (⟦ Φ ⟧ᵖ [ π₁ ] & ⟦ φ ⟧ᵖ)  P.≤⟨ φ⊢ψ' ⟩
    ⟦ ψ ⟧ᵖ                              P.≤∎
    where
    φ⊢ψ' : exists π₁ (⟦ Φ ⟧ᵖ [ π₁ ] & ⟦ φ ⟧ᵖ) ≤ ⟦ ψ ⟧ᵖ
    φ⊢ψ' = ≤-exists π₁
      (transport (ap₂ _≤_
        (ap₂ _&_ (sub-prop-correct (drop stop) Φ ∙ ap₂ _[_] refl (idl _)) refl)
        (sub-prop-correct (drop stop) ψ ∙ ap₂ _[_] refl (idl _)))
        φ⊢ψ)

  `∃-intro {Γ = Γ} {Φ = Φ} {ψ = ψ} {t = t} α = hom[ cancell π₁∘⟨⟩ ] $
         cocartesian.has-lift.lifting π₁ ⟦ ψ ⟧ᵖ
    ℙ.∘' cartesian.has-lift.lifting ⟨ id , ⟦ t ⟧ᵉ ⟩ ⟦ ψ ⟧ᵖ
    ℙ.∘' p
    where
    p : ⟦ Φ ⟧ᵖ ≤ (⟦ ψ ⟧ᵖ [ ⟨ id , ⟦ t ⟧ᵉ ⟩ ])
    p =
      ⟦ Φ ⟧ᵖ                               P.≤⟨ α ⟩
      ⟦ sub-prop (t , stop) ψ ⟧ᵖ           P.=⟨ sub-prop-correct (t , stop) ψ ⟩
      (⟦ ψ ⟧ᵖ [ ⟨ id , ⟦ t ⟧ᵉ ⟩ ])         P.≤∎
```

</details>

<!--
```agda
  =-refl : entails φ (t =ᵖ t)
  =-refl {t = t} =
    cartesian.has-lift.universal _ _ _ $ hom[ pulll (⟨⟩∘ _ ∙ ap₂ ⟨_,_⟩ (idl _) (idl _)) ] $
          cocartesian.has-lift.lifting ⟨ id , id ⟩ aye
    ℙ.∘' cartesian.has-lift.lifting _ _
    ℙ.∘' subst-! ⟦ t ⟧ᵉ
```
-->

### Local rewriting

Since we're working with a very strict *pre*syntax of formulas, there
are many distinct syntactic-formulae with identical semantics. This
strictness affords us good computational properties at the cost of
_mathematical_ properties: our syntax isn't initial in any sense.
Moreover, since the details of the entailment relation are kept `opaque`
to encourage use of the combinators above, it's not immediate to the
outside world that it respects semantic equality.

We'll remedy this in the following way: we can define an inductive
relation $t \approx s$ which includes semantic equality but also
includes combinators for "zooming in" part of a formula, ignoring the
parts that don't change, so that we can deploy semantic equality at
precisely the place where it matters. Then, we provide combinators
witnessing that the entailment $\phi \vDash \psi$ respects $\approx$.

```agda
data _≈ᵗ_ : Tm Γ τ → Tm Γ τ → Typeω where
  sem : ⟦ t ⟧ᵉ ≡ ⟦ s ⟧ᵉ → t ≈ᵗ s
  _,_ : t ≈ᵗ t₁ → s ≈ᵗ s₁ → (t , s) ≈ᵗ (t₁ , s₁)
  `π₁ : t ≈ᵗ t₁ → `π₁ t ≈ᵗ `π₁ t₁
  `π₂ : t ≈ᵗ t₁ → `π₂ t ≈ᵗ `π₂ t₁
  fun : ∀ {h : Hom ⟦ τ ⟧ᵗ ⟦ σ ⟧ᵗ} {t t₁ : Tm Γ τ}
      → t ≈ᵗ t₁
      → fun {τ = τ} {σ} h t ≈ᵗ fun h t₁

data _≈ᵖ_ : Formula Γ → Formula Γ → Typeω where
  sem  : ⟦ φ ⟧ᵖ ≡ ⟦ ψ ⟧ᵖ → φ ≈ᵖ ψ
  _`∧_ : φ ≈ᵖ φ' → ψ ≈ᵖ ψ' → (φ `∧ ψ) ≈ᵖ (φ' `∧ ψ')
  `∃   : φ ≈ᵖ ψ → `∃ φ ≈ᵖ `∃ ψ
  pred : ∀ {p} → t ≈ᵗ t₁ → pred p t ≈ᵖ pred p t₁
  _=ᵖ_ : ∀ {Γ τ} {t t₁ s s₁ : Tm Γ τ}
        → t ≈ᵗ t₁ → s ≈ᵗ s₁ → (t =ᵖ s) ≈ᵖ (t₁ =ᵖ s₁)
```

The data types above are simply presentations of semantic equality: $t
\approx s$ iff. $\sem{t} = \sem{s}$. However, $t \approx s$ once again
contains redundancy which is mathematically irrelevant but handy when
working in a proof assistant.

```agda
to-semᵗ : t ≈ᵗ t₁ → ⟦ t ⟧ᵉ ≡ ⟦ t₁ ⟧ᵉ
to-semᵗ (sem p) = p
to-semᵗ (p , q) = ap₂ ⟨_,_⟩ (to-semᵗ p) (to-semᵗ q)
to-semᵗ (`π₁ p) = ap₂ _∘_ refl (to-semᵗ p)
to-semᵗ (`π₂ p) = ap₂ _∘_ refl (to-semᵗ p)
to-semᵗ (fun p) = ap₂ _∘_ refl (to-semᵗ p)

to-semᵖ : φ ≈ᵖ ψ → ⟦ φ ⟧ᵖ ≡ ⟦ ψ ⟧ᵖ
to-semᵖ (sem p)  = p
to-semᵖ (p `∧ q) = ap₂ _&_ (to-semᵖ p) (to-semᵖ q)
to-semᵖ (`∃ p)   = ap (exists π₁) (to-semᵖ p)
to-semᵖ (pred p) = ap₂ _[_] refl (to-semᵗ p)
to-semᵖ (_=ᵖ_ {Γ = Γ} {τ = τ} p q) = ap₂ equ (to-semᵗ p) (to-semᵗ q) where
  equ : ∀ (h h' : Hom ⟦ Γ ⟧ᶜ ⟦ τ ⟧ᵗ) → ℙ.Ob[ ⟦ Γ ⟧ᶜ ]
  equ h h' = exists ⟨ id , id ⟩ aye [ ⟨ h , h' ⟩ ]
```

We can then provide combinators for turning $\phi \approx \psi$ into
$\phi \vDash \psi$, or $\psi \vDash \phi$, as appropriate.

```agda
opaque
  unfolding _⊨_

  ≈→entails : φ ≈ᵖ ψ → entails φ ψ
  ≈→entails p = transport (ap₂ _≤_ refl (to-semᵖ p)) P.≤-refl

  ≈→entails⁻ : φ ≈ᵖ ψ → entails ψ φ
  ≈→entails⁻ p = transport (ap₂ _≤_ refl (sym (to-semᵖ p))) P.≤-refl
```

<!--
```agda
_⊢⟨_⟩_ : ∀ φ → φ ⊨ ψ → ψ ⊨ θ → φ ⊨ θ
_⊢⟨_⟩_ _ p q = cut p q

_≈⟨_⟩_ : ∀ φ → φ ≈ᵖ ψ → ψ ⊨ θ → φ ⊨ θ
_≈⟨_⟩_ _ p q = cut (≈→entails p) q

_≈˘⟨_⟩_ : ∀ φ → ψ ≈ᵖ φ → ψ ⊨ θ → φ ⊨ θ
_≈˘⟨_⟩_ _ p q = cut (≈→entails⁻ p) q

opaque
  unfolding _⊨_

  _⊢∎ : (φ : Formula Γ) → φ ⊨ φ
  _⊢∎ φ = P.≤-refl {_} {⟦ φ ⟧ᵖ}

infixr 2 _≈⟨_⟩_ _≈˘⟨_⟩_ _⊢⟨_⟩_
infix  3 _⊢∎
```
-->
