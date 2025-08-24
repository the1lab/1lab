<!--
```agda
open import 1Lab.HLevel.Closure
open import 1Lab.Prelude

open import Data.String.Base
open import Data.Maybe
open import Data.Bool
open import Data.List
open import Data.Dec
open import Data.Nat
open import Data.Sum
```
-->

```agda
module Lang.STLC.Named where
```

# The simply-typed lambda calculus

The simply-typed lambda calclus (STLC) is an example of one of the smallest
"useful" typed programming languages. While very simple, and lacking
features that would make it useful for real programming, its small
size makes it very appealing for the demonstration of programming
language formalization.

This file represents the first in a series, exploring several
different approaches to formalizing various properties of the STLC.
We will start with the most "naive" approach, and build off it to
more advanced approaches.

First, the types of the STLC: the Unit type, products, and functions.
We will use `Ty`{.Agda} to denote these, although `Tp` is also commonly used.

```agda
data Ty : Type where
  `⊤ : Ty
  _`×_ : Ty → Ty → Ty
  _`⇒_ : Ty → Ty → Ty
```

We model contexts as (snoc) lists of pairs, alongside a partial
index function. We use `∷c`{.Agda} as the "reversed" list constructor
to avoid confusion about insertion order.
Sequels to this file will use more advanced techniques to avoid
this partiality, but it's alright for right now.

```agda
Ctx : Type
Ctx = List (String × Ty)
```

<!--
```agda
infixl 10 _∷c_
pattern _∷c_ Γ x = x ∷ Γ
```
-->

We also note some minor lemmas around lookup:

```agda
lookup-immediate : ∀ {Γ} {n : String} {t : Ty} → lookup n (Γ ∷c (n , t)) ≡ just t
lookup-duplicate
  : ∀ {Γ} {n : String} {k} {t₁ t₂ : Ty} {ρ}
  → lookup k (Γ ∷c (n , t₁)) ≡ just ρ
  → lookup k ((Γ ∷c (n , t₂)) ∷c (n , t₁)) ≡ just ρ
```

<details>

```agda
lookup-immediate {Γ} {n} {t} = refl
lookup-duplicate {Γ} {n} {k} {t₁} {t₂} {ρ} eq with k ≡? n
... | yes k≡n = eq
... | no ¬k≡n with k ≡? n
... | yes k≡n = absurd (¬k≡n k≡n)
... | no ¬k≡n = eq
```
</details>


Then, expressions: we have variables, functions and application,
pairs and projections, and the unit.

```agda
data Expr : Type where
  ` : String → Expr
  `λ : String → Expr → Expr
  _`$_ : Expr → Expr → Expr
  `⟨_,_⟩ :  Expr → Expr → Expr
  `π₁ : Expr → Expr
  `π₂ : Expr → Expr
  `tt : Expr
```

<details><summary>Some injectivity lemmas, for convenience.

```agda
`-inj : ∀ {a b} → ` a ≡ ` b → a ≡ b
`λ-inj : ∀ {x y a b} → `λ x a ≡ `λ y b → (x ≡ y) × (a ≡ b)
`$-inj : ∀ {f g x y} → f `$ x ≡ g `$ y → (f ≡ g) × (x ≡ y)
`⟨⟩-inj : ∀ {x y a b} → `⟨ x , y ⟩ ≡ `⟨ a , b ⟩ → (x ≡ a) × (y ≡ b)
`π₁-inj : ∀ {a b} → `π₁ a ≡ `π₁ b → a ≡ b
`π₂-inj : ∀ {a b} → `π₂ a ≡ `π₂ b → a ≡ b
```
</summary>

```agda
`-inj x = ap h x where
  h : Expr → String
  h (` x) = x
  h _ = ""

`λ-inj x = ap h x , ap g x where
  h : Expr → String
  h (`λ x _) = x
  h _ = ""

  g : Expr → Expr
  g (`λ _ b) = b
  g _ = `tt

`$-inj x = ap h x , ap g x where
  h : Expr → Expr
  h (a `$ _) = a
  h _ = `tt

  g : Expr → Expr
  g (_ `$ b) = b
  g _ = `tt

`⟨⟩-inj x = ap h x , ap g x where
  h : Expr → Expr
  h (`⟨ a , _ ⟩) = a
  h _ = `tt

  g : Expr → Expr
  g (`⟨ _ , b ⟩) = b
  g _ = `tt

`π₁-inj x = ap h x where
  h : Expr → Expr
  h (`π₁ x) = x
  h _ = `tt

`π₂-inj x = ap h x where
  h : Expr → Expr
  h (`π₂ x) = x
  h _ = `tt
```

</details>

We must then define a relation to assign types to expressions, which
we will notate `Γ ⊢ tm ⦂ ty`{.Agda}, for "a term $\rm{tm}$ has type $\rm{ty}$
in the context $\Gamma$":

<!--
```agda
infix 3 _⊢_⦂_
```
-->

```agda
data _⊢_⦂_ : Ctx → Expr → Ty → Type where
```

We say that a variable $n$ has a type $\tau$ in context $\Gamma$
if `lookup Γ n ≡ just τ`{.Agda}.

```agda
  `var-intro
    : ∀ {Γ τ} (n : String)
    → lookup n Γ ≡ just τ
    → Γ ⊢ ` n ⦂ τ
```

For lambda abstraction, if an expression $\text{body}$ extended with a variable $v$
of type $\tau$ has type $\rho$, we say that $λ\, v.\,\text{body}$ has type
$\tau \to \rho$. We call this constructor `\`⇒-intro`{.Agda} as it "introduces"
the arrow type.

```agda
  `⇒-intro : ∀ {Γ n body τ ρ} →
        Γ ∷c (n , τ) ⊢ body ⦂ ρ →
        Γ ⊢ `λ n body ⦂ τ `⇒ ρ
```

If an expression $f$ has type $\tau \to \rho$, and
an expression $x$ has type $\tau$, then the application $f\, x$ (written here as $\$ f x$) has type $\rho$.

We name it `\`⇒-elim`{.Agda} as it "eliminates" the arrow type.

```agda
  `⇒-elim : ∀ {Γ f x τ ρ} →
        Γ ⊢ f ⦂ τ `⇒ ρ →
        Γ ⊢ x ⦂ τ →
        Γ ⊢ f `$ x ⦂ ρ
```

The rest of the formers follow these patterns:

```agda
  `×-intro : ∀ {Γ a b τ ρ} →
          Γ ⊢ a ⦂ τ →
          Γ ⊢ b ⦂ ρ →
          Γ ⊢ `⟨ a , b ⟩ ⦂ τ `× ρ

  `×-elim₁ :  ∀ {Γ a τ ρ} →
          Γ ⊢ a ⦂ τ `× ρ →
          Γ ⊢ `π₁ a ⦂ τ

  `×-elim₂ :  ∀ {Γ a τ ρ} →
          Γ ⊢ a ⦂ τ `× ρ →
          Γ ⊢ `π₂ a ⦂ ρ

  `tt-intro :   ∀ {Γ} →
          Γ ⊢ `tt ⦂ `⊤
```

This completes our typing relation. We can now show that some given
program has some given type, for example:

<!--
```agda
private module Example-1 where
```
-->

```agda
  const : Expr
  const = `λ "x" (`λ "y" (` "x"))

  const-is-`⊤⇒`⊤⇒`⊤ : [] ⊢ const ⦂ `⊤ `⇒ (`⊤ `⇒ `⊤)
  const-is-`⊤⇒`⊤⇒`⊤ = `⇒-intro (`⇒-intro (`var-intro "x" refl))
```

The astute amongst you may note that the typing derivation looks
suspiciously similar to the term itself - this will be explored later
in the series.

Now we will take a slight detour, and define what it means for
an expression to be a **value**. This will come in useful in a second!
For right now, we note that a value is something that cannot be
reduced further - in our case, variables, lambda abstractions, pairs,
and unit.

```agda
data is-value : Expr → Type where
  v-λ : ∀ {n body} → is-value (`λ n body)
  v-⟨,⟩ : ∀ {a b} → is-value (`⟨ a , b ⟩)
  v-⊤ : is-value `tt
```

Our next goal is to now define a "step" relation,
which dictates that a term $x$ may, through a reduction, step to
another expression $x'$ that represents one "step" of evaluation.

This is how we will
define the evaluation of our expressions. Before we can define
stepping, we need to define substitution, so that we may turn an
expression like $(\lambda x. f\,x) y$ into $f\,y$. We notate the
substitution of a variable $n$ for an expression $e$ in another
expression $f$ as `f [ n := e ]`{.Agda}. It's worth noting that the
substitution we implement is actually not correct in general, due to
a problem called variable capture.

<!--
```agda
infix 2 _[_:=_]
```
-->

```agda
_[_:=_] : Expr → String → Expr → Expr
```

If a variable x is equal to the variable we are substituting for, n,
we return the new expression. Else, the variable unchanged.

```agda
` x [ n := e ] with x ≡? n
... | yes _ = e
... | no _ = ` x
```

This substitution is not capture avoiding. This causes issues if
the terms are not alpha distinct!

```agda
`λ x f [ n := e ] with x ≡? n
... | yes _ = `λ x f
... | no _ = `λ x (f [ n := e ])
```

In all other cases, we simply "move" the substitution into all
subexpressions. (Or, do nothing.)

```agda
f `$ x [ n := e ] = (f [ n := e ]) `$ (x [ n := e ])
`⟨ a , b ⟩ [ n := e ] = `⟨ a [ n := e ] , b [ n := e ] ⟩
`π₁ a [ n := e ] = `π₁ (a [ n := e ])
`π₂ a [ n := e ] = `π₂ (a [ n := e ])
`tt [ n := e ] = `tt
```

Now, we define our step relation proper. Each of these step relations
is properly referred to as a "reduction rule".

```agda
data _↦_ : Expr → Expr → Type where
```

The act of turning an application $(λ\,y. y)\,x$ into $x$ is called
β-reduction for lambda terms. We require $x$ to be a value in order
to keep reduction deterministic -- this will be elaborated on in
a moment.

```agda
  β-λ : ∀ {n body x} →
        is-value x →
        ((`λ n body) `$ x) ↦ (body [ n := x ])
```

Likewise, reducing projections on a pair is called β-reduction for
pairs.

```agda
  β-π₁ : ∀ {a b} →
       (`π₁ `⟨ a , b ⟩) ↦ a
  β-π₂ : ∀ {a b} →
       (`π₂ `⟨ a , b ⟩) ↦ b
```

We also have two reductions that can step "inside" projections, which
we will call ξ rules.

```agda
  ξ-π₁ : ∀ {a₁ a₂} →
       a₁ ↦ a₂ →
       (`π₁ a₁) ↦ (`π₁ a₂)

  ξ-π₂ : ∀ {a₁ a₂} →
       a₁ ↦ a₂ →
       (`π₂ a₁) ↦ (`π₂ a₂)
```

Likewise, we have one that can step inside an application, on
the left hand side.

```agda
  ξ-$ₗ : ∀ {f₁ f₂ x} →
       f₁ ↦ f₂ →
       (f₁ `$ x) ↦ (f₂ `$ x)
```

We also include a rule for reduction on the right hand side, requiring
the left to be a value first. This, combined with the value requirement
of the `β-λ`{.Agda} rule, keep our evaluation **deterministic**, forcing
that evaluation should take place from left to right. We will prove
this later.

```agda
  ξ-$ᵣ : ∀ {f x₁ x₂} →
       is-value f →
       x₁ ↦ x₂ →
       (f `$ x₁) ↦ (f `$ x₂)
```

These are all of our reduction rules! The STLC is indeed very simple.
We can now show that, say, an identity function applied to something
reduces properly:

<!--
```agda
private module Example-2 where
```
-->

```agda
  our-id : Expr
  our-id = `λ "x" (` "x")

  pair : Expr
  pair = `⟨ `tt , `tt ⟩

  id-app-step : (our-id `$ pair) ↦ pair
  id-app-step = β-λ v-⟨,⟩
```

<!-- [TODO: Wren, 13/06/2025]  Refl Trans closure of _↦_ -->

## The big two properties

The two "big" properties about the STLC we wish to prove are called
**progress** and **preservation**. Progress states that any
given term is either done (a value), or can take another step.
Preservation states that if a well typed expression $x$ reduces to another $x'$,
they have the same type (i.e., reduction preserves types.)

The first step in proving these is showing that a "proper" substitution
preserves types. If a term $tm$ has type $\tau$ when extended
with a variable $n$ of type $\rho$, then substituting any expression
of type $\rho$ for $n$ preserves the type of $tm$. To prove this,
we first show that renaming preserves types - if $\Gamma$ and $\Delta$
are contexts, and for every lookup in $\Gamma$, $\Delta$ gives the
same type, then any term with a type under $\Gamma$ has the same
type under $\Delta$.

```agda
rename
  : ∀ {Γ Δ}
  → (∀ n ty → lookup n Γ ≡ just ty → lookup n Δ ≡ just ty)
  → ∀ tm ty → Γ ⊢ tm ⦂ ty → Δ ⊢ tm ⦂ ty
```

Variables are fairly straightforward - we simply apply our renaming
function.

```agda
rename {Γ} {Δ} f (` x) ty (`var-intro .x n) = `var-intro x (f x ty n)
```

Lambda abstractions are more complex - we need to extend our renaming
function to encompass the new abstraction.

```agda
rename {Γ} {Δ} f (`λ x tm) ty (`⇒-intro {τ = τ} {ρ = ρ} Γ⊢) = `⇒-intro (rename f' tm ρ Γ⊢)
  where
    f' : (n : String) (ty : Ty) →
          lookup n (Γ ∷c (x , τ)) ≡ just ty →
          lookup n (Δ ∷c (x , τ)) ≡ just ty
    f' n ty Γ≡ with n ≡? x
    ... | yes x≡n = Γ≡
    ... | no p = f n ty Γ≡
```

Everything else is straightforward, as in the substitution case.

```agda
rename {Γ} {Δ} f (f' `$ x) ty (`⇒-elim {τ = τ} Γ⊢₁ Γ⊢₂) =
  `⇒-elim (rename f f' (τ `⇒ ty) Γ⊢₁) (rename f x τ Γ⊢₂)

rename {Γ} {Δ} f `⟨ a , b ⟩ ty (`×-intro {τ = τ} {ρ = ρ} Γ⊢₁ Γ⊢₂) =
  `×-intro (rename f a τ Γ⊢₁) (rename f b ρ Γ⊢₂)

rename {Γ} {Δ} f (`π₁ tm) ty (`×-elim₁ {ρ = ρ} Γ⊢) = `×-elim₁ (rename f tm (ty `× ρ) Γ⊢)
rename {Γ} {Δ} f (`π₂ tm) ty (`×-elim₂ {τ = τ} Γ⊢) = `×-elim₂ (rename f tm (τ `× ty) Γ⊢)
rename {Γ} {Δ} f `tt ty `tt-intro = `tt-intro
```

Another few lemmas! This time about shuffling and dropping names
in the context.

```agda
duplicates-are-ok
  : ∀ {Γ n t₁ t₂ bd typ}
  → Γ ∷c (n , t₂) ∷c (n , t₁) ⊢ bd ⦂ typ
  → Γ ∷c (n , t₁) ⊢ bd ⦂ typ
variable-swap
  : ∀ {Γ n k t₁ t₂ bd typ}
  → ¬ n ≡ k
  → Γ ∷c (n , t₁) ∷c (k , t₂) ⊢ bd ⦂ typ
  → Γ ∷c (k , t₂) ∷c (n , t₁) ⊢ bd ⦂ typ
```

<details>

```agda
variable-swap {Γ} {n} {k} {t₁} {t₂} {x} {typ} ¬n≡k Γ⊢ = rename f x typ Γ⊢
  where
    f : (z : String) (ty : Ty) →
         lookup z (Γ ∷c (n , t₁) ∷c (k , t₂)) ≡ just ty →
         lookup z (Γ ∷c (k , t₂) ∷c (n , t₁)) ≡ just ty
    f z ty x with z ≡? n in eq
    ... | no ¬z≡n = h
      where
        h : (lookup z (Γ ∷c (k , t₂))) ≡ just ty
        h with z ≡? k
        ... | yes z≡k = x
        ... | no ¬z≡k with z ≡? n
        ... | no ¬z≡n = x
    ... | yes z≡n with z ≡? k
    ... | yes z≡k = absurd (¬n≡k (sym z≡n ∙ z≡k))
    ... | no ¬z≡k with z ≡? n
    ... | yes z≡n = x
    ... | no ¬z≡n = absurd (¬z≡n z≡n)

duplicates-are-ok {Γ} {n} {t₁} {t₂} {bd} {typ} Γ⊢ =
  rename f bd typ Γ⊢
  where
    f : (k : String) (ty : Ty) →
         lookup k (Γ ∷c (n , t₂) ∷c (n , t₁)) ≡ just ty →
         lookup k (Γ ∷c (n , t₁)) ≡ just ty
    f k ty x with k ≡? n
    ... | yes k≡n = x
    ... | no ¬k≡n with k ≡? n
    ... | yes k≡n = absurd (¬k≡n k≡n)
    ... | no ¬k≡n = x
```
</details>

We need one additional important lemma - weaking. It says that if a term has a
type in the empty context, it also has that type in any other context.
This turns out to be a special case of renaming, where we get an
absurdity from considering that `lookup [] n ≡ just τ`{.Agda}, for any $n$
and $\tau$.

```agda
weakening
  : ∀ {Γ tm ty}
  → [] ⊢ tm ⦂ ty
  → Γ  ⊢ tm ⦂ ty
weakening {Γ} {tm} {ty} []⊢ = rename f tm ty []⊢
  where
    f : (n : String) (τ : Ty) → lookup n [] ≡ just τ → lookup n Γ ≡ just τ
    f _ _ x = absurd (nothing≠just x)
```

Now with renaming under our belt, we can prove substitution proper
preserves types. Note that the substitute's type must exist in
the empty context, to prevent conflicts of variables.

```agda
subst-pres
  : ∀ {Γ n t bd typ s}
  → [] ⊢ s ⦂ t
  → Γ ∷c (n , t) ⊢ bd ⦂ typ
  → Γ ⊢ bd [ n := s ] ⦂ typ
```

In the case of variables, we use weakening for the substitution itself,
to embed our term `s`{.Agda} into the context $\Gamma$.

```agda
subst-pres {Γ} {n} {t} {` x} {typ} {s} s⊢ (`var-intro .x k) with x ≡? n
... | yes _ = weakening (subst (λ ρ → [] ⊢ s ⦂ ρ) (just-inj k) s⊢)
... | no _  = `var-intro x k
```

Lambda abstraction is once again slightly annoying. Handling the case
where the names are equal requires some removing of duplicates in the
context, and where they are not equal requires some shuffling.

```agda
subst-pres {Γ} {n} {t} {`λ x bd} {typ} {s} s⊢ (`⇒-intro {τ = τ} {ρ = ρ} Γ⊢) with x ≡? n
... | yes x≡n = `⇒-intro (duplicates-are-ok
                      (subst (λ _ → Γ ∷c _ ∷c _ ⊢ bd ⦂ ρ) (sym x≡n) Γ⊢))
... | no ¬x≡n = `⇒-intro (subst-pres s⊢ (variable-swap (λ x≡n → ¬x≡n (sym x≡n)) Γ⊢))
```

The rest proceeds nicely.

```agda
subst-pres {Γ} {n} {t} {f `$ x} {typ} {s} s⊢ (`⇒-elim Γ⊢₁ Γ⊢₂) =
  `⇒-elim (subst-pres s⊢ Γ⊢₁) (subst-pres s⊢ Γ⊢₂)

subst-pres {Γ} {n} {t} {`⟨ a , b ⟩} {typ} {s} s⊢ (`×-intro Γ⊢₁ Γ⊢₂) =
  `×-intro (subst-pres s⊢ Γ⊢₁) (subst-pres s⊢ Γ⊢₂)

subst-pres {Γ} {n} {t} {`π₁ bd} {typ} {s} s⊢ (`×-elim₁ Γ⊢) = `×-elim₁ (subst-pres s⊢ Γ⊢)
subst-pres {Γ} {n} {t} {`π₂ bd} {typ} {s} s⊢ (`×-elim₂ Γ⊢) = `×-elim₂ (subst-pres s⊢ Γ⊢)
subst-pres {Γ} {n} {t} {`tt} {typ} {s} s⊢ `tt-intro = `tt-intro
```

We'll do preservation first, which follows very easily from the
lemmas we've already defined:

```agda
preservation
  : ∀ {x₁ x₂ typ}
  → x₁ ↦ x₂
  → [] ⊢ x₁ ⦂ typ
  → [] ⊢ x₂ ⦂ typ

preservation (β-λ p) (`⇒-elim (`⇒-intro ⊢f) ⊢x) = subst-pres ⊢x ⊢f
preservation β-π₁ (`×-elim₁ (`×-intro ⊢a ⊢b)) = ⊢a
preservation β-π₂ (`×-elim₂ (`×-intro ⊢a ⊢b)) = ⊢b
preservation (ξ-π₁ step) (`×-elim₁ ⊢a) = `×-elim₁ (preservation step ⊢a)
preservation (ξ-π₂ step) (`×-elim₂ ⊢b) = `×-elim₂ (preservation step ⊢b)
preservation (ξ-$ₗ step) (`⇒-elim ⊢f ⊢x) = `⇒-elim (preservation step ⊢f) ⊢x
preservation (ξ-$ᵣ val step) (`⇒-elim ⊢f ⊢x) = `⇒-elim ⊢f (preservation step ⊢x)
```

Then, progress, noting that the expression must be well typed. We
define progress as a datatype, as it's much nicer to work with.

```agda
data Progress (M : Expr) : Type where
  going : ∀ {N} → M ↦ N → Progress M
  done : is-value M → Progress M
```

Then, progress reduces to mostly a lot of case analysis.

```agda
progress : ∀ {x ty} → [] ⊢ x ⦂ ty → Progress x
progress (`var-intro n n∈) = absurd (nothing≠just n∈)
progress (`⇒-intro {n = n} {body = body} ⊢x) = done v-λ
progress (`⇒-elim ⊢f ⊢x) with progress ⊢f
... | going next-f = going (ξ-$ₗ next-f)
... | done vf with progress ⊢x
... |   going next-x = going (ξ-$ᵣ vf next-x)
... |   done vx with ⊢f
... |     `var-intro n n∈ = absurd (nothing≠just n∈)
... |     `⇒-intro f = going (β-λ vx)

progress (`×-intro {a = a} {b = b} ⊢a ⊢b) = done v-⟨,⟩
progress (`×-elim₁ {a = a} ⊢x) with progress ⊢x
... | going next = going (ξ-π₁ next)
... | done v-⟨,⟩ = going β-π₁

progress (`×-elim₂ ⊢x) with progress ⊢x
... | going next = going (ξ-π₂ next)
... | done v-⟨,⟩ = going β-π₂

progress `tt-intro = done v-⊤
```

There's our big two properties! As promised, we'll also now prove
that our step relation is deterministic -- there is only one
step that can be applied at any given time. This is also equivalent
to saying that if some term $x$ steps to $x_{1}$ and also to $x_{2}$,
then $x_{1} ≡ x_{2}$.

We do this with the help of a lemma that states values do not step to
anything.

```agda
value-¬reduce : ∀ {x y} → is-value x → ¬ (x ↦ y)
```

<details>
```agda
value-¬reduce v-λ ()
value-¬reduce v-⟨,⟩ ()
value-¬reduce v-⊤ ()
```
</details>

Finally we can show that reduction in a closed context is deterministic.
While it is possible to show that reduction in any context is deterministic,
this named STLC is not very pleasant to work with, and so this will be
shown in the next part.

```agda
deterministic
  : ∀ {x ty x₁ x₂}
  → [] ⊢ x ⦂ ty
  → x ↦ x₁
  → x ↦ x₂
  → x₁ ≡ x₂

deterministic (`⇒-elim ⊢f ⊢x) (β-λ vx₁) (β-λ vx₂) = refl
deterministic (`⇒-elim ⊢f ⊢x) (β-λ vx) (ξ-$ᵣ x b) = absurd (value-¬reduce vx b)
deterministic (`⇒-elim ⊢f ⊢x) (ξ-$ₗ →x₁) (ξ-$ₗ →x₂) =
  ap₂ _`$_ (deterministic ⊢f →x₁ →x₂) refl

deterministic (`⇒-elim ⊢f ⊢x) (ξ-$ₗ →x₁) (ξ-$ᵣ vx →x₂) = absurd (value-¬reduce vx →x₁)
deterministic (`⇒-elim ⊢f ⊢x) (ξ-$ᵣ vx₁ →x₁) (β-λ vx₂) = absurd (value-¬reduce vx₂ →x₁)
deterministic (`⇒-elim ⊢f ⊢x) (ξ-$ᵣ vx →x₁) (ξ-$ₗ →x₂) = absurd (value-¬reduce vx →x₂)
deterministic (`⇒-elim ⊢f ⊢x) (ξ-$ᵣ _ →x₁) (ξ-$ᵣ _ →x₂) =
  ap₂ _`$_ refl (deterministic ⊢x →x₁ →x₂)

deterministic (`×-elim₁ ⊢x) β-π₁ β-π₁ = refl
deterministic (`×-elim₁ ⊢x) (ξ-π₁ →x₁) (ξ-π₁ →x₂) = ap `π₁ (deterministic ⊢x →x₁ →x₂)
deterministic (`×-elim₂ ⊢x) β-π₂ β-π₂ = refl
deterministic (`×-elim₂ ⊢x) (ξ-π₂ →x₁) (ξ-π₂ →x₂) = ap `π₂ (deterministic ⊢x →x₁ →x₂)
```

It is also possible to prove that the evaluation of the simply typed lambda calculus
always terminates. (In other words, for any well-typed term $x$, there exist some $v$
such that there is a chain $x \mapsto x₁ \mapsto \cdots \mapsto v$, and $\text{is-value} v$).
However, this named representation is enough of a pain to work with as-is, so this
will be proven later.
