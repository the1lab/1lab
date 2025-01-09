<!--
```agda
open import 1Lab.Path
open import 1Lab.Type

open import Data.Maybe
open import Data.Bool
open import Data.List
open import Data.Dec
open import Data.Nat
open import Data.Sum
```
-->

```agda
module ProgrammingLanguage.STLC.Simple where
```

# The simply-typed lambda calculus

The simple-typed lamdba calclus (STLC) is an example of one of the smallest
"useful" typed programming languages. While very simple, and lacking
features that would make it useful for real programming, its small
size makes it very appealing for the demonstration of programming
language formalization.

This file represents the first in a series, exploring several
different approaches to formalizing various properties of the STLC.
We will start with the most "naive" approach, and build off it to
more advanced approaches.

First, the types of the STLC: the Unit type, products, and functions.

```agda
data Ty : Type where
  UU : Ty
  _`×_ : Ty → Ty → Ty
  _`⇒_ : Ty → Ty → Ty
```

We model contexts as (snoc) lists of pairs, alongside a partial
index function. We use `∷c`{.Agda} as the "reversed" list constructor
to avoid confusion about insertion order.
Sequels to this file will use more advanced techniques to avoid
this partiality, but it's alright for right now.

```agda
Con : Type
Con = List (Nat × Ty)
```

<!--
```agda
infixl 10 _∷c_
pattern _∷c_ Γ x = x ∷ Γ
```
-->

```agda
index : Con → Nat → Maybe Ty
index [] _ = nothing
index (Γ ∷c (n , ty)) k with k ≡? n
... | yes _ = just ty
... | no _ = index Γ k
```

We also note some minor lemmas around indexing:
```agda
index-immediate : ∀ {Γ n t} → index (Γ ∷c (n , t)) n ≡ just t
index-duplicate : ∀ {Γ n k t₁ t₂ ρ} →
                  index (Γ ∷c (n , t₁)) k ≡ just ρ →
                  index ((Γ ∷c (n , t₂)) ∷c (n , t₁)) k ≡ just ρ
```
<details>
```agda
index-immediate {Γ} {n} {t} with n ≡? n
... | yes n≡n = refl
... | no ¬n≡n = absurd (¬n≡n refl)

index-duplicate {Γ} {n} {k} {t₁} {t₂} {ρ} eq with k ≡? n
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
  ` : Nat → Expr
  `λ : Nat → Expr → Expr
  `$ : Expr → Expr → Expr
  `⟨_,_⟩ :  Expr → Expr → Expr
  `π₁ : Expr → Expr
  `π₂ : Expr → Expr
  `U : Expr
```

<details><summary>Some application lemmas, for convinience.</summary>
```agda
`$-apₗ : ∀ {a b x} → a ≡ b → `$ a x ≡ `$ b x
`$-apᵣ : ∀ {f a b} → a ≡ b → `$ f a ≡ `$ f b

`$-apₗ {x = x} a≡b = ap (λ k → `$ k x) a≡b
`$-apᵣ {f = f} a≡b = ap (λ k → `$ f k) a≡b
```
</details>

We must then define a relation to assign types to expressions, which
we will notate `Γ ⊢ tm ⦂ ty`{.Agda}, for "a term $tm$ has type $ty$
in the context $\Gamma$":

<!--
```agda
infix 3 _⊢_⦂_
```
-->

```agda
data _⊢_⦂_ : Con → Expr → Ty → Type where
```

We say that a variable $n$ has a type $\tau$ in context $\Gamma$
if `index Γ n ≡ just τ`{.Agda}.

```agda
  `⊢ : ∀ {Γ τ} (n : Nat) →
       index Γ n ≡ just τ →
       Γ ⊢ ` n ⦂ τ
```

For lambda abstraction, if an expression $\text{body}$ extended with a variable $v$
of type $\tau$ has type $\rho$, we say that $λ\, v.\,\text{body}$ has type
$\tau \to \rho$.

```agda
  `λ⊢ : ∀ {Γ n body τ ρ} →
        Γ ∷c (n , τ) ⊢ body ⦂ ρ →
        Γ ⊢ `λ n body ⦂ τ `⇒ ρ
```

If an expression $f$ has type $\tau \to \rho$, and
an expression $x$ has type $\tau$, then the application $f\, x$ (written here as $\$ f x$) has type $\rho$.

```agda
  `·⊢ : ∀ {Γ f x τ ρ} →
        Γ ⊢ f ⦂ τ `⇒ ρ →
        Γ ⊢ x ⦂ τ →
        Γ ⊢ `$ f x ⦂ ρ
```

The rest of the formers follow these patterns:
```agda
  `⟨,⟩⊢ : ∀ {Γ a b τ ρ} →
          Γ ⊢ a ⦂ τ →
          Γ ⊢ b ⦂ ρ →
          Γ ⊢ `⟨ a , b ⟩ ⦂ τ `× ρ
          
  `π₁⊢ :  ∀ {Γ a τ ρ} →
          Γ ⊢ a ⦂ τ `× ρ →
          Γ ⊢ `π₁ a ⦂ τ
          
  `π₂⊢ :  ∀ {Γ a τ ρ} →
          Γ ⊢ a ⦂ τ `× ρ →
          Γ ⊢ `π₂ a ⦂ ρ
          
  `U⊢ :   ∀ {Γ} →
          Γ ⊢ `U ⦂ UU
```

This completes our typing relation. We can now show that some given
program has some given type, for example:

<!--
```agda
module Example-1 where
```
-->

```agda
  const : Expr
  const = `λ 0 (`λ 1 (` 0))

  const-is-UU⇒UU⇒UU : [] ⊢ const ⦂ UU `⇒ (UU `⇒ UU)
  const-is-UU⇒UU⇒UU = `λ⊢ (`λ⊢ (`⊢ 0 refl))
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
data Value : Expr → Type where
  v-var : ∀ {n} → Value (` n)
  v-λ : ∀ {n body} → Value (`λ n body)
  v-⟨,⟩ : ∀ {a b} → Value (`⟨ a , b ⟩)
  v-U : Value `U
```

Our next goal is to now define a "step" relation,
which dictates that a term $x$ may, through a reduction, step to
another expression $x'$ that represents one "step" of evaluation.

This is how we will
define the evaluation of our expressions. Before we can define
stepping, we need to define substitution, so that we may turn an
expression like $(\lambda x. f\,x) y$ into $f\,y$. We notate the
substitution of a variable $n$ for an expression $e$ in another
expression $f$ as `f [ n := e ]`{.Agda}. The method of substitution
we implement is called **capture-avoiding substitution**.

<!--
```agda
infix 2 _[_:=_]
```
-->

```agda
_[_:=_] : Expr → Nat → Expr → Expr
```
If a variable x is equal to the variable we are substituing for, n,
we return the new expression. Else, the variable unchanged.
```agda
` x [ n := e ] with x ≡? n
... | yes _ = e
... | no _ = ` x 
```

Here is why it's called capture-avoiding: if our lambda binds the
variable name again, we don't substitute inside. In other words, the
substituion `(λ y. y) y [y := k]`{.Agda} yields `(λ y. y) k`{.Agda},
not `(λ y. k) k`{.Agda}.

```agda
`λ x f [ n := e ] with x ≡? n
... | yes _ = `λ x f
... | no _ = `λ x (f [ n := e ])
```
In all other cases, we simply "move" the substition into all
subexpressions. (Or, do nothing.)
```agda
`$ f x [ n := e ] = `$ (f [ n := e ]) (x [ n := e ])
`⟨ a , b ⟩ [ n := e ] = `⟨ a [ n := e ] , b [ n := e ] ⟩
`π₁ a [ n := e ] = `π₁ (a [ n := e ])
`π₂ a [ n := e ] = `π₂ (a [ n := e ])
`U [ n := e ] = `U
```

Now, we define our step relation proper.

```agda
data Step : Expr → Expr → Type where
```

The act of turning an application $(λ\,y. y)\,x$ into $x$ is called
β-reduction for lambda terms. We require $x$ to be a value in order
to keep reduction deterministic -- this will be elaborated on in
a moment.
```agda
  β-λ : ∀ {n body x} →
        Value x →
        Step (`$ (`λ n body) x) (body [ n := x ])
```

Likewise, reducing projections on a pair is called β-reduction for
pairs.

```agda
  β-π₁ : ∀ {a b} →
       Step (`π₁ `⟨ a , b ⟩) a
  β-π₂ : ∀ {a b} →
       Step (`π₂ `⟨ a , b ⟩) b
```

We also have two reductions that can step "inside" projections, which
we will call ξ rules.

```agda
  ξ-π₁ : ∀ {a₁ a₂} →
       Step a₁ a₂ →
       Step (`π₁ a₁) (`π₁ a₂)

  ξ-π₂ : ∀ {a₁ a₂} →
       Step a₁ a₂ →
       Step (`π₂ a₁) (`π₂ a₂)
```

Likewise, we have one that can step inside an application, on
the left hand side.

```agda
  ξ-$ₗ : ∀ {f₁ f₂ x} →
       Step f₁ f₂ →
       Step (`$ f₁ x) (`$ f₂ x)
```

We also include a rule for stepping on the right hand side, requiring
the left to be a value first. This, combined with the value requirement
of the `β-λ`{.Agda} rule, keep our evaluation **deterministic**, forcing
that evaluation should take place from left to right. We will prove
this later.

```agda
  ξ-$ᵣ : ∀ {f x₁ x₂} →
       Value f →
       Step x₁ x₂ →
       Step (`$ f x₁) (`$ f x₂)
```

These are all of our step rules! The STLC is indeed very simple.
We can now show that, say, an identity function applied to something
reduces properly:

<!--
```agda
module Example-2 where
```
-->

```agda
  our-id : Expr
  our-id = `λ 0 (` 0)

  pair : Expr
  pair = `⟨ `U , `U ⟩

  id-app : Expr
  id-app = `$ our-id pair

  id-app-step : Step id-app pair
  id-app-step = β-λ v-⟨,⟩
```

TODO: Refl Trans closure of Step

## The big two properties

The two "big" properties about the STLC we wish to prove are called
**progress** and **preservation**. Progress states that any
given term is either done (a value), or can take another step.
Preservation states that if a well typed expression $x$ steps to another $x'$,
they have the same type (i.e., stepping preserves type.)

The first step in proving these is showing that a "proper" substituion
preserves types. If a term $tm$ has type $\tau$ when extended
with a variable $n$ of type $\rho$, then substituting any expression
of type $\rho$ for $n$ preserves the type of $tm$. To prove this,
we first show that renaming preserves types - if $\Gamma$ and $\Delta$
are contexts, and for every index in $\Gamma$, $\Delta$ gives the
same type, then any term with a type under $\Gamma$ has the same
type under $\Delta$.

```agda
rename : ∀ {Γ Δ} →
         (∀ n ty → index Γ n ≡ just ty → index Δ n ≡ just ty) →
         (∀ tm ty → Γ ⊢ tm ⦂ ty → Δ ⊢ tm ⦂ ty)
```

Variables are fairly straightforward - we simply apply our renaming
function.

```agda
rename {Γ} {Δ} f (` x) ty (`⊢ .x n) = `⊢ x (f x ty n)
```

Lambda abstractions are more complex - we need to extend our renaming
function to encompass the new abstraction.

```agda
rename {Γ} {Δ} f (`λ x tm) ty (`λ⊢ {τ = τ} {ρ = ρ} Γ⊢) = `λ⊢ (rename f' tm ρ Γ⊢)
  where
    f' : (n : Nat) (ty : Ty) →
          index (Γ ∷c (x , τ)) n ≡ just ty →
          index (Δ ∷c (x , τ)) n ≡ just ty
    f' n ty Γ≡ with n ≡? x
    ... | yes x≡n = Γ≡
    ... | no p = f n ty Γ≡
```

Everything else is straightforward, as in the substitution case.

```agda
rename {Γ} {Δ} f (`$ f' x) ty (`·⊢ {τ = τ} Γ⊢₁ Γ⊢₂) =
  `·⊢ (rename f f' (τ `⇒ ty) Γ⊢₁) (rename f x τ Γ⊢₂)
  
rename {Γ} {Δ} f `⟨ a , b ⟩ ty (`⟨,⟩⊢ {τ = τ} {ρ = ρ} Γ⊢₁ Γ⊢₂) =
  `⟨,⟩⊢ (rename f a τ Γ⊢₁) (rename f b ρ Γ⊢₂)
  
rename {Γ} {Δ} f (`π₁ tm) ty (`π₁⊢ {ρ = ρ} Γ⊢) = `π₁⊢ (rename f tm (ty `× ρ) Γ⊢)
rename {Γ} {Δ} f (`π₂ tm) ty (`π₂⊢ {τ = τ} Γ⊢) = `π₂⊢ (rename f tm (τ `× ty) Γ⊢)
rename {Γ} {Δ} f `U ty `U⊢ = `U⊢
```

Another few lemmas! This time about shuffling and dropping names
in the context.
```agda
duplicates-are-ok : ∀ {Γ n t₁ t₂ bd typ} →
                        Γ ∷c (n , t₂) ∷c (n , t₁) ⊢ bd ⦂ typ →
                        Γ ∷c (n , t₁) ⊢ bd ⦂ typ
variable-swap : ∀ {Γ n k t₁ t₂ bd typ} →
                ¬ n ≡ k →
                Γ ∷c (n , t₁) ∷c (k , t₂) ⊢ bd ⦂ typ →
                Γ ∷c (k , t₂) ∷c (n , t₁) ⊢ bd ⦂ typ                        
                    
```
<details>
```agda
variable-swap {Γ} {n} {k} {t₁} {t₂} {x} {typ} ¬n≡k Γ⊢ = rename f x typ Γ⊢ 
  where
    f : (z : Nat) (ty : Ty) →
         index (Γ ∷c (n , t₁) ∷c (k , t₂)) z ≡ just ty →
         index (Γ ∷c (k , t₂) ∷c (n , t₁)) z ≡ just ty
    f z ty x with z ≡? n in eq
    ... | no ¬z≡n = h
      where
        h : (index (Γ ∷c (k , t₂)) z) ≡ just ty
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
    f : (k : Nat) (ty : Ty) →
         index (Γ ∷c (n , t₂) ∷c (n , t₁)) k ≡ just ty →
         index (Γ ∷c (n , t₁)) k ≡ just ty
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
absurdity from considering that `index [] n ≡ just τ`{.Agda}, for any $n$
and $\tau$.

```agda
weakening : ∀ {Γ tm ty} →
              [] ⊢ tm ⦂ ty →
              Γ  ⊢ tm ⦂ ty
weakening {Γ} {tm} {ty} []⊢ = rename f tm ty []⊢
  where
    f : (n : Nat) (τ : Ty) → index [] n ≡ just τ → index Γ n ≡ just τ
    f _ _ x = absurd (nothing≠just x)
```

Now with renaming under our belt, we can prove substitution proper
preserves types. Note that the substitute's type must exist in
the empty context, to prevent conflicts of variables.

```agda
subst-pres : ∀ {Γ n t bd typ s} →
               [] ⊢ s ⦂ t → 
               Γ ∷c (n , t) ⊢ bd ⦂ typ →
               Γ ⊢ bd [ n := s ] ⦂ typ
```

In the case of variables, we use weakening for the substituion itself,
to embed our term `s`{.Agda} into the context $\Gamma$.

```agda
subst-pres {Γ} {n} {t} {` x} {typ} {s} s⊢ (`⊢ .x k) with x ≡? n
... | yes _ = weakening (subst (λ ρ → [] ⊢ s ⦂ ρ) (just-inj k) s⊢)
... | no _  = `⊢ x k
```

Lambda abstraction is once again slightly annoying. Handling the case
where the names are equal requires some removing of duplicates in the
context, and where they are not equal requires some shuffling. 

```agda
subst-pres {Γ} {n} {t} {`λ x bd} {typ} {s} s⊢ (`λ⊢ {τ = τ} {ρ = ρ} Γ⊢) with x ≡? n
... | yes x≡n = `λ⊢ (duplicates-are-ok
                      (subst (λ _ → Γ ∷c _ ∷c _ ⊢ bd ⦂ ρ) (sym x≡n) Γ⊢))
... | no ¬x≡n = `λ⊢ (subst-pres s⊢ (variable-swap (λ x≡n → ¬x≡n (sym x≡n)) Γ⊢))
```

The rest proceeds nicely.

```agda
subst-pres {Γ} {n} {t} {`$ bd bd₁} {typ} {s} s⊢ (`·⊢ Γ⊢₁ Γ⊢₂) =
  `·⊢ (subst-pres s⊢ Γ⊢₁) (subst-pres s⊢ Γ⊢₂)
  
subst-pres {Γ} {n} {t} {`⟨ a , b ⟩} {typ} {s} s⊢ (`⟨,⟩⊢ Γ⊢₁ Γ⊢₂) =
  `⟨,⟩⊢ (subst-pres s⊢ Γ⊢₁) (subst-pres s⊢ Γ⊢₂)
  
subst-pres {Γ} {n} {t} {`π₁ bd} {typ} {s} s⊢ (`π₁⊢ Γ⊢) = `π₁⊢ (subst-pres s⊢ Γ⊢)
subst-pres {Γ} {n} {t} {`π₂ bd} {typ} {s} s⊢ (`π₂⊢ Γ⊢) = `π₂⊢ (subst-pres s⊢ Γ⊢)
subst-pres {Γ} {n} {t} {`U} {typ} {s} s⊢ `U⊢ = `U⊢
```

We'll do preservation first, which follows very easily from the
lemmas we've already defined:

```agda
preservation : ∀ {x₁ x₂ typ} →
               Step x₁ x₂ →
               [] ⊢ x₁ ⦂ typ →
               [] ⊢ x₂ ⦂ typ
               
preservation (β-λ p) (`·⊢ (`λ⊢ ⊢f) ⊢x) = subst-pres ⊢x ⊢f
preservation β-π₁ (`π₁⊢ (`⟨,⟩⊢ ⊢a ⊢b)) = ⊢a
preservation β-π₂ (`π₂⊢ (`⟨,⟩⊢ ⊢a ⊢b)) = ⊢b
preservation (ξ-π₁ step) (`π₁⊢ ⊢a) = `π₁⊢ (preservation step ⊢a)
preservation (ξ-π₂ step) (`π₂⊢ ⊢b) = `π₂⊢ (preservation step ⊢b)
preservation (ξ-$ₗ step) (`·⊢ ⊢f ⊢x) = `·⊢ (preservation step ⊢f) ⊢x
preservation (ξ-$ᵣ val step) (`·⊢ ⊢f ⊢x) = `·⊢ ⊢f (preservation step ⊢x)
```

Then, progress, noting that the expression must be well typed. We
define progress as a datatype, as it's much nicer to work with.

```agda
data Progress (M : Expr): Type where
  going : ∀ {N} →
               Step M N →
               Progress M
  done : Value M → Progress M                 
```

Then, progress reduces to mostly a lot of case analysis.

```agda
progress : ∀ {x ty} →
           [] ⊢ x ⦂ ty →
           Progress x
           
progress (`⊢ n n∈) = absurd (nothing≠just n∈)
progress (`λ⊢ {n = n} {body = body} ⊢x) = done v-λ
progress (`·⊢ ⊢f ⊢x) with progress ⊢f
... | going next-f = going (ξ-$ₗ next-f)
... | done vf with progress ⊢x
... |   going next-x = going (ξ-$ᵣ vf next-x)
... |   done vx with ⊢f
... |     `⊢ n n∈ = absurd (nothing≠just n∈)
... |     `λ⊢ f = going (β-λ vx)

progress (`⟨,⟩⊢ {a = a} {b = b} ⊢a ⊢b) = done v-⟨,⟩
progress (`π₁⊢ {a = a} ⊢x) with progress ⊢x
... | going next = going (ξ-π₁ next)
... | done v-⟨,⟩ = going β-π₁
... | done v-var with ⊢x
... |   `⊢ _ x∈ = absurd (nothing≠just x∈)

progress (`π₂⊢ ⊢x) with progress ⊢x
... | going next = going (ξ-π₂ next)
... | done v-⟨,⟩ = going β-π₂
... | done v-var with ⊢x
... |   `⊢ _ x∈ = absurd (nothing≠just x∈)

progress `U⊢ = done v-U
```

There's our big two properties! As promised, we'll also now prove
that our step relation is deterministic -- there is only one
step that can be applied at any given time. This is also equivalent
to saying that if some term $x$ steps to $x_{1}$ and also to $x_{2}$,
then $x_{1} ≡ x_{2}$.

We do this with the help of a lemma that states values do not step to
anything.
```agda
value-¬step : ∀ {x y} →
              Value x →
              ¬ (Step x y)
```
<details>
```agda
value-¬step v-var ()
value-¬step v-λ ()
value-¬step v-⟨,⟩ ()
value-¬step v-U ()
```
</details>

```agda
deterministic : ∀ {x ty x₁ x₂} →
                [] ⊢ x ⦂ ty →
                Step x x₁ →
                Step x x₂ →
                x₁ ≡ x₂
                
deterministic (`·⊢ ⊢f ⊢x) (β-λ vx₁) (β-λ vx₂) = refl
deterministic (`·⊢ ⊢f ⊢x) (β-λ vx) (ξ-$ᵣ x b) = absurd (value-¬step vx b)
deterministic (`·⊢ ⊢f ⊢x) (ξ-$ₗ →x₁) (ξ-$ₗ →x₂) =
  `$-apₗ (deterministic ⊢f →x₁ →x₂)
  
deterministic (`·⊢ ⊢f ⊢x) (ξ-$ₗ →x₁) (ξ-$ᵣ vx →x₂) = absurd (value-¬step vx →x₁)
deterministic (`·⊢ ⊢f ⊢x) (ξ-$ᵣ vx₁ →x₁) (β-λ vx₂) = absurd (value-¬step vx₂ →x₁)
deterministic (`·⊢ ⊢f ⊢x) (ξ-$ᵣ vx →x₁) (ξ-$ₗ →x₂) = absurd (value-¬step vx →x₂)
deterministic (`·⊢ ⊢f ⊢x) (ξ-$ᵣ _ →x₁) (ξ-$ᵣ _ →x₂) =
  `$-apᵣ (deterministic ⊢x →x₁ →x₂)
  
deterministic (`π₁⊢ ⊢x) β-π₁ β-π₁ = refl
deterministic (`π₁⊢ ⊢x) (ξ-π₁ →x₁) (ξ-π₁ →x₂) = ap `π₁ (deterministic ⊢x →x₁ →x₂)
deterministic (`π₂⊢ ⊢x) β-π₂ β-π₂ = refl
deterministic (`π₂⊢ ⊢x) (ξ-π₂ →x₁) (ξ-π₂ →x₂) = ap `π₂ (deterministic ⊢x →x₁ →x₂)
```
