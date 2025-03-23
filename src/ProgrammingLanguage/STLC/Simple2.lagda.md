<!--
```agda
open import 1Lab.HLevel.Closure
open import 1Lab.Prelude


open import Data.Maybe
open import Data.Bool
open import Data.List
open import Data.Dec
open import Data.Nat
open import Data.Sum
```
-->

```agda
module ProgrammingLanguage.STLC.Simple2 where
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
  _`$_ : Expr → Expr → Expr
  `⟨_,_⟩ :  Expr → Expr → Expr
  `π₁ : Expr → Expr
  `π₂ : Expr → Expr
  `tt : Expr
```

<details><summary>Some application and injectivity lemmas, for convenience.

```agda
`$-ap : ∀ {a b x y} → a ≡ b → x ≡ y → a `$ x ≡ b `$ y
`λ-ap : ∀ {x y a b} → x ≡ y → a ≡ b → `λ x a ≡ `λ y b
`⟨⟩-ap : ∀ {x y a b} → x ≡ y → a ≡ b → `⟨ x , a ⟩ ≡ `⟨ y , b ⟩


`-inj : ∀ {a b} → ` a ≡ ` b → a ≡ b
`λ-inj : ∀ {x y a b} → `λ x a ≡ `λ y b → (x ≡ y) × (a ≡ b)
`$-inj : ∀ {f g x y} → f `$ x ≡ g `$ y → (f ≡ g) × (x ≡ y)
`⟨⟩-inj : ∀ {x y a b} → `⟨ x , y ⟩ ≡ `⟨ a , b ⟩ → (x ≡ a) × (y ≡ b)
`π₁-inj : ∀ {a b} → `π₁ a ≡ `π₁ b → a ≡ b
`π₂-inj : ∀ {a b} → `π₂ a ≡ `π₂ b → a ≡ b
```
</summary>

```agda
`$-ap {x = x} a=b x=y = ap₂ (λ q w → q `$ w) a=b x=y
`λ-ap {x} {y} {a} {b} x=y a=b = ap₂ `λ x=y a=b
`⟨⟩-ap {x} {y} {a} {b} x=y a=b = ap₂ (λ q w → `⟨ q , w ⟩) x=y a=b

`-inj x = ap h x
  where
    h : Expr → Nat 
    h (` x) = x 
    h _ = 0
`λ-inj x = ap h x , ap g x
  where
    h : Expr → Nat
    h (`λ x _) = x
    h _ = 0

    g : Expr → Expr
    g (`λ _ b) = b
    g _ = `tt

`$-inj x = ap h x , ap g x
  where
    h : Expr → Expr
    h (a `$ _) = a
    h _ = `tt

    g : Expr → Expr
    g (_ `$ b) = b
    g _ = `tt
`⟨⟩-inj x = ap h x , ap g x
  where
    h : Expr → Expr
    h (`⟨ a , _ ⟩) = a
    h _ = `tt

    g : Expr → Expr
    g (`⟨ _ , b ⟩) = b
    g _ = `tt
`π₁-inj x = ap h x
  where
    h : Expr → Expr
    h (`π₁ x) = x
    h _ = `tt
`π₂-inj x = ap h x
  where
    h : Expr → Expr
    h (`π₂ x) = x
    h _ = `tt
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
  `var-intro : ∀ {Γ τ} (n : Nat) →
       index Γ n ≡ just τ →
       Γ ⊢ ` n ⦂ τ
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
module Example-1 where
```
-->

```agda
  const : Expr
  const = `λ 0 (`λ 1 (` 0))

  const-is-`⊤⇒`⊤⇒`⊤ : [] ⊢ const ⦂ `⊤ `⇒ (`⊤ `⇒ `⊤)
  const-is-`⊤⇒`⊤⇒`⊤ = `⇒-intro (`⇒-intro (`var-intro 0 refl))
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
  v-λ : ∀ {n body} → Value (`λ n body)
  v-⟨,⟩ : ∀ {a b} → Value (`⟨ a , b ⟩)
  v-⊤ : Value `tt
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

Another detour! In order to correctly implement the capture-avoiding
part of the subtitution, we need to be able to tell when terms are
**alpha equivalent**. Alpha equivalence is when terms are equivalent,
up to renaming. For example, $\lambda x. x$ is alpha equivalent to
$\lambda y. y$, but $\lambda z. x$ is not alpha equivalent to
$\lambda z. y$.

```agda
is-swap : (Nat → Nat) → Type
is-swap f = ∀ x → f (f x) ≡ x

id-is-swap : is-swap id
id-is-swap x = refl

single-swap : Nat → Nat → (Nat → Nat)
single-swap x y k with k ≡? x 
... | yes _ = y
... | no _ with k ≡? y 
... | yes _ = x
... | no _ = k

single-is-swap : ∀ x y → is-swap (single-swap x y)
single-is-swap x y k with k ≡? x 
single-is-swap x y k | yes k=x with y ≡? x 
... | yes y=x = y=x ∙ sym k=x
... | no ¬y=x with y ≡? y 
... | yes _ = sym k=x
... | no ¬y=y = absurd (¬y=y refl)
single-is-swap x y k | no ¬k=x with k ≡? y
single-is-swap x y k | no ¬k=x | yes k=y with x ≡? x 
... | yes _ = sym k=y
... | no ¬x=x = absurd (¬x=x refl) 
single-is-swap x y k | no ¬k=x | no ¬k=y with k ≡? x 
... | yes k=x = absurd (¬k=x k=x)
... | no ¬k=x with k ≡? y 
... | yes k=y = absurd (¬k=y k=y)
... | no ¬k=y = refl

swap-inj : ∀ {f x y} → is-swap f → f x ≡ f y → x ≡ y
swap-inj {f} {x} {y} p eq = go (ap f eq)
  where
    go : f (f x) ≡ f (f y) → x ≡ y
    go eq = subst₂ (λ a b → a ≡ b) (p x) (p y) eq

swap-compat : ∀ (f g : Nat → Nat) → Type
swap-compat f g = f ∘ g ≡ g ∘ f

swap-compat-to-involute : (f g : Nat → Nat) →
                          is-swap f →
                          is-swap g →
                          swap-compat f g → 
                          ∀ x → f (g (f (g x))) ≡ x
swap-compat-to-involute f g sf sg sc x = h₅ x
  where
    h₅ : ∀ z → f (g (f (g z))) ≡ z
    h₅ z = ap f (ap g (happly sc z) ∙ sg (f z)) ∙ sf z

merge : ∀ f g → is-swap f → is-swap g → swap-compat f g → is-swap (f ∘ g)
merge f g sf sg compat = swap-compat-to-involute f g sf sg compat

remove-swap : (f : Nat → Nat) (x y : Nat) → f x ≡ y → f y ≡ x → Σ (Nat → Nat) λ g → (g x ≡ x × g y ≡ y)
remove-swap f x y fx=y fy=x .fst k with k ≡? x 
... | yes _ = x
... | no _ with k ≡? y
... | yes _ = y
... | no _ = f k 
remove-swap f x y fx=y fy=x .snd .fst with x ≡? x 
... | yes _ = refl
... | no ¬x=x = absurd (¬x=x refl)
remove-swap f x y fx=y fy=x .snd .snd with y ≡? x
... | yes y=x = sym y=x
... | no ¬y=x with y ≡? y 
... | yes _ = refl
... | no ¬y=y = absurd (¬y=y refl)

remove : ∀ (f : Nat → Nat) x → is-swap f → Σ (Nat → Nat) λ g → Σ Nat λ y → f x ≡ y → (g x ≡ x × g y ≡ y)
remove f x sf = 
  let r = remove-swap f x (f x) refl (sf x) in
  r .fst , (f x) , λ _ → h₁ , h₂

  where
    h₁ : remove-swap f x (f x) refl (sf x) .fst x ≡ x
    h₁ with x ≡? x 
    ... | yes _ = refl
    ... | no ¬x=x = absurd (¬x=x refl)

    h₂ :  remove-swap f x (f x) refl (sf x) .fst (f x) ≡ f x
    h₂ with f x ≡? x 
    ... | yes fx=x = sym fx=x
    ... | no ¬fx=x with f x ≡? f x 
    ... | yes _ = refl
    ... | no ¬fx=fx = absurd (¬fx=fx refl)

is-swap→is-swap-remove : ∀ (f : Nat → Nat) x → (sf : is-swap f) → is-swap ((remove f x sf) .fst)
is-swap→is-swap-remove f x sf p with p ≡? x 
is-swap→is-swap-remove f x sf p | yes p=x with x ≡? x
... | yes _ = sym p=x
... | no ¬x=x = absurd (¬x=x refl)
is-swap→is-swap-remove f x sf p | no ¬p=x with p ≡? f x
is-swap→is-swap-remove f x sf p | no ¬p=x | yes p=fx with f x ≡? x 
... | yes fx=x = sym (p=fx ∙ fx=x)
... | no ¬fx=x with f x ≡? f x 
... | yes _ = sym p=fx
... | no ¬fx=fx = absurd (¬fx=fx refl)
is-swap→is-swap-remove f x sf p | no ¬p=x | no ¬p=fx with f p ≡? x 
... | yes fp=x = absurd (¬p=fx (h (ap f fp=x)))
  where
    h : f (f p) ≡ f x → p ≡ f x
    h w = subst (λ k → p ≡ k) w (sym (sf p))
... | no ¬fp=x with f p ≡? f x
... | yes fp=fx = absurd (¬p=x (swap-inj sf fp=fx))
... | no ¬fp=fx = sf p

up : Nat → Expr → Expr
up n (` x) = ` (n + x)
up n (`λ x e) = `λ (n + x) (up n e)
up n (f `$ x) = up n f `$ up n x
up n `⟨ a , b ⟩ = `⟨ up n a , up n b ⟩
up n (`π₁ e) = `π₁ (up n e)
up n (`π₂ e) = `π₂ (up n e)
up n `tt = `tt

up-0-eq : ∀ (e : Expr) → e ≡ up 0 e
up-0-eq (` x) = refl
up-0-eq (`λ x e) = `λ-ap refl (up-0-eq e)
up-0-eq (e `$ e₁) = `$-ap (up-0-eq e) (up-0-eq e₁)
up-0-eq `⟨ e , e₁ ⟩ = `⟨⟩-ap (up-0-eq e) (up-0-eq e₁)
up-0-eq (`π₁ e) = ap `π₁ (up-0-eq e)
up-0-eq (`π₂ e) = ap `π₂ (up-0-eq e)
up-0-eq `tt = refl

data α-equiv' : (f : Nat → Nat) → {is-swap f} → Expr → Expr → Type where
  α-var : ∀ {x y s} → 
          s ≡ single-swap x y →
          (is : is-swap s) →
          α-equiv' (s) {is} (` x) (` y) 
  α-lam : ∀ {x y : Nat} {b₁ b₂ f sf}
          {r : _} →
          α-equiv' f {sf} b₁ b₂ →
          r ≡ fst (remove f x sf) →
          (is : is-swap r) →
          (f x ≡ y ⊎ (f x ≡ x × f y ≡ y)) →
          α-equiv' r 
                  {is} 
                  (`λ x b₁) (`λ y b₂)
  α-app : ∀ {q₁ q₂ x₁ x₂ f g sf sg m} →
          α-equiv' f {sf} q₁ q₂ →
          α-equiv' g {sg} x₁ x₂ →
          (s : swap-compat f g) →
          m ≡ merge f g sf sg s →
          α-equiv' (f ∘ g) {m} (q₁ `$ x₁) (q₂ `$ x₂)
  α-pair : ∀ {a₁ a₂ b₁ b₂ f g sf sg m} →
          α-equiv' f {sf} a₁ a₂ →
          α-equiv' g {sg} b₁ b₂ →
          (s : swap-compat f g) →
          m ≡ merge f g sf sg s →
          α-equiv' (f ∘ g) {m} (`⟨ a₁ , b₁ ⟩) (`⟨ a₂ , b₂ ⟩)
  α-pi₁ : ∀ {a b f sf} →
          α-equiv' f {sf} a b →
          α-equiv' f {sf} (`π₁ a) (`π₁ b)
  α-pi₂ : ∀ {a b f sf} →
          α-equiv' f {sf} a b →
          α-equiv' f {sf} (`π₂ a) (`π₂ b)
  α-tt : α-equiv' id {id-is-swap} `tt `tt

record α-equiv (a b : Expr) : Type where
  field
    f : Nat → Nat
    sf : is-swap f
    n : Nat
    eq : α-equiv' f {sf} a (up n b)

single-swap-id-is-id : ∀ x → single-swap x x ≡ id
single-swap-id-is-id x = funext h
  where
    h : (y : Nat) → single-swap x x y ≡ id y
    h y with y ≡? x 
    ... | yes y=x = sym y=x
    ... | no ¬y=x with y ≡? x 
    ... | yes y=x = absurd (¬y=x y=x)
    ... | no _ = refl

α-equiv'-self : ∀ (e : Expr) → α-equiv' id {id-is-swap} e e
α-equiv'-self (` x) = α-var (sym (single-swap-id-is-id x)) id-is-swap
α-equiv'-self (`λ x e) = α-lam (α-equiv'-self e) (sym (funext (rem x))) id-is-swap (inl refl)
  where
    rem : ∀ y k → fst (remove id y id-is-swap) k ≡ id k
    rem y k with k ≡? y 
    ... | yes k=y = sym k=y
    ... | no ¬k=y with k ≡? y 
    ... | yes k=y = absurd (¬k=y k=y)
    ... | no ¬k=y = refl

α-equiv'-self (f `$ x) = α-app (α-equiv'-self f) (α-equiv'-self x) refl prop!
α-equiv'-self `⟨ a , b ⟩ = α-pair (α-equiv'-self a) (α-equiv'-self b) refl prop!
α-equiv'-self (`π₁ e) = α-pi₁ (α-equiv'-self e)
α-equiv'-self (`π₂ e) = α-pi₂ (α-equiv'-self e)
α-equiv'-self `tt = α-tt

α-equiv-self : ∀ (e : Expr) → α-equiv e e
α-equiv-self e .α-equiv.f = id
α-equiv-self e .α-equiv.sf = id-is-swap
α-equiv-self e .α-equiv.n = 0
α-equiv-self e .α-equiv.eq = 
             subst (λ s → α-equiv' id e s) (up-0-eq e) (α-equiv'-self e)

max-in+1 : ∀ (e : Expr) → Nat
max-in+1 (` x) = suc x
max-in+1 (`λ x e) = max (suc x) (max-in+1 e)
max-in+1 (f `$ x) = max (max-in+1 f) (max-in+1 x)
max-in+1 `⟨ a , b ⟩ = max (max-in+1 a) (max-in+1 b)
max-in+1 (`π₁ e) = max-in+1 e
max-in+1 (`π₂ e) = max-in+1 e
max-in+1 `tt = 1

α-self-respect : ∀ (e : Expr) (n : Nat) f sf → 
                 α-equiv' f {sf} e (up n e) →
                 ∀ x → f x ≡ (n + x) ⊎ (f x ≡ x × f (n + x) ≡ n + x)
α-self-respect (` x₁) n f sf (α-var x₂ .sf) x = subst (λ f → f x ≡ n + x ⊎ Σ (f x ≡ x) (λ _ → f (n + x) ≡ n + x)) 
               (sym x₂)
               go
    where
      go : (single-swap x₁ (n + x₁) x) ≡
            n + x
            ⊎
            Σ
            ((single-swap x₁ (n + x₁) x) ≡ x)
            (λ _ →
               (single-swap x₁ (n + x₁) (n + x))
               ≡ n + x)
      go with x ≡? x₁ 
      ... | yes a = inl (subst (λ w → n + w ≡ n + x) a refl)
      ... | no ¬a with x ≡? n + x₁ 
      go | no ¬a | yes a = {!!}
      go | no ¬a | no ¬a₁ with n + x ≡? x₁ 
      ... | yes a = {!!}
      ... | no ¬a₂ = {!!}

α-self-respect (`λ x₁ e) n f sf aph x = {!!}
α-self-respect (e `$ e₁) n f sf aph x = {!!}
α-self-respect `⟨ e , e₁ ⟩ n f sf aph x = {!!}
α-self-respect (`π₁ e) n f sf aph x = {!!}
α-self-respect (`π₂ e) n f sf aph x = {!!}
α-self-respect `tt n f sf aph x = {!!}

α-lift' : ∀ (e : Expr) (n : Nat) → max-in+1 e ≤ n → Σ _ λ f 
          → Σ (is-swap f) λ sf → α-equiv' f {sf} e (up n e)
α-lift' (` x) n max .fst = single-swap x (n + x)
α-lift' (` x) n max .snd .fst = single-is-swap x (n + x)
α-lift' (` x) n max .snd .snd = α-var refl (α-lift' (` x) n max .snd .fst)
α-lift' (`λ x e) n max =
  let f : Σ (Nat → Nat) (λ f → Σ (is-swap f) (λ sf → α-equiv' f e (up n e)))
      f = α-lift' e n (≤-trans (max-≤r (suc x) (max-in+1 e)) max)
  in
  fst (remove (f .fst) x (f .snd .fst)) , 
  is-swap→is-swap-remove (fst f) x (f .snd .fst) ,   
  α-lam (f .snd .snd) refl (is-swap→is-swap-remove (fst f) x (f .snd .fst)) go
    where
      f = α-lift' e n (≤-trans (max-≤r (suc x) (max-in+1 e)) max)

      go : f .fst x ≡
            n + x
            ⊎
            Σ
            (f .fst x ≡
             x)
            (λ _ →
               f .fst
               (n + x)
               ≡ n + x)
      go = α-self-respect e n (f .fst) (f .snd .fst) (f .snd . snd) x
α-lift' (e `$ e₁) n max = {!!}
α-lift' `⟨ e , e₁ ⟩ n max = {!!}
α-lift' (`π₁ e) n max = α-lift' e n max .fst ,
                         α-lift' e n max .snd .fst , α-pi₁ (α-lift' e n max .snd .snd)
α-lift' (`π₂ e) n max = α-lift' e n max .fst ,
                         α-lift' e n max .snd .fst , α-pi₂ (α-lift' e n max .snd .snd)
α-lift' `tt n max = id , id-is-swap , α-tt
```
            
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
substitution `(λ y. y) y [y := k]`{.Agda} yields `(λ y. y) k`{.Agda},
not `(λ y. k) k`{.Agda}.

```agda
`λ x f [ n := e ] with x ≡? n
... | yes _ = `λ x f
... | no _ = `λ x (f [ n := e ])
```

In all other cases, we simply "move" the substition into all
subexpressions. (Or, do nothing.)

```agda
f `$ x [ n := e ] = (f [ n := e ]) `$ (x [ n := e ])
`⟨ a , b ⟩ [ n := e ] = `⟨ a [ n := e ] , b [ n := e ] ⟩
`π₁ a [ n := e ] = `π₁ (a [ n := e ])
`π₂ a [ n := e ] = `π₂ (a [ n := e ])
`tt [ n := e ] = `tt
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
        Step ((`λ n body) `$ x) (body [ n := x ])
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
       Step (f₁ `$ x) (f₂ `$ x)
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
       Step (f `$ x₁) (f `$ x₂)
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
  pair = `⟨ `tt , `tt ⟩

  id-app : Expr
  id-app = our-id `$ pair

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

The first step in proving these is showing that a "proper" substitution
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
rename {Γ} {Δ} f (` x) ty (`var-intro .x n) = `var-intro x (f x ty n)
```

Lambda abstractions are more complex - we need to extend our renaming
function to encompass the new abstraction.

```agda
rename {Γ} {Δ} f (`λ x tm) ty (`⇒-intro {τ = τ} {ρ = ρ} Γ⊢) = `⇒-intro (rename f' tm ρ Γ⊢)
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
preservation : ∀ {x₁ x₂ typ} →
               Step x₁ x₂ →
               [] ⊢ x₁ ⦂ typ →
               [] ⊢ x₂ ⦂ typ
               
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
value-¬step : ∀ {x y} →
              Value x →
              ¬ (Step x y)
```

<details>
```agda
value-¬step v-λ ()
value-¬step v-⟨,⟩ ()
value-¬step v-⊤ ()
```
</details>

```agda
deterministic : ∀ {x ty x₁ x₂} →
                [] ⊢ x ⦂ ty →
                Step x x₁ →
                Step x x₂ →
                x₁ ≡ x₂
                
deterministic (`⇒-elim ⊢f ⊢x) (β-λ vx₁) (β-λ vx₂) = refl
deterministic (`⇒-elim ⊢f ⊢x) (β-λ vx) (ξ-$ᵣ x b) = absurd (value-¬step vx b)
deterministic (`⇒-elim ⊢f ⊢x) (ξ-$ₗ →x₁) (ξ-$ₗ →x₂) =
  `$-ap (deterministic ⊢f →x₁ →x₂) refl
  
deterministic (`⇒-elim ⊢f ⊢x) (ξ-$ₗ →x₁) (ξ-$ᵣ vx →x₂) = absurd (value-¬step vx →x₁)
deterministic (`⇒-elim ⊢f ⊢x) (ξ-$ᵣ vx₁ →x₁) (β-λ vx₂) = absurd (value-¬step vx₂ →x₁)
deterministic (`⇒-elim ⊢f ⊢x) (ξ-$ᵣ vx →x₁) (ξ-$ₗ →x₂) = absurd (value-¬step vx →x₂)
deterministic (`⇒-elim ⊢f ⊢x) (ξ-$ᵣ _ →x₁) (ξ-$ᵣ _ →x₂) =
  `$-ap refl (deterministic ⊢x →x₁ →x₂)
  
deterministic (`×-elim₁ ⊢x) β-π₁ β-π₁ = refl
deterministic (`×-elim₁ ⊢x) (ξ-π₁ →x₁) (ξ-π₁ →x₂) = ap `π₁ (deterministic ⊢x →x₁ →x₂)
deterministic (`×-elim₂ ⊢x) β-π₂ β-π₂ = refl
deterministic (`×-elim₂ ⊢x) (ξ-π₂ →x₁) (ξ-π₂ →x₂) = ap `π₂ (deterministic ⊢x →x₁ →x₂)
```
