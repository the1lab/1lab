```agda
open import Cat.Instances.Functor
open import Cat.Displayed.Base
open import Cat.Prelude

module
  Cat.Displayed.Reasoning
    {o′ ℓ′ o′′ ℓ′′}
    {B : Precategory o′ ℓ′}
    (E : Displayed B o′′ ℓ′′)
  where
```

# Reasoning in displayed categories

<!--
```agda
private
  module E = Displayed E
  module B = Precategory B
  _ = Displayed.Hom[_] -- anchor for the reference below
```
-->

Contrary to the [reasoning combinators for precategories][catr],
reasoning in a displayed category is _much_ harder. The core of the
problem is that the type `Displayed.Hom[_]`{.Agda} of displayed
morphisms is _dependent_, so all but the most trivial paths over it will
similarly be `dependent paths`{.Agda ident=PathP}. We prefer to work
instead with non-dependent paths and substitution, using the
`from-pathp`{.Agda} and `to-pathp`{.Agda} combinators to adjust to the
situation.

[catr]: Cat.Reasoning.html

A fundamental operator is moving a morphism between displayed
$\hom$-spaces depending on a path in the base category, so we provide a
shorthand syntax for that here. You can think of this as being an
abbreviation for `subst`{.Agda} because... that's what it is.

```agda
hom[_] : ∀ {a b x y} {f g : B.Hom a b} → f ≡ g → E.Hom[ f ] x y → E.Hom[ g ] x y
hom[ p ] f′ = subst (λ h → E.Hom[ h ] _ _) p f′

hom[_]⁻ : ∀ {a b x y} {f g : B.Hom a b} → g ≡ f → E.Hom[ f ] x y → E.Hom[ g ] x y
hom[ p ]⁻ f′ = subst (λ h → E.Hom[ h ] _ _) (sym p) f′
```

Since equality in the base $\hom_b(-,-)$ is a proposition, we can always
adjust the path we're transporting over to get something more convenient.

```agda
reindex
  : ∀ {a b x y} {f g : B.Hom a b} (p q : f ≡ g) {f′ : E.Hom[ f ] x y}
  → hom[ p ] f′ ≡ hom[ q ] f′
reindex p q {f′} = ap (λ e → hom[ e ] f′) (B.Hom-set _ _ _ _ p q)
```

Next come the most important lemmas: Moving substitution in and out of
composite morphisms. The `hom[]-whisker-r`{.Agda} combinator says that
substituting on the right of a composition is the same thing as
composing first, then adjusting by a path which leaves the "left"
composite unchanged.

```agda
hom[]-∙
  : ∀ {a b x y} {f g h : B.Hom a b} (p : f ≡ g) (q : g ≡ h)
      {f′ : E.Hom[ f ] x y}
  → hom[ q ] (hom[ p ] f′) ≡ hom[ p ∙ q ] f′
hom[]-∙ p q = sym (subst-∙ (λ h → E.Hom[ h ] _ _) _ _ _)
```

To understand why these whiskering lemmas have such complicated types,
recall that the "displayed composition" operator has type

$$
\hom_f(b, c) \times \hom_g(a, b) \to \hom_{f \circ g}(a, c)\text{,}
$$

so if we have some path $p : g = g'$, the composite $f \circ p_*g$ will
have type $\hom_{f \circ g'}(-,-)$, but the composite $f \circ g$ has
type $\hom_{f \circ g}(-,-)$. Hence the need to adjust that composite:
we can't just get rid of the transport $p^*(-)$.

```agda
whisker-r
  : ∀ {a b c} {f : B.Hom b c} {g g' : B.Hom a b} {a′ b′ c′}
      {f′ : E.Hom[ f ] b′ c′} {g′ : E.Hom[ g ] a′ b′}
  → (p : g ≡ g')
  → f′ E.∘′ hom[ p ] g′ ≡ hom[ ap (f B.∘_) p ] (f′ E.∘′ g′)
whisker-r {f = f} {a′ = a′} {_} {c′} {f′} {g′} p i =
  comp
    (λ j → E.Hom[ f B.∘ p (i ∨ j) ] a′ c′)
    (λ { j (i = i0) → f′ E.∘′ transport-filler (λ i → E.Hom[ p i ] _ _) g′ j
       ; j (i = i1) → hom[ ap (f B.∘_) p ] (f′ E.∘′ g′)
       })
    (transport-filler (λ i → E.Hom[ f B.∘ p i ] _ _) (f′ E.∘′ g′) i)

whisker-l
  : ∀ {a b c} {f f' : B.Hom b c} {g : B.Hom a b} {a′ b′ c′}
      {f′ : E.Hom[ f ] b′ c′} {g′ : E.Hom[ g ] a′ b′}
  → (p : f ≡ f')
  → hom[ p ] f′ E.∘′ g′ ≡ hom[ ap (B._∘ g) p ] (f′ E.∘′ g′)
whisker-l {g = g} {a′} {_} {c′} {f′ = f′} {g′ = g′} p i =
  comp
    (λ j → E.Hom[ p (i ∨ j) B.∘ g ] a′ c′)
    (λ { j (i = i0) → transport-filler (λ i → E.Hom[ p i ] _ _) f′ j E.∘′ g′
       ; j (i = i1) → hom[ ap (B._∘ g) p ] (f′ E.∘′ g′)
       })
    (transport-filler (λ i → E.Hom[ p i B.∘ g ] _ _) (f′ E.∘′ g′) i)
```

The rest of this module is made up of grueling applications of the three
lemmas above:

```agda
smashr
  : ∀ {a b c} {f : B.Hom b c} {g g' : B.Hom a b} {h : B.Hom a c} {a′ b′ c′}
      {f′ : E.Hom[ f ] b′ c′} {g′ : E.Hom[ g ] a′ b′}
  → (p : g ≡ g') (q : f B.∘ g' ≡ h)
  → hom[ q ] (f′ E.∘′ hom[ p ] g′) ≡ hom[ ap (f B.∘_) p ∙ q ] (f′ E.∘′ g′)
smashr p q = ap hom[ q ] (whisker-r p) ∙ hom[]-∙ _ _

smashl
  : ∀ {a b c} {f f' : B.Hom b c} {g : B.Hom a b} {h : B.Hom a c} {a′ b′ c′}
      {f′ : E.Hom[ f ] b′ c′} {g′ : E.Hom[ g ] a′ b′}
  → (p : f ≡ f') (q : f' B.∘ g ≡ h)
  → hom[ q ] (hom[ p ] f′ E.∘′ g′) ≡ hom[ ap (B._∘ g) p ∙ q ] (f′ E.∘′ g′)
smashl p q = ap hom[ q ] (whisker-l p) ∙ hom[]-∙ _ _

cancel
  : ∀ {a b} {f g : B.Hom a b} (p q : f ≡ g) {a′ b′}
    {f′ : E.Hom[ f ] a′ b′} {g′ : E.Hom[ g ] a′ b′}
  → PathP (λ i → E.Hom[ q i ] a′ b′) f′ g′
  → hom[ p ] f′ ≡ g′
cancel p q r = reindex p q ∙ from-pathp r

kill₁
  : ∀ {a b} {a′ b′} {f g h : B.Hom a b} {h₁′ : E.Hom[ f ] a′ b′} {h₂′ : E.Hom[ g ] a′ b′}
  → (p : f ≡ g) (q : g ≡ h)
  → PathP (λ i → E.Hom[ p i ] a′ b′) h₁′ h₂′
  → hom[ p ∙ q ] h₁′ ≡ hom[ q ] h₂′
kill₁ p q r = sym (hom[]-∙ _ _) ∙ ap hom[ q ] (from-pathp r)

-- Idea: p is equal to some composite p′ ∙ q, but it's mis-associated or
-- something. We combine the reindexing to fix the association and
-- killing the first parameter to "weave" here.
weave
  : ∀ {a b} {a′ b′} {f g h : B.Hom a b} {h₁′ : E.Hom[ f ] a′ b′} {h₂′ : E.Hom[ g ] a′ b′}
  → (p : f ≡ h) (p′ : f ≡ g) (q : g ≡ h)
  → PathP (λ i → E.Hom[ p′ i ] a′ b′) h₁′ h₂′
  → hom[ p ] h₁′ ≡ hom[ q ] h₂′
weave p p′ q s =
    reindex p (p′ ∙ q)
  ∙ kill₁ p′ q s

split
  : ∀ {a b c} {f f' : B.Hom b c} {g g' : B.Hom a b} {a′ b′ c′}
      {f′ : E.Hom[ f ] b′ c′} {g′ : E.Hom[ g ] a′ b′}
      (p : f ≡ f') (q : g ≡ g')
  → hom[ ap₂ B._∘_ p q ] (f′ E.∘′ g′) ≡ hom[ p ] f′ E.∘′ hom[ q ] g′
split p q =
     reindex _ (ap₂ B._∘_ p refl ∙ ap₂ B._∘_ refl q)
  ·· sym (hom[]-∙ _ _)
  ·· ap hom[ _ ] (sym (whisker-l p)) ∙ sym (whisker-r q)

hom[]⟩⟨_
  : ∀ {a b} {f f' : B.Hom a b} {a′ b′} {p : f ≡ f'}
      {f′ g′ : E.Hom[ f ] a′ b′}
  → f′ ≡ g′
  → hom[ p ] f′ ≡ hom[ p ] g′
hom[]⟩⟨_ = ap hom[ _ ]

_⟩∘′⟨_
  : ∀ {a b c} {f f' : B.Hom b c} {g g' : B.Hom a b} {a′ b′ c′}
      {f₁′ : E.Hom[ f ] b′ c′} {f₂′ : E.Hom[ f' ] b′ c′}
      {g₁′ : E.Hom[ g ] a′ b′} {g₂′ : E.Hom[ g' ] a′ b′}
      {p : f ≡ f'} {q : g ≡ g'}
  → PathP (λ i → E.Hom[ p i ] b′ c′) f₁′ f₂′
  → PathP (λ i → E.Hom[ q i ] a′ b′) g₁′ g₂′
  → hom[ p ] f₁′ E.∘′ hom[ q ] g₁′ ≡ f₂′ E.∘′ g₂′
p ⟩∘′⟨ q = ap₂ E._∘′_ (from-pathp p) (from-pathp q)

_⟩∘′⟨refl
  : ∀ {a b c} {f f' : B.Hom b c} {g : B.Hom a b} {a′ b′ c′}
      {f₁′ : E.Hom[ f ] b′ c′} {f₂′ : E.Hom[ f' ] b′ c′} {g′ : E.Hom[ g ] a′ b′}
      {p : f ≡ f'}
  → PathP (λ i → E.Hom[ p i ] b′ c′) f₁′ f₂′
  → hom[ p ] f₁′ E.∘′ g′ ≡ f₂′ E.∘′ g′
p ⟩∘′⟨refl = ap₂ E._∘′_ (from-pathp p) refl

refl⟩∘′⟨_
  : ∀ {a b c} {f : B.Hom b c} {g g' : B.Hom a b} {a′ b′ c′}
      {f′ : E.Hom[ f ] b′ c′}
      {g₁′ : E.Hom[ g ] a′ b′} {g₂′ : E.Hom[ g' ] a′ b′}
      {q : g ≡ g'}
  → PathP (λ i → E.Hom[ q i ] a′ b′) g₁′ g₂′
  → f′ E.∘′ hom[ q ] g₁′ ≡ f′ E.∘′ g₂′
refl⟩∘′⟨ p = ap₂ E._∘′_ refl (from-pathp p)

split⟩⟨_
  : ∀ {a b c} {f f' : B.Hom b c} {g g' : B.Hom a b} {a′ b′ c′}
      {f₁′ : E.Hom[ f ] b′ c′} {f₂′ : E.Hom[ f' ] b′ c′}
      {g₁′ : E.Hom[ g ] a′ b′} {g₂′ : E.Hom[ g' ] a′ b′}
      {p : f ≡ f'} {q : g ≡ g'}
  → hom[ p ] f₁′ E.∘′ hom[ q ] g₁′ ≡ f₂′ E.∘′ g₂′
  → hom[ ap₂ B._∘_ p q ] (f₁′ E.∘′ g₁′) ≡ f₂′ E.∘′ g₂′
split⟩⟨ p = split _ _ ∙ p

infixr 5 _⟩∘′⟨_ refl⟩∘′⟨_ _⟩∘′⟨refl
infixl 4 split⟩⟨_ hom[]⟩⟨_

hom[] : ∀ {a b x y} {f g : B.Hom a b} {p : f ≡ g} → E.Hom[ f ] x y → E.Hom[ g ] x y
hom[] {p = p} f′ = subst (λ h → E.Hom[ h ] _ _) p f′
```
