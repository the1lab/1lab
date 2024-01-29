<!--
```agda
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning as Cat
```
-->

```agda
module
  Cat.Displayed.Reasoning
    {o' ℓ' o'' ℓ''}
    {B : Precategory o' ℓ'}
    (E : Displayed B o'' ℓ'')
  where
```

# Reasoning in displayed categories

<!--
```agda
private
  module E = Displayed E
  module B = Cat B
  _ = Displayed.Hom[_] -- anchor for the reference below
```
-->

Contrary to the [reasoning combinators for precategories][catr],
reasoning in a [[displayed category]] is _much_ harder. The core of the
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
hom[ p ] f' = subst (λ h → E.Hom[ h ] _ _) p f'

hom[_]⁻ : ∀ {a b x y} {f g : B.Hom a b} → g ≡ f → E.Hom[ f ] x y → E.Hom[ g ] x y
hom[ p ]⁻ f' = hom[ sym p ] f'
```

Since equality in the base $\hom_b(-,-)$ is a proposition, we can always
adjust the path we're transporting over to get something more convenient.

```agda
reindex
  : ∀ {a b x y} {f g : B.Hom a b} (p q : f ≡ g) {f' : E.Hom[ f ] x y}
  → hom[ p ] f' ≡ hom[ q ] f'
reindex p q {f'} = ap (λ e → hom[ e ] f') (B.Hom-set _ _ _ _ p q)

cast[]
  : ∀ {a b x y} {f g : B.Hom a b} {f' : E.Hom[ f ] x y} {g' : E.Hom[ g ] x y}
  → {p q : f ≡ g}
  → f' E.≡[ p ] g'
  → f' E.≡[ q ] g'
cast[] {f = f} {g = g} {f' = f'} {g' = g'} {p = p} {q = q} r =
  coe0→1 (λ i → f' E.≡[ B.Hom-set _ _ f g p q i ] g') r
```


Next come the most important lemmas: Moving substitution in and out of
composite morphisms. The `whisker-r`{.Agda} combinator says that
substituting on the right of a composition is the same thing as
composing first, then adjusting by a path which leaves the "left"
composite unchanged.

```agda
hom[]-∙
  : ∀ {a b x y} {f g h : B.Hom a b} (p : f ≡ g) (q : g ≡ h)
      {f' : E.Hom[ f ] x y}
  → hom[ q ] (hom[ p ] f') ≡ hom[ p ∙ q ] f'
hom[]-∙ p q = sym (subst-∙ (λ h → E.Hom[ h ] _ _) _ _ _)

duplicate
  : ∀ {a b x y} {f f' g : B.Hom a b} (p : f ≡ g) (q : f' ≡ g) (r : f ≡ f')
      {f' : E.Hom[ f ] x y}
  → hom[ p ] f' ≡ hom[ q ] (hom[ r ] f')
duplicate p q r = reindex _ _ ∙ sym (hom[]-∙ r q)
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
  : ∀ {a b c} {f : B.Hom b c} {g g₁ : B.Hom a b} {a' b' c'}
      {f' : E.Hom[ f ] b' c'} {g' : E.Hom[ g ] a' b'}
  → (p : g ≡ g₁)
  → f' E.∘' hom[ p ] g' ≡ hom[ ap (f B.∘_) p ] (f' E.∘' g')
whisker-r {f = f} {a' = a'} {_} {c'} {f'} {g'} p i =
  comp (λ j → E.Hom[ f B.∘ p (i ∨ j) ] a' c') (∂ i) λ where
    j (i = i0) → f' E.∘' transport-filler (λ i → E.Hom[ p i ] _ _) g' j
    j (i = i1) → hom[ ap (f B.∘_) p ] (f' E.∘' g')
    j (j = i0) → transport-filler (λ i → E.Hom[ f B.∘ p i ] _ _) (f' E.∘' g') i

whisker-l
  : ∀ {a b c} {f f₁ : B.Hom b c} {g : B.Hom a b} {a' b' c'}
      {f' : E.Hom[ f ] b' c'} {g' : E.Hom[ g ] a' b'}
  → (p : f ≡ f₁)
  → hom[ p ] f' E.∘' g' ≡ hom[ ap (B._∘ g) p ] (f' E.∘' g')
whisker-l {g = g} {a'} {_} {c'} {f' = f'} {g' = g'} p i =
  comp (λ j → E.Hom[ p (i ∨ j) B.∘ g ] a' c') (∂ i) λ where
    j (i = i0) → transport-filler (λ i → E.Hom[ p i ] _ _) f' j E.∘' g'
    j (i = i1) → hom[ ap (B._∘ g) p ] (f' E.∘' g')
    j (j = i0) → transport-filler (λ i → E.Hom[ p i B.∘ g ] _ _) (f' E.∘' g') i
```

<!--
```agda
unwhisker-r
  : ∀ {a b c} {f : B.Hom b c} {g g₁ : B.Hom a b} {a' b' c'}
      {f' : E.Hom[ f ] b' c'} {g' : E.Hom[ g ] a' b'}
  → (p : f B.∘ g ≡ f B.∘ g₁) (q : g ≡ g₁)
  → hom[ p ] (f' E.∘' g') ≡ f' E.∘' hom[ q ] g'
unwhisker-r p q = reindex _ _ ∙ sym (whisker-r _)

unwhisker-l
  : ∀ {a b c} {f f₁ : B.Hom b c} {g : B.Hom a b} {a' b' c'}
      {f' : E.Hom[ f ] b' c'} {g' : E.Hom[ g ] a' b'}
  → (p : f B.∘ g ≡ f₁ B.∘ g) (q : f ≡ f₁)
  → hom[ p ] (f' E.∘' g') ≡ hom[ q ] f' E.∘' g'
unwhisker-l p q = reindex _ _ ∙ sym (whisker-l _)
```
-->

The rest of this module is made up of grueling applications of the three
lemmas above:

```agda
smashr
  : ∀ {a b c} {f : B.Hom b c} {g g₁ : B.Hom a b} {h : B.Hom a c} {a' b' c'}
      {f' : E.Hom[ f ] b' c'} {g' : E.Hom[ g ] a' b'}
  → (p : g ≡ g₁) (q : f B.∘ g₁ ≡ h)
  → hom[ q ] (f' E.∘' hom[ p ] g') ≡ hom[ ap (f B.∘_) p ∙ q ] (f' E.∘' g')
smashr p q = ap hom[ q ] (whisker-r p) ∙ hom[]-∙ _ _

smashl
  : ∀ {a b c} {f f₁ : B.Hom b c} {g : B.Hom a b} {h : B.Hom a c} {a' b' c'}
      {f' : E.Hom[ f ] b' c'} {g' : E.Hom[ g ] a' b'}
  → (p : f ≡ f₁) (q : f₁ B.∘ g ≡ h)
  → hom[ q ] (hom[ p ] f' E.∘' g') ≡ hom[ ap (B._∘ g) p ∙ q ] (f' E.∘' g')
smashl p q = ap hom[ q ] (whisker-l p) ∙ hom[]-∙ _ _

expandl
  : ∀ {a b c} {f f₁ : B.Hom b c} {g : B.Hom a b} {h : B.Hom a c} {a' b' c'}
      {f' : E.Hom[ f ] b' c'} {g' : E.Hom[ g ] a' b'}
  → (p : f ≡ f₁) (q : f B.∘ g ≡ h)
  → hom[ q ] (f' E.∘' g') ≡ hom[ ap (B._∘ g) (sym p) ∙ q ] (hom[ p ] f' E.∘' g')
expandl p q = reindex q _ ∙ (sym $ smashl _ _)

expandr
  : ∀ {a b c} {f : B.Hom b c} {g g₁ : B.Hom a b} {h : B.Hom a c} {a' b' c'}
      {f' : E.Hom[ f ] b' c'} {g' : E.Hom[ g ] a' b'}
  → (p : g ≡ g₁) (q : f B.∘ g ≡ h)
  → hom[ q ] (f' E.∘' g') ≡ hom[ ap (f B.∘_) (sym p) ∙ q ] (f' E.∘' hom[ p ] g')
expandr p q = reindex q _ ∙ (sym $ smashr _ _)

yank
  : ∀ {a b c d}
      {f : B.Hom c d} {g : B.Hom b c} {h : B.Hom a b} {i : B.Hom a c} {j : B.Hom b d}
      {a' b' c' d'}
      {f' : E.Hom[ f ] c' d'} {g' : E.Hom[ g ] b' c'} {h' : E.Hom[ h ] a' b'}
      (p : g B.∘ h ≡ i) (q : f B.∘ g ≡ j) (r : f B.∘ i ≡ j B.∘ h)
  → (f' E.∘' hom[ p ](g' E.∘' h')) E.≡[ r ] hom[ q ] (f' E.∘' g') E.∘' h'
yank {f' = f'} {g' = g'} {h' = h'} p q r = to-pathp $
  hom[ r ] (f' E.∘' hom[ p ] (g' E.∘' h'))                                             ≡⟨ smashr p r ⟩
  hom[ ap (B._∘_ _) p ∙ r ] (f' E.∘' g' E.∘' h')                                       ≡⟨ ap hom[ _ ] (sym (from-pathp λ i → E.assoc' f' g' h' (~ i))) ⟩
  hom[ ap (B._∘_ _) p ∙ r  ] (hom[ sym (B.assoc _ _ _) ] ((f' E.∘' g') E.∘' h'))       ≡⟨ hom[]-∙ _ _ ⟩
  hom[ sym (B.assoc _ _ _) ∙ (ap (B .Precategory._∘_ _) p ∙ r)] ((f' E.∘' g') E.∘' h') ≡⟨ reindex _ _ ⟩
  hom[ (ap (B._∘ _) q) ] ((f' E.∘' g') E.∘' h')                                        ≡˘⟨ whisker-l q ⟩
  hom[ q ] (f' E.∘' g') E.∘' h' ∎

cancel
  : ∀ {a b} {f g : B.Hom a b} (p q : f ≡ g) {a' b'}
    {f' : E.Hom[ f ] a' b'} {g' : E.Hom[ g ] a' b'}
  → PathP (λ i → E.Hom[ q i ] a' b') f' g'
  → hom[ p ] f' ≡ g'
cancel p q r = reindex p q ∙ from-pathp r

kill₁
  : ∀ {a b} {a' b'} {f g h : B.Hom a b} {h₁' : E.Hom[ f ] a' b'} {h₂' : E.Hom[ g ] a' b'}
  → (p : f ≡ g) (q : g ≡ h)
  → PathP (λ i → E.Hom[ p i ] a' b') h₁' h₂'
  → hom[ p ∙ q ] h₁' ≡ hom[ q ] h₂'
kill₁ p q r = sym (hom[]-∙ _ _) ∙ ap hom[ q ] (from-pathp r)


revive₁ : ∀ {a b} {f g h : B.Hom a b}
           {a' b'} {f' : E.Hom[ f ] a' b'} {g' : E.Hom[ g ] a' b'}
       → {p : f ≡ g} {q : f ≡ h}
       → f' E.≡[ p ] g'
       → hom[ q ] f' ≡ hom[ sym p ∙ q ] g'
revive₁ {f' = f'} {g' = g'} {p = p} {q = q} p' =
  hom[ q ] f'             ≡⟨ reindex _ _ ⟩
  hom[ p ∙ sym p ∙ q ] f' ≡⟨ kill₁ p (sym p ∙ q) p' ⟩
  hom[ sym p ∙ q ] g'     ∎

-- Idea: p is equal to some composite p' ∙ q, but it's misassociated or
-- something. We combine the reindexing to fix the association and
-- killing the first parameter to "weave" here.
weave
  : ∀ {a b} {a' b'} {f g h : B.Hom a b} {h₁' : E.Hom[ f ] a' b'} {h₂' : E.Hom[ g ] a' b'}
  → (p : f ≡ h) (p' : f ≡ g) (q : g ≡ h)
  → PathP (λ i → E.Hom[ p' i ] a' b') h₁' h₂'
  → hom[ p ] h₁' ≡ hom[ q ] h₂'
weave p p' q s =
    reindex p (p' ∙ q)
  ∙ kill₁ p' q s

split
  : ∀ {a b c} {f f₁ : B.Hom b c} {g g₁ : B.Hom a b} {a' b' c'}
      {f' : E.Hom[ f ] b' c'} {g' : E.Hom[ g ] a' b'}
      (p : f ≡ f₁) (q : g ≡ g₁)
  → hom[ ap₂ B._∘_ p q ] (f' E.∘' g') ≡ hom[ p ] f' E.∘' hom[ q ] g'
split p q =
     reindex _ (ap₂ B._∘_ p refl ∙ ap₂ B._∘_ refl q)
  ·· sym (hom[]-∙ _ _)
  ·· ap hom[ _ ] (sym (whisker-l p)) ∙ sym (whisker-r q)

liberate
  : ∀ {a b x y} {f : B.Hom a b} {f' : E.Hom[ f ] x y}
      (p : f ≡ f)
    → hom[ p ] f' ≡ f'
liberate p = reindex p refl ∙ transport-refl _

hom[]⟩⟨_
  : ∀ {a b} {f f' : B.Hom a b} {a' b'} {p : f ≡ f'}
      {f' g' : E.Hom[ f ] a' b'}
  → f' ≡ g'
  → hom[ p ] f' ≡ hom[ p ] g'
hom[]⟩⟨_ = ap hom[ _ ]

_⟩∘'⟨_
  : ∀ {a b c} {f f' : B.Hom b c} {g g' : B.Hom a b} {a' b' c'}
      {f₁' : E.Hom[ f ] b' c'} {f₂' : E.Hom[ f' ] b' c'}
      {g₁' : E.Hom[ g ] a' b'} {g₂' : E.Hom[ g' ] a' b'}
      {p : f ≡ f'} {q : g ≡ g'}
  → f₁' E.≡[ p ] f₂'
  → g₁' E.≡[ q ] g₂'
  → f₁' E.∘' g₁' E.≡[ ap₂ B._∘_ p q ] f₂' E.∘' g₂'
(p ⟩∘'⟨ q) i = p i E.∘' q i

_⟩∘'⟨refl
  : ∀ {a b c} {f f' : B.Hom b c} {g : B.Hom a b} {a' b' c'}
      {f₁' : E.Hom[ f ] b' c'} {f₂' : E.Hom[ f' ] b' c'} {g' : E.Hom[ g ] a' b'}
      {p : f ≡ f'}
  → f₁' E.≡[ p ] f₂'
  → f₁' E.∘' g' E.≡[ p B.⟩∘⟨refl ] f₂' E.∘' g'
_⟩∘'⟨refl {g' = g'} p = apd (λ _ → E._∘' g') p

refl⟩∘'⟨_
  : ∀ {a b c} {f : B.Hom b c} {g g' : B.Hom a b} {a' b' c'}
      {f' : E.Hom[ f ] b' c'}
      {g₁' : E.Hom[ g ] a' b'} {g₂' : E.Hom[ g' ] a' b'}
      {q : g ≡ g'}
  → g₁' E.≡[ q ] g₂'
  → f' E.∘' g₁' E.≡[ B.refl⟩∘⟨ q ] f' E.∘' g₂'
refl⟩∘'⟨_ {f' = f'} p = apd (λ _ → f' E.∘'_) p

split⟩⟨_
  : ∀ {a b c} {f f' : B.Hom b c} {g g' : B.Hom a b} {a' b' c'}
      {f₁' : E.Hom[ f ] b' c'} {f₂' : E.Hom[ f' ] b' c'}
      {g₁' : E.Hom[ g ] a' b'} {g₂' : E.Hom[ g' ] a' b'}
      {p : f ≡ f'} {q : g ≡ g'}
  → hom[ p ] f₁' E.∘' hom[ q ] g₁' ≡ f₂' E.∘' g₂'
  → hom[ ap₂ B._∘_ p q ] (f₁' E.∘' g₁') ≡ f₂' E.∘' g₂'
split⟩⟨ p = split _ _ ∙ p

infixr 5 _⟩∘'⟨_ refl⟩∘'⟨_ _⟩∘'⟨refl
infixl 4 split⟩⟨_ hom[]⟩⟨_

hom[] : ∀ {a b x y} {f g : B.Hom a b} {p : f ≡ g} → E.Hom[ f ] x y → E.Hom[ g ] x y
hom[] {p = p} f' = hom[ p ] f'

pulll-indexr
  : ∀ {a b c d} {f : B.Hom c d} {g : B.Hom b c} {h : B.Hom a b} {ac : B.Hom a c}
      {a' : E.Ob[ a ]} {b' : E.Ob[ b ]} {c' : E.Ob[ c ]} {d' : E.Ob[ d ]}
      {f' : E.Hom[ f ] c' d'}
      {g' : E.Hom[ g ] b' c'}
      {h' : E.Hom[ h ] a' b'}
      {fg' : E.Hom[ f B.∘ g ] b' d'}
  → (p : g B.∘ h ≡ ac)
  → (f' E.∘' g' ≡ fg')
  → f' E.∘' hom[ p ] (g' E.∘' h') ≡ hom[ B.pullr p ] (fg' E.∘' h')
pulll-indexr p q = whisker-r _ ∙
  sym ( reindex _ (sym (B.assoc _ _ _) ∙ ap (_ B.∘_) p) ·· sym (hom[]-∙ _ _)
    ·· ap hom[] ( ap hom[] (ap (E._∘' _) (sym q))
                ∙ from-pathp (symP (E.assoc' _ _ _))))
```

Using these tools, we can define displayed versions of the usual category
reasoning combinators.

<!--
```agda
open Cat B
open Displayed E

private variable
  u w x y z : Ob
  a b c d f g h i : Hom x y
  u' w' x' y' y'' z' : Ob[ x ]
  a' b' c' d' f' g' h' i' : Hom[ a ] x' y'
```
-->

<!--
```agda
wrap
  : ∀ {f g : Hom x y} {f' : Hom[ f ] x' y'}
  → (p : f ≡ g)
  → f' ≡[ p ] hom[ p ] f'
wrap p = to-pathp refl

wrapl
  : ∀ {f h : Hom y z} {g : Hom x y} {f' : Hom[ f ] y' z'} {g' : Hom[ g ] x' y'}
  → (p : f ≡ h)
  → f' ∘' g' ≡[ ap (_∘ g) p ] hom[ p ] f' ∘' g'
wrapl p = to-pathp (unwhisker-l (ap (_∘ _) p) p)

unwrap
  : ∀ {f g : Hom x y} {f' : Hom[ f ] x' y'}
  → (p : f ≡ g)
  → hom[ p ] f' ≡[ sym p ] f'
unwrap p = to-pathp⁻ refl

wrapr
  : ∀ {f : Hom y z} {g h : Hom x y} {f' : Hom[ f ] y' z'} {g' : Hom[ g ] x' y'}
  → (p : g ≡ h)
  → f' ∘' g' ≡[ ap (f ∘_) p ] f' ∘' hom[ p ] g'
wrapr p = to-pathp (unwhisker-r (ap (_ ∘_) p) p)

unwrapl
  : ∀ {f h : Hom y z} {g : Hom x y} {f' : Hom[ f ] y' z'} {g' : Hom[ g ] x' y'}
  → (p : f ≡ h)
  → hom[ p ] f' ∘' g' ≡[ ap (_∘ g) (sym p) ] f' ∘' g'
unwrapl p = to-pathp⁻ (whisker-l p)

unwrapr
  : ∀ {f : Hom y z} {g h : Hom x y} {f' : Hom[ f ] y' z'} {g' : Hom[ g ] x' y'}
  → (p : g ≡ h)
  → f' ∘' hom[ p ]  g' ≡[ ap (f ∘_) (sym p) ] f' ∘' g'
unwrapr p = to-pathp⁻ (whisker-r p)
```
-->

## Shiftings

When working with displayed categories, we prefer to write all of our laws
using `PathP`{.Agda}, as this is conceptually cleaner and avoids coherence
issues. However, when performing equational reasoning, we use regular
paths and `hom[_]`{.Agda}. To resolve this mismatch, we define the following
combinators.

```agda
module _ {f' : Hom[ f ] x' y'} {g' : Hom[ g ] x' y'} (p : f ≡ g) where abstract
  shiftl : f' ≡[ p ] g' → hom[ p ] f' ≡ g'
  shiftl q i = from-pathp (λ j → q (i ∨ j)) i

  shiftr : f' ≡[ p ] g' → f' ≡ hom[ p ]⁻ g'
  shiftr q i = from-pathp (λ j → q (i ∧ ~ j)) (~ i)
```

## Path actions

Due to the plethora of `PathP`{.Agda}, we can no longer perform `ap`{.Agda} as easily.
This is especially true when we have a `PathP`{.Agda} as well as a path between
two `hom[_]`{.Agda}. These combinators allow us to more ergonomically handle that
situation.

```agda
module _ {f' : Hom[ f ] y' z'} {g' : Hom[ g ] x' y'} {p : f ∘ g ≡ a} where abstract

  apl' : ∀ {h' : Hom[ h ] y' z'} {q : h ∘ g ≡ a}
          → {f≡h : f ≡ h}
          → f' ≡[ f≡h ] h'
          → hom[ p ] (f' ∘' g') ≡ hom[ q ] (h' ∘' g')
  apl' {h' = h'} {q = q} {f≡h = f≡h} f'≡h' =
    hom[ p ] (f' ∘' g')                       ≡⟨ hom[]⟩⟨ (ap (_∘' g') (shiftr _ f'≡h')) ⟩
    hom[ p ] (hom[ f≡h ]⁻ h' ∘' g')           ≡⟨ smashl _ _ ⟩
    hom[ ap (_∘ g) (sym f≡h) ∙ p ] (h' ∘' g') ≡⟨ reindex _ _ ⟩
    hom[ q ] (h' ∘' g') ∎

  apr' : ∀ {h' : Hom[ h ] x' y'} {q : f ∘ h ≡ a}
          → {g≡h : g ≡ h}
          → g' ≡[ g≡h ] h'
          → hom[ p ] (f' ∘' g') ≡ hom[ q ] (f' ∘' h')
  apr' {h' = h'} {q = q} {g≡h = g≡h} g'≡h' =
    hom[ p ] (f' ∘' g')                       ≡⟨ hom[]⟩⟨ ap (f' ∘'_) (shiftr _ g'≡h') ⟩
    hom[ p ] (f' ∘' hom[ g≡h ]⁻ h')           ≡⟨ smashr _ _ ⟩
    hom[ ap (f ∘_) (sym g≡h) ∙ p ] (f' ∘' h') ≡⟨ reindex _ _ ⟩
    hom[ q ] (f' ∘' h') ∎
```


## Generalized category laws

In the definition of displayed categories, the identity and associativity
laws are defined over `idl`{.Agda}, `idr`{.Agda}, and `assoc`{.Agda}. However,
we often run into situations where we need to apply these equations over
different equations! These combinators do just that.

```agda
module _ {f' : Hom[ f ] x' y'} where abstract
  idl[] : {p : id ∘ f ≡ f} → hom[ p ] (id' ∘' f') ≡ f'
  idl[] {p = p} = reindex p (idl _) ∙ from-pathp (idl' f')

  idr[] : {p : f ∘ id ≡ f} → hom[ p ] (f' ∘' id') ≡ f'
  idr[] {p = p} = reindex p (idr _) ∙ from-pathp (idr' f')

assoc[] : ∀ {a' : Hom[ a ] y' z'} {b' : Hom[ b ] x' y'} {c' : Hom[ c ] w' x'}
            {p : a ∘ (b ∘ c) ≡ d} {q : (a ∘ b) ∘ c ≡ d}
          → hom[ p ] (a' ∘' (b' ∘' c')) ≡ hom[ q ] ((a' ∘' b') ∘' c')
assoc[] {a = a} {b = b} {c =  c} {a' = a'} {b' = b'} {c' = c'} {p = p} {q = q} =
  hom[ p ] (a' ∘' b' ∘' c')                         ≡⟨ hom[]⟩⟨ shiftr (assoc a b c) (assoc' a' b' c') ⟩
  hom[ p ] (hom[ assoc a b c ]⁻ ((a' ∘' b') ∘' c')) ≡⟨ hom[]-∙ _ _ ⟩
  hom[ sym (assoc a b c) ∙ p ] ((a' ∘' b') ∘' c')   ≡⟨ reindex _ q ⟩
  hom[ q ] ((a' ∘' b') ∘' c')                       ∎
```

## Identity morphisms

These are the displayed counterparts to the
[identity morphism combinators] for categories.

[identity morphism combinators]: Cat.Reasoning.html#identity-morphisms

```agda
module _ {a' : Hom[ a ] x' x'}
         (p : a ≡ id) (p' : a' ≡[ p ] id') where abstract
  eliml' : ∀ {f' : Hom[ f ] y' x'} → {q : a ∘ f ≡ f} → a' ∘' f' ≡[ q ] f'
  eliml' {f = f} {f' = f'} {q = q} = to-pathp $
    hom[ q ] (a' ∘' f')      ≡⟨ apl' p' ⟩
    hom[ idl f ] (id' ∘' f') ≡⟨ idl[] ⟩
    f' ∎

  elimr' : ∀ {f' : Hom[ f ] x' y'} → {q : f ∘ a ≡ f} → f' ∘' a' ≡[ q ] f'
  elimr' {f = f} {f' = f'} {q = q} = to-pathp $
    hom[ q ] (f' ∘' a')      ≡⟨ apr' p' ⟩
    hom[ idr f ] (f' ∘' id') ≡⟨ idr[] ⟩
    f' ∎

  introl' : ∀ {f' : Hom[ f ] y' x'} → {q : f ≡ a ∘ f} → f' ≡[ q ] a' ∘' f'
  introl' {f' = f'} {q = q} i = eliml' {f' = f'} {q = sym q} (~ i)

  intror' : ∀ {f' : Hom[ f ] x' y'} → {q : f ≡ f ∘ a} → f' ≡[ q ] f' ∘' a'
  intror' {f' = f'} {q = q} i = elimr' {f' = f'} {q = sym q} (~ i)
```

## Reassociations

These are the displayed counterparts to the reassociation combinators
for categories.

```agda
module _ {a' : Hom[ a ] y' z'} {b' : Hom[ b ] x' y'} {c' : Hom[ c ] x' z'}
         (p : a ∘ b ≡ c) (p' : a' ∘' b' ≡[ p ] c') where abstract

  pulll' : ∀ {f' : Hom[ f ] w' x'} {q : a ∘ (b ∘ f) ≡ c ∘ f}
           → a' ∘' (b' ∘' f') ≡[ q ] c' ∘' f'
  pulll' {f = f} {f' = f'} {q = q} = to-pathp $
    hom[ q ] (a' ∘' b' ∘' f')                       ≡⟨ assoc[] ⟩
    hom[ sym (assoc a b f) ∙ q ] ((a' ∘' b') ∘' f') ≡⟨ apl' p' ⟩
    hom[ refl ] (c' ∘' f')                          ≡⟨ liberate _ ⟩
    c' ∘' f'                                        ∎

  pulll[] : ∀ {f' : Hom[ f ] w' x'}
           → a' ∘' (b' ∘' f') ≡[ pulll p ] c' ∘' f'
  pulll[] = pulll'

  pullr' : ∀ {f' : Hom[ f ] z' w'} {q : (f ∘ a) ∘ b ≡ f ∘ c}
         → (f' ∘' a') ∘' b' ≡[ q ] f' ∘' c'
  pullr' {f = f} {f' = f'} {q = q} = to-pathp $
    hom[ q ] ((f' ∘' a') ∘' b')             ≡˘⟨ assoc[] ⟩
    hom[ assoc f a b ∙ q ] (f' ∘' a' ∘' b') ≡⟨ apr' p' ⟩
    hom[ refl ] (f' ∘' c')                  ≡⟨ liberate _ ⟩
    f' ∘' c'                                ∎

  pullr[] : ∀ {f' : Hom[ f ] z' w'}
          → (f' ∘' a') ∘' b' ≡[ pullr p ] f' ∘' c'
  pullr[] = pullr'

module _ {a' : Hom[ a ] y' z'} {b' : Hom[ b ] x' y'} {c' : Hom[ c ] x' z'}
         (p : c ≡ a ∘ b) (p' : c' ≡[ p ] a' ∘' b') where abstract

  pushl' : ∀ {f' : Hom[ f ] w' x'} {q : c ∘ f ≡ a ∘ (b ∘ f)}
           → c' ∘' f' ≡[ q ] a' ∘' (b' ∘' f')
  pushl' {f' = f'} {q = q} i =
    pulll' (sym p) (λ j → p' (~ j)) {f' = f'} {q = sym q} (~ i)

  pushl[] : ∀ {f' : Hom[ f ] w' x'}
           → c' ∘' f' ≡[ pushl p ] a' ∘' (b' ∘' f')
  pushl[] = pushl'

  pushr' : ∀ {f' : Hom[ f ] z' w'} {q : f ∘ c ≡ (f ∘ a) ∘ b}
           → f' ∘' c' ≡[ q ] (f' ∘' a') ∘' b'
  pushr' {f' = f'} {q = q} i =
    pullr' (sym p) (λ j → p' (~ j)) {f' = f'} {q = sym q} (~ i)

  pushr[] : ∀ {f' : Hom[ f ] z' w'}
           → f' ∘' c' ≡[ pushr p ] (f' ∘' a') ∘' b'
  pushr[] = pushr'

module _ {f' : Hom[ f ] y' z'} {h' : Hom[ h ] x' y'}
         {g' : Hom[ g ] y'' z'} {i' : Hom[ i ] x' y''}
         (p : f ∘ h ≡ g ∘ i) (p' : f' ∘' h' ≡[ p ] g' ∘' i') where abstract

  extendl' : ∀ {b' : Hom[ b ] w' x'} {q : f ∘ (h ∘ b) ≡ g ∘ (i ∘ b)}
             → f' ∘' (h' ∘' b') ≡[ q ] g' ∘' (i' ∘' b')
  extendl' {b = b} {b' = b'} {q = q} = to-pathp $
    hom[ q ] (f' ∘' h' ∘' b')                       ≡⟨ assoc[] ⟩
    hom[ sym (assoc f h b) ∙ q ] ((f' ∘' h') ∘' b') ≡⟨ apl' p' ⟩
    hom[ sym (assoc g i b) ] ((g' ∘' i') ∘' b')     ≡⟨ shiftl _ (λ j → (assoc' g' i' b') (~ j)) ⟩
    g' ∘' i' ∘' b'                                  ∎

  extendr' : ∀ {a' : Hom[ a ] z' w'} {q : (a ∘ f) ∘ h ≡ (a ∘ g) ∘ i}
             → (a' ∘' f') ∘' h' ≡[ q ] (a' ∘' g') ∘' i'
  extendr' {a = a} {a' = a'} {q = q} = to-pathp $
    hom[ q ] ((a' ∘' f') ∘' h')             ≡˘⟨ assoc[] ⟩
    hom[ assoc a f h ∙ q ] (a' ∘' f' ∘' h') ≡⟨ apr' p' ⟩
    hom[ assoc a g i ] (a' ∘'(g' ∘' i'))    ≡⟨ shiftl _ (assoc' a' g' i') ⟩
    (a' ∘' g') ∘' i' ∎

  extend-inner' : ∀ {a' : Hom[ a ] z' u'} {b' : Hom[ b ] w' x'}
                    {q : a ∘ f ∘ h ∘ b ≡ a ∘ g ∘ i ∘ b}
                  → a' ∘' f' ∘' h' ∘' b' ≡[ q ] a' ∘' g' ∘' i' ∘' b'
  extend-inner' {a = a} {b = b} {a' = a'} {b' = b'} {q = q} = to-pathp $
    hom[ q ] (a' ∘' f' ∘' h' ∘' b')                                   ≡⟨ apr' (assoc' f' h' b') ⟩
    hom[ ap (a ∘_) (sym (assoc f h b)) ∙ q ] (a' ∘' (f' ∘' h') ∘' b') ≡⟨ apr' (λ j → p' j ∘' b') ⟩
    hom[ ap (a ∘_) (sym (assoc g i b)) ] (a' ∘' (g' ∘' i') ∘' b')     ≡⟨ shiftl _ (λ j → a' ∘' assoc' g' i' b' (~ j)) ⟩
    a' ∘' g' ∘' i' ∘' b' ∎

  extendl[] : ∀ {b' : Hom[ b ] w' x'}
             → f' ∘' (h' ∘' b') ≡[ extendl p ] g' ∘' (i' ∘' b')
  extendl[] = extendl'

  extendr[] : ∀ {a' : Hom[ a ] z' w'}
             → (a' ∘' f') ∘' h' ≡[ extendr p ] (a' ∘' g') ∘' i'
  extendr[] = extendr'
```

## Cancellation

These are the displayed counterparts to the [cancellation combinators]
for categories

[cancellation combinators]: Cat.Reasoning.html#cancellation

```agda
module _ {a' : Hom[ a ] y' x'} {b' : Hom[ b ] x' y'}
         (p : a ∘ b ≡ id) (p' : a' ∘' b' ≡[ p ] id') where abstract

  cancell' : ∀ {f' : Hom[ f ] z' x'} {q : a ∘ b ∘ f ≡ f}
             → a' ∘' b' ∘' f' ≡[ q ] f'
  cancell' {f = f} {f' = f'} {q = q} = to-pathp $
    hom[ q ] (a' ∘' b' ∘' f')                       ≡⟨ assoc[] ⟩
    hom[ sym (assoc a b f) ∙ q ] ((a' ∘' b') ∘' f') ≡⟨ shiftl _ (eliml' p p') ⟩
    f'                                              ∎

  cancell[] : ∀ {f' : Hom[ f ] z' x'}
             → a' ∘' b' ∘' f' ≡[ cancell p ] f'
  cancell[] = cancell'

  cancelr' : ∀ {f' : Hom[ f ] x' z'} {q : (f ∘ a) ∘ b ≡ f}
             → (f' ∘' a') ∘' b' ≡[ q ] f'
  cancelr' {f = f} {f' = f'} {q = q} = to-pathp $
    hom[ q ] ((f' ∘' a') ∘' b')             ≡˘⟨ assoc[] ⟩
    hom[ assoc f a b ∙ q ] (f' ∘' a' ∘' b') ≡⟨ shiftl _ (elimr' p p') ⟩
    f' ∎

  cancelr[] : ∀ {f' : Hom[ f ] x' z'}
             → (f' ∘' a') ∘' b' ≡[ cancelr p ] f'
  cancelr[] = cancelr'

  cancel-inner' : ∀ {f' : Hom[ f ] x' z'} {g' : Hom[ g ] w' x'}
    → {q : (f ∘ a) ∘ (b ∘ g) ≡ f ∘ g}
    → (f' ∘' a') ∘' (b' ∘' g') ≡[ q ] f' ∘' g'
  cancel-inner' = cast[] $ pullr[] _ cancell[]

  cancel-inner[] : ∀ {f' : Hom[ f ] x' z'} {g' : Hom[ g ] w' x'}
    → (f' ∘' a') ∘' (b' ∘' g') ≡[ cancel-inner p ] f' ∘' g'
  cancel-inner[] = cancel-inner'

  insertl' : ∀ {f' : Hom[ f ] z' x'} {q : f ≡ a ∘ b ∘ f }
             → f' ≡[ q ] a' ∘' b' ∘' f'
  insertl' {f = f} {f' = f'} {q = q} i = cancell' {f' = f'} {q = sym q} (~ i)

  insertr' : ∀ {f' : Hom[ f ] x' z'} {q : f ≡ (f ∘ a) ∘ b }
             → f' ≡[ q ] (f' ∘' a') ∘' b'
  insertr' {f = f} {f' = f'} {q = q} i = cancelr' {f' = f'} {q = sym q} (~ i)
```
