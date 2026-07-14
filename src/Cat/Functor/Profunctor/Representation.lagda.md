<!--
```agda
open import Cat.Functor.Naturality
open import Cat.Functor.Profunctor
open import Cat.Functor.Bifunctor
open import Cat.Instances.Product
open import Cat.Diagram.Product
open import Cat.Functor.Compose
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Functor.Profunctor.Representation where
```

# Profunctor representations

Every [[functor]] $F : \cC \to \cD$ induces, by precomposition with
$\cD$'s [[hom functor]], a [[profunctor]] $\cD(-, F-) : \cC \rel \cD$.
Fixing a profunctor $R : \cC \rel \cD$, we refer to the type of functors
$F : \cC \to \cD$ equipped with a [[natural isomorphism]] $R \cong
\cD(-, F-)$ as the type of **representations** of $R$.

<!--
```agda
private
  variable
    o ℓ o' ℓ' : Level
    C D : Precategory o ℓ

  rep-level
    : {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    → Profunctor C D ℓ'
    → Level
  rep-level {o = o} {ℓ = ℓ} {o' = o'} {ℓ' = ℓ'} R = o ⊔ ℓ ⊔ o' ⊔ ℓ'
```
-->

```agda
induced-profunctor : Functor C D → Profunctor C D _
induced-profunctor {D = D} = precompose₂ (Hom[-,-] D) Id

Representation : (R : Profunctor C D _) → Type (rep-level R)
Representation {C = C} {D = D} R =
  Σ[ F ∈ Functor C D ] (R ≅ⁿ induced-profunctor F)
```

## Functor presentations

The notion of profunctor representation can be used to explain the
"type-theoretic" presentation of universal constructions, that is, its
presentation in terms of formation rules, introduction and elimination
rules, and beta/eta laws. In particular, thinking of universal
constructions in terms of profunctor representations explains the common
"formula" for deriving functoriality of universal constructions from the
type-theoretic presentation.

```agda
record Right-presentation (R : Profunctor C D _) : Type (rep-level R) where
```

<!--
```agda
  private
    module C = Precategory C
    module D = Precategory D
    module R = Bifunctor R
```
--->

Fix a profunctor $R : \cC \to \cD$. Here, we focus on *right* functor
presentations, which are best suited for "limit-like" universal
constructions. Let us think of $\cD$ as the theory we are interested in
studying, and write $\Gamma \vdash h : \Delta$ for $h : \cD(\Gamma,
\Delta)$; of $\cC$ as a category of *formation data* for $R$, and,
fixing $\Gamma : \cD$ and $c : \cC$, of the [[set]] $R(\Gamma, c)$ as
classifying *introduction data* for $F(c)$ in context $\Gamma$.

A **right functor presentation** relative to $R$ consists, firstly, of a
**formation rule** `F₀`{.Agda}, which turns a formation datum $c : \cC$
into actual object $F(c) : \cD$. Using type-theoretic notation, we can
imagine that $c : \cC$ represents the premises of a generic formation
rule
$$
  \frac{c : \cC}{F(c) : \cD}
$$. Additionally, we require an **introduction rule** `intro`{.Agda},
assigning to each $r : R(\Gamma, x)$ a morphism $\iota(r) : \cD(\Gamma,
F(x))$. Using our type-theoretic analogy, the element $r$ collects the
premises of a generic introduction rule
$$
  \frac{r : R(\Gamma, x)}{\Gamma \vdash \iota(r) : F(x)}
$$.
The appearance of $F$ on the right of the turnstile gives *right*
presentations their name.

Since $F(-)$ is a limit-like universal construction, the type theory of
$\cD$ imagines it as a `record`{.Agda}-like type. From this perspective,
we can think of an element $r : R(\Gamma, x)$ as containing the values
for $F(x)$'s *projections* in context $\Gamma$, and of the map $\Gamma
\vdash \iota(r) : F(x)$ as the constructed record value.

```agda
  field
    F₀    : ⌞ C ⌟ → ⌞ D ⌟
    intro : ∀ {Γ y} → ⌞ R · Γ · y ⌟ → D.Hom Γ (F₀ y)
```

We incorporate the *elimination* rules for $F(-)$ by requiring a
**generic introduction datum** `univ`{.Agda}, which associates a
$u(c) : R(F(c), c)$ to each $c : \cC$. By the analogy above, we think of
$u(-)$ as a set of projections applied to a *generic* element of $F(-)$.

```agda
    univ : ∀ {c} → ⌞ R · F₀ c · c ⌟
```

Presenting the elimination rules in terms of a generic introduction
datum is slightly confusing from a type-theoretic perspective, where it
is more familiar to say that a term $\Gamma \vdash p : F(c)$ can be
eliminated to obtain $e(p) : R(\Gamma, c)$. The reason for using a
generic element is that it buys us *naturality*, i.e. stability under
substitution, automatically. This is because we *define* elimination in
terms of substitution, which in this case is the functorial action
$R(-,\id)$.

```agda
  elim : ∀ {Γ x} → D.Hom Γ (F₀ x) → ⌞ R · Γ · x ⌟
  elim h = R.lmap h univ
```

With this in hand, stating the laws becomes easy: the **computation
rule**, `beta`{.Agda}, says that eliminating from an introduction form
recovers the introduction datum; the **uniqueness rule**, `eta`{.Agda},
says that if projecting from $\Gamma \vdash h : F(y)$ recovers some
projections $a : R(\Gamma, y)$, then $\iota(a) = h$.

```agda
  field
    beta : ∀ {Γ y} {h : ⌞ R · Γ · y ⌟} → elim (intro h) ≡ h
    unique
      : ∀ {Γ y} {a : ⌞ R · Γ · y ⌟} {h : D.Hom Γ (F₀ y)}
      → elim h ≡ a → intro a ≡ h
```

A short calculation recovers naturality of `intro`{.Agda} from
functoriality of $R$ and the two laws.

```agda
  abstract
    intro-∘
      : ∀ {Γ Δ z} {f : D.Hom Δ Γ} (h : ⌞ R · Γ · z ⌟)
      → intro (R.lmap f h) ≡ intro h D.∘ f
    intro-∘ {f = f} h = unique $
      elim (intro h D.∘ f)        ≡⟨ R.◀.expand refl ·ₚ _ ⟩
      R.lmap f ⌜ elim (intro h) ⌝ ≡⟨ ap! beta ⟩
      R.lmap f h                  ∎
```

<!--
```agda
private module example {o ℓ} (D : Precategory o ℓ) where
  private module D = Cat D
  open Right-presentation
```
-->

#### An example

To exemplify the notion of right functor presentation, we can turn to
the notion of [[product]]. Fixing a category $\cD$, we can simply take
$\cD \times \cD$ to be the category of *formation data for products*,
since the data needed is exactly a pair of objects of $\cD$. The notion
of *introduction* data for products is captured in the definition of
`product-profunctor`{.Agda}, below, which says precisely that we are
considering records $\Gamma \vdash (f,g) : A \times B$ built from pairs
of $\Gamma \vdash f : A$ and $\Gamma \vdash g : B$.

Note that this definition is independent of whether or not $\cD$
actually *has* all products. We can work hypothetically with the data
required to form pairs even if there are no actual pairs in $\cD$.

```agda
  product-profunctor : Profunctor (D ×ᶜ D) D ℓ
  product-profunctor = make-bifunctor mk where
    open Make-bifunctor

    mk : Make-bifunctor
    mk .F₀   Γ (A , B) = el! (D.Hom Γ A × D.Hom Γ B)
    mk .lmap f g = g .fst D.∘ f , g .snd D.∘ f
    mk .rmap f g = f .fst D.∘ g .fst , f .snd D.∘ g .snd
```

<!--
```agda
    mk .lmap-id    = ext λ h₁ h₂ → D.idr _ ,ₚ D.idr _
    mk .rmap-id    = ext λ h₁ h₂ → D.idl _ ,ₚ D.idl _
    mk .lmap-∘ f g = ext λ h₁ h₂ → D.assoc _ _ _ ,ₚ D.assoc _ _ _
    mk .rmap-∘ f g = ext λ h₁ h₂ → sym (D.assoc _ _ _) ,ₚ sym (D.assoc _ _ _)
    mk .lrmap  f g = ext λ h₁ h₂ → sym (D.assoc _ _ _) ,ₚ sym (D.assoc _ _ _)
```
-->

A right presentation relative to this profunctor gives exactly an
assignment of products in $\cD$; the presented functor is, modulo
currying, the product bifunctor on $\cD$. Showing this amounts to
shuffling around some data:

```agda
  products→presentation
    : (∀ X Y → Product D X Y) → Right-presentation product-profunctor
  products→presentation prods = record where
    open Binary-products D prods

    F₀ (X , Y)    = X ⊗₀ Y
    intro (f , g) = ⟨ f , g ⟩
    univ          = π₁ , π₂
    unique p      = ⟨⟩-unique (ap fst p) (ap snd p)
    beta          = π₁∘⟨⟩ ,ₚ π₂∘⟨⟩

  representation→products
    : Right-presentation product-profunctor → ∀ X Y → Product D X Y
  representation→products rep X Y = record where
    module rep = Right-presentation rep

    apex = rep.F₀ (X , Y)
    π₁   = rep.univ .fst
    π₂   = rep.univ .snd
    has-is-product = record where
      ⟨_,_⟩  f g = rep.intro (f , g)
      π₁∘⟨⟩      = ap fst rep.beta
      π₂∘⟨⟩      = ap snd rep.beta
      unique p q = rep.unique (p ,ₚ q)
```

<!--
```agda
module _ {R : Profunctor C D ℓ'} (p : Right-presentation R) where
  private
    module R = Bifunctor R
    module C = Precategory C
    module D = Cat D
    open module p = Right-presentation p

  open Functor
```
-->

## Presented functors

With a motivating example out of the way, we can turn to calculating the
functor presented by a right functor presentation. The object mapping is
given by the introduction rule; the functorial action is obtained by
subjecting the universal introduction datum to a "substitution" in the
category of formation data, and introducing a map from this.
Functoriality follows from straightforward, though lengthy,
computations.

```agda
  presentation→functor : Functor C D
  presentation→functor .F₀   = p.F₀
  presentation→functor .F₁ f = intro (R.rmap f univ)
  presentation→functor .F-id = unique $
    R.lmap D.id univ ≡⟨ R.◀.elim refl  ·ₚ _ ⟩
    univ             ≡⟨ R.▶.intro refl ·ₚ _ ⟩
    R.rmap C.id univ ∎
  presentation→functor .F-∘ f g = sym $
    intro (R.rmap f univ) D.∘ intro (R.rmap g univ)          ≡˘⟨ p.intro-∘ _ ⟩
    intro (R.lmap (intro (R.rmap g univ)) (R.rmap f univ))   ≡⟨ ap intro (R.lrmap _ _ ·ₚ _) ⟩
    intro (R.rmap f ⌜ R.lmap (intro (R.rmap g univ)) univ ⌝) ≡⟨ ap! beta ⟩
    intro (R.rmap f (R.rmap g univ))                         ≡⟨ ap intro (R.▶.collapse refl ·ₚ univ) ⟩
    intro (R.rmap (f C.∘ g) univ)                            ∎
```

We can then show that this is a representation of $R$ by showing that
the isomorphism furnished by `intro`{.Agda} and `elim`{.Agda} is
suitably natural; note that one direction of naturality is simply
`intro-∘`{.Agda}, shown above.

```agda
  presentation→representation : Representation R
  presentation→representation .fst = presentation→functor
  presentation→representation .snd =
    let
      module S = Cat (Sets ℓ')

      im : ∀ x y → R · x · y S.≅ Hom[-,-] D · x · p.F₀ y
      im x y = S.make-iso intro p.elim
        (ext λ h → p.unique refl)
        (ext λ h → beta)

      nat
        : ∀ {x y z} {f : C.Hom x y} (h : ⌞ R · z · x ⌟)
        → intro (R.rmap f univ) D.∘ intro h ≡ intro (R.rmap f h)
      nat {f = f} h =
        intro (R.rmap f univ) D.∘ intro h          ≡˘⟨ intro-∘ _ ⟩
        intro ⌜ R.lmap (intro h) (R.rmap f univ) ⌝ ≡⟨ ap! (R.lrmap _ _ ·ₚ _) ⟩
        intro (R.rmap f ⌜ R.lmap (intro h) univ ⌝) ≡⟨ ap! beta ⟩
        intro (R.rmap f h)                         ∎
    in biiso→isoⁿ im (λ f → sym (ext p.intro-∘)) (λ f → ext nat)
```
