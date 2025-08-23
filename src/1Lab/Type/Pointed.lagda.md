<!--
```agda
open import 1Lab.Path.IdentitySystem
open import 1Lab.Reflection.HLevel
open import 1Lab.HLevel.Closure
open import 1Lab.Path.Reasoning
open import 1Lab.Path.Groupoid
open import 1Lab.Type.Sigma
open import 1Lab.Underlying hiding (Σ-syntax)
open import 1Lab.Univalence
open import 1Lab.Type.Pi
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.Type.Pointed where
```

# Pointed types {defines="pointed pointed-type pointed-map pointed-homotopy"}

A **pointed type** is a type $A$ equipped with a choice of base point $\point{A}$.

```agda
Type∙ : ∀ ℓ → Type (lsuc ℓ)
Type∙ ℓ = Σ (Type ℓ) (λ A → A)
```

<!--
```agda
private variable
  ℓ ℓ' : Level
  A B C D : Type∙ ℓ
```
-->

If we have pointed types $(A, a)$ and $(B, b)$, the most natural notion
of function between them is not simply the type of functions $A \to B$,
but rather those functions $A \to B$ which _preserve the basepoint_,
i.e. the functions $f : A \to B$ equipped with paths $f(a) \is b$.
Those are called **pointed maps**.

```agda
_→∙_ : Type∙ ℓ → Type∙ ℓ' → Type _
(A , a) →∙ (B , b) = Σ[ f ∈ (A → B) ] (f a ≡ b)
```

The type of pointed maps $A \to_* (B, b)$ is always inhabited by the
constant function with value $b$, which we refer to as the **zero map**.
This makes the type $A \to_* B$ *itself* a pointed type; in the code, we
write `Maps∙`{.Agda}. As further examples, the identity is evidently
pointed, and the composition of pointed maps is once again pointed.

```agda
zero∙ : A →∙ B
zero∙ {B = _ , b₀} = record { snd = refl }

id∙ : A →∙ A
id∙ = id , refl

_∘∙_ : (B →∙ C) → (A →∙ B) → A →∙ C
(f , f*) ∘∙ (g , g*) = record
  { fst = f ∘ g
  ; snd = ap f g* ∙ f*
  }
```

<!--
```agda
Maps∙ : Type∙ ℓ → Type∙ ℓ' → Type∙ (ℓ ⊔ ℓ')
Maps∙ A B .fst = A →∙ B
Maps∙ A B .snd = zero∙

infixr 0 _→∙_
infixr 40 _∘∙_
```
-->

The product of pointed types is naturally pointed (at the pairing of the
basepoints), and this definition makes the `fst`{.Agda} and `snd`{.Agda}
projections into pointed maps.

```agda
_×∙_ : Type∙ ℓ → Type∙ ℓ' → Type∙ (ℓ ⊔ ℓ')
(A , a) ×∙ (B , b) = A × B , a , b

infixr 5 _×∙_

fst∙ : A ×∙ B →∙ A
fst∙ = fst , refl

snd∙ : A ×∙ B →∙ B
snd∙ = snd , refl
```

Paths between pointed maps are characterised as **pointed homotopies**.
If we are comparing $(f, \phi)$ and $(g, \gamma)$ as pointed maps $(A,
a_0) \to_* (B, b_0)$, it suffices to give a homotopy $h : f \is g$ and a
`Square`{.Agda} with the boundary below. We note in passing that this is
equivalent to asking for a proof that $\phi \is h(a_0)\cdot \gamma$.

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  {f(a_0)} \&\& {g(a_0)} \\
  \\
  {b_0} \&\& {b_0}
  \arrow["{h(a_0)}", from=1-1, to=1-3]
  \arrow["\phi"', from=1-1, to=3-1]
  \arrow["\gamma", from=1-3, to=3-3]
  \arrow["\refl"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

<!--
```agda
module
  _ {ℓ ℓ'} {A@(_ , a₀) : Type∙ ℓ} {B@(_ , b₀) : Type∙ ℓ'}
    {f∙@(f , φ) g∙@(g , γ) : A →∙ B}
  where
```
-->

```agda
  funext∙ : (h : ∀ x → f x ≡ g x) → Square (h a₀) φ γ refl → f∙ ≡ g∙
  funext∙ h pth i = record
    { fst = funext h i
    ; snd = pth i
    }

  _ : (h : ∀ x → f x ≡ g x) → φ ≡ h a₀ ∙ γ → f∙ ≡ g∙
  _ = λ h α → funext∙ h (flip₁ (∙→square' α))
```

<!--
```agda
∘∙-idl : (f : A →∙ B) → id∙ ∘∙ f ≡ f
∘∙-idl f = funext∙ (λ _ → refl) (∙-idr _)

∘∙-idr : (f : A →∙ B) → f ∘∙ id∙ ≡ f
∘∙-idr f = funext∙ (λ _ → refl) (∙-idl _)

∘∙-assoc : (f : C →∙ D) (g : B →∙ C) (h : A →∙ B)
         → (f ∘∙ g) ∘∙ h ≡ f ∘∙ (g ∘∙ h)
∘∙-assoc (f , f') (g , g') (h , h') = funext∙ (λ _ → refl) $
  ap (f ∘ g) h' ∙ ap f g' ∙ f'   ≡⟨ ∙-assoc _ _ _ ⟩
  (ap (f ∘ g) h' ∙ ap f g') ∙ f' ≡˘⟨ ap-∙ f _ _ ⟩∙⟨refl ⟩
  ap f (ap g h' ∙ g') ∙ f'       ∎
```
-->

## Pointed equivalences {defines="pointed-equivalence"}

Combining our [[univalent|univalence]] understanding of paths in the
universe and our understanding of paths in $\Sigma$ types, it stands to
reason that identifications $(A, a_0) \is (B, b_0)$ in the space of
pointed types are given by equivalences $e : A \simeq B$ which carry
$a_0$ to $b_0$. We call these **pointed equivalences** from $(A, a_0)$
to $(B, b_0)$; and, as expected, we can directly use cubical primitives
to turn a pointed equivalence into a path of pointed types.

```agda
_≃∙_ : Type∙ ℓ → Type∙ ℓ' → Type _
(A , a₀) ≃∙ (B , b₀) = Σ[ e ∈ A ≃ B ] (e · a₀ ≡ b₀)

ua∙ : A ≃∙ B → A ≡ B
ua∙ (e , p) i .fst = ua e i
ua∙ (e , p) i .snd = path→ua-pathp e p i
```

Of course, a pointed equivalence has an underlying pointed map, by
simply swapping the quantifiers. Less directly, the *inverse* of a
pointed equivalence is a pointed equivalence as well.

<!--
```agda
module Equiv∙ {ℓ ℓ'} {A@(_ , a₀) : Type∙ ℓ} {B@(_ , b₀) : Type∙ ℓ'} (e : A ≃∙ B) where
```
-->

```agda
  to∙ : A →∙ B
  to∙ = e .fst .fst , e .snd

  open Equiv (e .fst) hiding (inverse) public

  inverse : B ≃∙ A
  inverse .fst = Equiv.inverse (e .fst)
  inverse .snd = sym (Equiv.adjunctl (e .fst) (e .snd))
```

<!--
```agda
  from∙ : B →∙ A
  from∙ = inverse .fst .fst , inverse .snd

id≃∙ : ∀ {ℓ} {A : Type∙ ℓ} → A ≃∙ A
id≃∙ = id≃ , refl

_∙e∙_ : ∀ {ℓ ℓ₁ ℓ₂} {A : Type∙ ℓ} {B : Type∙ ℓ₁} {C : Type∙ ℓ₂}
      → A ≃∙ B → B ≃∙ C → A ≃∙ C
(f , pt) ∙e∙ (g , pt') = f ∙e g , ap (g .fst) pt ∙ pt'

≃∙⟨⟩-syntax : ∀ {ℓ ℓ₁ ℓ₂} (A : Type∙ ℓ) {B : Type∙ ℓ₁} {C : Type∙ ℓ₂}
            → B ≃∙ C → A ≃∙ B → A ≃∙ C
≃∙⟨⟩-syntax A g f = f ∙e∙ g

_≃∙˘⟨_⟩_ : ∀ {ℓ ℓ₁ ℓ₂} (A : Type∙ ℓ) {B : Type∙ ℓ₁} {C : Type∙ ℓ₂}
        → B ≃∙ A → B ≃∙ C → A ≃∙ C
A ≃∙˘⟨ f ⟩ g = Equiv∙.inverse f ∙e∙ g

_≃∙⟨⟩_ : ∀ {ℓ ℓ₁} (A : Type∙ ℓ) {B : Type∙ ℓ₁} → A ≃∙ B → A ≃∙ B
x ≃∙⟨⟩ x≡y = x≡y

_≃∙∎ : ∀ {ℓ} (A : Type∙ ℓ) → A ≃∙ A
x ≃∙∎ = id≃∙

infixr 30 _∙e∙_

infixr 2 ≃∙⟨⟩-syntax _≃∙⟨⟩_ _≃∙˘⟨_⟩_
infix  3 _≃∙∎
infix 21 _≃∙_

syntax ≃∙⟨⟩-syntax x q p = x ≃∙⟨ p ⟩ q

≃∙-ext
  : {f g : A ≃∙ B} → Equiv∙.to∙ f ≡ Equiv∙.to∙ g → f ≡ g
≃∙-ext p = Σ-pathp (Σ-prop-path! (ap fst p)) (ap snd p)

path→equiv∙ : A ≡ B → A ≃∙ B
path→equiv∙ p .fst = path→equiv (ap fst p)
path→equiv∙ p .snd = from-pathp (ap snd p)

ua∙-id-equiv : ua∙ {A = A} id≃∙ ≡ refl
ua∙-id-equiv {A = A , a₀} i j .fst = ua-id-equiv {A = A} i j
ua∙-id-equiv {A = A , a₀} i j .snd = attach (∂ j ∨ i)
  (λ { (j = i0) → a₀ ; (j = i1) → a₀ ; (i = i1) → a₀ })
  (inS a₀)
```
-->

Moreover, we can prove that pointed equivalences are an [[identity
system]] on the type of pointed types, again by a pretty direct cubical
argument.

```agda
univalence∙-identity-system
  : is-identity-system {A = Type∙ ℓ} _≃∙_ (λ _ → id≃∙)
univalence∙-identity-system .to-path = ua∙
univalence∙-identity-system .to-path-over {a = A , a₀} (e , e*) i = record
  { fst =
    let
      f : ∀ i → A → ua e i
      f i a = path→ua-pathp e refl i
    in f i , is-prop→pathp (λ i → is-equiv-is-prop (f i)) id-equiv (e .snd) i
  ; snd = λ j → path→ua-pathp e (λ k → e* (j ∧ k)) i
  }
```

Note that this immediately lets us obtain a *pointed equivalence
induction* principle.

```agda
Equiv∙J
  : ∀ {ℓ ℓ'} {A : Type∙ ℓ} (P : (B : Type∙ ℓ) → A ≃∙ B → Type ℓ')
  → P A id≃∙
  → ∀ {B} e → P B e
Equiv∙J = IdsJ univalence∙-identity-system
```

## Homogeneity

Coming up with pointed homotopies is tricky when there's a lot of path
algebra involved in showing that the underlying functions are identical,
since we would have to trace the pointedness witness along this
construction. However, there is a simplifying assumption we can impose
on the codomain that makes this much simpler, allowing us to consider
only the underlying functions to begin with.

:::{.definition #homogeneous}
We say that a type $A$ is **homogeneous** if, given two choices of
basepoint $a_0, a_1 : A$, we have that $(A, a_0) = (A, a_1)$ in the type
of pointed types.
:::

```agda
Homogeneous : Type ℓ → Type _
Homogeneous A = ∀ {x y} → Path (Type∙ _) (A , x) (A , y)
```

By univalence, this is equivalent to asking for, given $a_0, a_1$, an
equivalence $e : A \simeq A$ with $e(a_0) = a_1$. This provides us some
example that the notion is not vacuous: for example, if we can decide
equality in $A$, then we can build such an equivalence by case analysis.

Another example is readily given by path spaces, where if we are given
$p, q : x \is y$ then precomposition with $q \cdot p\inv$ is an
auto-equivalence of $x \is y$ which sends $p$ to $q$, thence an
identification between the pointed types $(x \is y, p)$ and $(x \is y,
q)$.

```agda
instance
  Path-homogeneous : ∀ {ℓ} {A : Type ℓ} {x y : A} → Homogeneous (Path A x y)
  Path-homogeneous {x = _} {_} {p} {q} = ua∙ record
    { fst = ∙-pre-equiv (q ∙ sym p)
    ; snd = ∙-cancelr q p
    }
```

If $f, g : A \to_* B$ are pointed maps into a homogeneous type $B$, then
to get an identity $f \is g$ it suffices to identify the underlying
unpointed maps $f, g : A \to B$.

```agda
homogeneous-funext∙
  : ∀ {ℓ ℓ'} {A : Type∙ ℓ} {B : Type∙ ℓ'}
  → ⦃ _ : Homogeneous (B .fst) ⦄
  → ∀ {f g : A →∙ B} (h : ∀ x → f .fst x ≡ g .fst x)
  → f ≡ g
homogeneous-funext∙ {A = A} {B = B , b₀} {f = f∙@(f , f*)} {g∙@(g , g*)} h =
  subst (λ b → PathP (λ i → A →∙ b i) f∙ g∙) fix bad where
    hom : ∀ x → Path (Type∙ _) (B , b₀) (B , x)
    hom x = auto

    fg* = sym f* ∙∙ h (A .snd) ∙∙ g*

    bad : PathP (λ i → A →∙ B , fg* i) f∙ g∙
    bad i .fst x = h x i
    bad i .snd j = ∙∙-filler (sym f*) (h (A .snd)) g* j i

    fix : Square {A = Type∙ _} refl (λ i → B , fg* i) refl refl
    fix i j = hcomp (∂ i ∨ ∂ j) λ where
      k (k = i0) → B , b₀
      k (i = i0) → hom (fg* j) k
      k (i = i1) → hom b₀ k
      k (j = i0) → hom b₀ k
      k (j = i1) → hom b₀ k
```

<!--
```agda
Type∙-path-is-hlevel
  : ∀ {ℓ} {A : Type ℓ} {x y : A} n
  → ⦃ _ : H-Level A (suc n) ⦄ ⦃ _ : H-Level A (suc (suc n)) ⦄
  → is-hlevel (Path (Type∙ ℓ) (A , x) (A , y)) (suc n)
Type∙-path-is-hlevel {A = A} n = Equiv→is-hlevel (suc n)
  (identity-system-gives-path univalence∙-identity-system e⁻¹)
  (hlevel (suc n))
```
-->
