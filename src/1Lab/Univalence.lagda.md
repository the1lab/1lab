```
open import 1Lab.Type
open import 1Lab.Path
open import 1Lab.Equiv

module 1Lab.Univalence where
```

# Univalence

The univalence axiom says that equivalent types can be identified. In
cubical type theory, this is implemented computationally using the
`Glue`{.Agda} type former, which - roughly - lets us fill a cube of
types where some of the faces can be an equivalence.

<details>
<summary> First, we need to provide bindings for the Cubical Agda glue
primitives </summary>

```
private
  variable
    ℓ ℓ' : Level

  primitive
    primGlue : (A : Type ℓ) {φ : I}
             → (T : Partial φ (Type ℓ')) → (e : PartialP φ (λ o → T o ≃ A))
             → Type ℓ'

    prim^glue : {A : Type ℓ} {φ : I}
              → {T : Partial φ (Type ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
              → PartialP φ T → A → primGlue A T e

    prim^unglue : {A : Type ℓ} {φ : I}
                → {T : Partial φ (Type ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
                → primGlue A T e → A

open import Agda.Builtin.Cubical.HCompU
```
</details>

Now we can build a friendly interface for them:

```
Glue : (A : Type ℓ) {φ : I}
     → (Te : Partial φ (Σ[ T ∈ Type ℓ' ] (T ≃ A)))
     → Type ℓ'
Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

unglue : {A : Type ℓ} (φ : I) {T : Partial φ (Type ℓ')}
         {e : PartialP φ (λ o → T o ≃ A)} → primGlue A T e → A
unglue φ = prim^unglue {φ = φ}
```

Glue satisfies a _boundary condition_: When `φ = i1`, `Glue B {i1} (A,
e)` evaluates to the type `A`:

```
module _ {A B : Type} {e : A ≃ B} where
  private
    Glue-boundary : Glue B {i1} (λ x → A , e) ≡ A
    Glue-boundary i = A
```

From this computation rule, we can turn any equivalence into a path:

```
ua : {A B : Type ℓ} → A ≃ B → A ≡ B
ua {A = A} {B} eqv i = Glue B λ { (i = i0) → A , eqv
                                ; (i = i1) → B , _ , idEquiv
                                }
```

Why does this definition go through? Because of the boundary condition
for Glue! When `i = i0`, the whole thing evaluates to `A`, meaning that
the left endpoint of the path is correct. The same thing happens with
the right endpoint. And, what's more, the evaluation rules for
`transport`{.Agda} give us the correct computation rule for this path:

```
uaβ : {A B : Type ℓ} (f : A ≃ B) (x : A) → transport (ua f) x ≡ f .fst x
uaβ {A = A} {B} f x i = transp (λ _ → B) i (f .fst x)
```

# The axiom

```
pathToEquiv : {A B : Type ℓ} → A ≡ B → A ≃ B
pathToEquiv {A = A} {B} = J (λ x _ → A ≃ x) (_ , idEquiv)
```

The actual univalence axiom says that the canonical map `A ≡ B`, defined
using `J`, is an equivalence. This map is `pathToEquiv`{.Agda}, defined
right above. In more intuitive terms, it's "casting" the identity
equivalence `A ≃ A` along a proof that `A ≡ B` to get an equivalence `A
≃ B`.


```
univalence : {A B : Type ℓ} → isEquiv (pathToEquiv {A = A} {B})
```

We can now prove the univalence theorem - this map is an isomorphism,
and thus, an equivalence. First, we need a small lemma that says `ua id
≡ refl`. This will be used to show one direction of the inverse.

```
univalence {A = A} {B} = isIso→isEquiv _ iso where
  uaIdEquiv : {A : Type ℓ} → ua (_ , idEquiv {A = A}) ≡ refl
  uaIdEquiv {A = A} i j = Glue A {φ = i ∨ ~ j ∨ j} (λ _ → A , _ , idEquiv)
```

It's easy to show that using `Glue`{.Agda}. There are two interval
variables, this is a path between paths: a square. When `i = i0`, the
glue is stuck[^1], so we get `Glue A (λ _ → A , _ , idEquiv)`. When `i =
i1`, by the argument `φ`, the glue computes away, and we get `refl`,
hence the type.

[^1]: Pardon the pun.

```
  iso : isIso pathToEquiv
  isIso.g iso = ua
```

The inverse to `pathToEquiv`{.Agda} is the `ua`{.Agda} map which turns
equivalences into paths.

```
  isIso.right-inverse iso (f , isEqv) = Σ-Path p (isProp-isEquiv f _ _) where
    p : transport (λ i → A → ua (f , isEqv) i) (λ x → x) ≡ f
    p i x = transp (λ j → B) i (f (transp (λ j → A) i x))
```

We have that `pathToEquiv (ua f) ≡ f` in two parts. Since equivalences
are pairs, we can reduce this to proving that the function is preserved,
and proving that the equivalence proof is preserved. The latter is easy
since equivalence proofs are propositions.

For the former, Agda basically does all the work for us: All we need to
show is that `transport (λ i → B) (f (transport (λ i → A) x))` is equal
to `f`. This we do using `transp`{.Agda}, which, when `i = i1`, behaves
like the identity function.

```
  isIso.left-inverse iso = 
    J (λ _ p → ua (pathToEquiv p) ≡ p)
      (ap ua (JRefl (λ x _ → A ≃ x) (_ , idEquiv)) ∙ uaIdEquiv)
```

To show that `pathToEquiv (ua p) ≡ p`, we do path induction on `p`,
reducing this to showing that `ua (pathToEquiv refl) ≡ refl`. By
`JRefl`{.Agda}, we have that `pathToEquiv refl` is `idEquiv`{.Agda},
which means the `uaIdEquiv`{.Agda} lemma proves what we wanted.