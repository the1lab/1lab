```
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type

open isContr

module 1Lab.Equiv where
```

# Equivalences

The big idea of homotopy type theory is that isomorphic types can be
identified: the univalence axiom. However, the notion of isomorphism,
is, in a sense, not structured enough to be used in the definition. For
that, we need a coherent definition of _equivalence_, where "being an
equivalence" is [a proposition](agda://1Lab.HLevel#isProp).

```
private
  variable
    ℓ₁ : Level
    A B : Type ℓ₁
```

A _fibre_ of a function `f` at a point `y : B` is the collection of all
elements of `A` that `f` maps to `y`.

```
fibre : (A → B) → B → Type _
fibre f y = Σ λ x → f x ≡ y
```

A function `f` is an equivalence if every one of its fibres is
[contractible](agda://1Lab.HLevel#isContr) - that is, for any element
`y` in the range, there is exactly one element in the domain which `f`
maps to `y`.

```
record isEquiv (f : A → B) : Type (level-of A ⊔ level-of B) where
  no-eta-equality
  field
    isEqv : (y : B) → isContr (fibre f y)

open isEquiv public

_≃_ : {ℓ₁ ℓ₂ : _} → Type ℓ₁ → Type ℓ₂ → Type _
_≃_ A B = Σ (isEquiv {A = A} {B = B})

idEquiv : isEquiv {A = A} (λ x → x)
idEquiv .isEqv y = contr (y , λ i → y) λ { (y' , p) i → p (~ i) , λ j → p (~ i ∨ j) } 
```

For Cubical Agda, the type of equivalences is special, so we have to
make a small wrapper to match the interface Agda expects:

```
{-# BUILTIN EQUIV _≃_ #-}
{-# BUILTIN EQUIVFUN fst #-}

isEqv' : {a b : _} (A : Type a) (B : Type b)
       → (w : A ≃ B) (a : B)
       → (ψ : I)
       → Partial ψ (fibre (w .fst) a)
       → fibre (w .fst) a
isEqv' A B (f , isEquiv) a ψ u0 =
  hcomp (λ i → λ { (ψ = i0) → c .centre
                 ; (ψ = i1) → c .paths (u0 1=1) i
                 })
        (c .centre)
  where c = isEquiv .isEqv a

{-# BUILTIN EQUIVPROOF isEqv' #-}
```

## isEquiv is propositional

A function can be an equivalence in at most one way. This follows from
propositions being closed under dependent products, and `isContr`{.Agda}
being a proposition.

```
isProp-isEquiv : (f : A → B) → isProp (isEquiv f)
isProp-isEquiv f x y i .isEqv p = isProp-isContr (x .isEqv p) (y .isEqv p) i
```

# Isomorphisms from equivalences

For this section, we need a definition of _isomorphism_. This is the
same as ever! An isomorphism is a function that has a two-sided inverse.
We first define what it means for a function to invert another on the
left and on the right:

```
isLeftInverse : (B → A) → (A → B) → Type _
isLeftInverse g f = (x : _) → g (f x) ≡ x

isRightInverse : (B → A) → (A → B) → Type _
isRightInverse g f = (x : _) → f (g x) ≡ x
```

A proof that a function $f$ is an isomorphism consists of a function $g$
in the other direction, together with homotopies exhibiting $g$ as a
left- and right- inverse to $f$.

```
record isIso (f : A → B) : Type (level-of A ⊔ level-of B) where
  no-eta-equality
  constructor iso
  field
    g : B → A
    right-inverse : isRightInverse g f
    left-inverse : isLeftInverse g f

  inverse : isIso g
  g inverse = f
  right-inverse inverse = left-inverse
  left-inverse inverse = right-inverse

Iso : {ℓ₁ ℓ₂ : _} → Type ℓ₁ → Type ℓ₂ → Type _
Iso A B = Σ (isIso {A = A} {B = B})
```

Any function that is an equivalence is an isomorphism:

```
isEquiv→isIso : {f : A → B} → isEquiv f → isIso f
isIso.g (isEquiv→isIso eqv) y =
  eqv .isEqv y .centre .fst
```

We can get an element of `x` from the proof that `f` is an equivalence -
it's the point of `A` mapped to `y`, which we get from centre of
contraction for the fibres of `f` over `y`.

```
isIso.right-inverse (isEquiv→isIso eqv) y =
  eqv .isEqv y .centre .snd
```

Similarly, that one fibre gives us a proof that the function above is a
right inverse to `f`.

```
isIso.left-inverse (isEquiv→isIso {f = f} eqv) x i =
  eqv .isEqv (f x) .paths (x , refl) i .fst
```

The proof that the function is a _left_ inverse comes from the fibres of
`f` over `y` being contractible. Since we have a fibre - namely, `f`
maps `x` to `f x` by `refl`{.Agda} - we can get any other we want!

# Equivalences from isomorphisms

Any isomorphism can be made into a coherent equivalence, by a complex
cubical argument that honestly does not matter all that much. That's why
I put it in a details tag!

```
module _ {f : A → B} (i : isIso f) where
```

<details>
<summary> Honestly, there are no explanations here. </summary>

```
  open isIso i renaming ( g to g
                        ; right-inverse to s
                        ; left-inverse to t)

  private
    module _ (y : B) (x0 x1 : A) (p0 : f x0 ≡ y) (p1 : f x1 ≡ y) where
      fill0 : I → I → A
      fill0 i j = hfill (λ k → λ { (i = i1) → t x0 k
                                 ; (i = i0) → g y })
                        (inS (g (p0 (~ i)))) j

      fill1 : I → I → A
      fill1 i j = hfill (λ k → λ { (i = i1) → t x1 k
                                 ; (i = i0) → g y })
                        (inS (g (p1 (~ i)))) j

      fill2 : I → I → A
      fill2 i j = hfill (λ k → λ { (i = i1) → fill1 k i1
                                 ; (i = i0) → fill0 k i1 })
                        (inS (g y)) j

      p : x0 ≡ x1
      p i = fill2 i i1

      sq : I → I → A
      sq i j = hcomp (λ k → λ { (i = i1) → fill1 j (~ k)
                              ; (i = i0) → fill0 j (~ k)
                              ; (j = i1) → t (fill2 i i1) (~ k)
                              ; (j = i0) → g y })
                     (fill2 i j)

      sq1 : I → I → B
      sq1 i j = hcomp (λ k → λ { (i = i1) → s (p1 (~ j)) k
                               ; (i = i0) → s (p0 (~ j)) k
                               ; (j = i1) → s (f (p i)) k
                               ; (j = i0) → s y k })
                      (f (sq i j))

      lemIso : (x0 , p0) ≡ (x1 , p1)
      lemIso i .fst = p i
      lemIso i .snd = λ j → sq1 i (~ j)
```
</details>

This is the important part: if we have `isIso f`, we can conclude
`isEquiv f`.

```
  isIso→isEquiv : isEquiv f
  isIso→isEquiv .isEqv y .centre .fst = g y
  isIso→isEquiv .isEqv y .centre .snd = s y
  isIso→isEquiv .isEqv y .paths z = lemIso y (g y) (fst z) (s y) (snd z)
```

Applying this to the `Iso`{.Agda} and `_≃_`{.Agda} pairs, we can turn
any isomorphism into a coherent equivalence.

```
Iso→Equiv : {ℓ₁ ℓ₂ : _} {A : Type ℓ₁} {B : Type ℓ₂}
          → Iso A B
          → A ≃ B
Iso→Equiv (f , isIso) = f , isIso→isEquiv isIso
```

A helpful lemma: Any function between contractible types is an equivalence:

```
isContr→isEquiv : {ℓ₁ ℓ₂ : _} {A : Type ℓ₁} {B : Type ℓ₂}
                → isContr A → isContr B → {f : A → B}
                → isEquiv f
isContr→isEquiv cA cB = isIso→isEquiv f-is-iso where
  f-is-iso : isIso _
  isIso.g f-is-iso _ = cA .centre
  isIso.right-inverse f-is-iso _ = isContr→isProp cB _ _
  isIso.left-inverse f-is-iso _ = isContr→isProp cA _ _
```

<!--
```
Σ-PathP-iso : {a b : _} {A : Type a} {B : A → Type b}
           → {x y : Σ B}
           → Iso (Σ[ p ∈ x .fst ≡ y .fst ] (PathP (λ i → B (p i)) (x .snd) (y .snd)))
                 (x ≡ y)
fst Σ-PathP-iso (p , q) i = p i , q i
isIso.g (snd Σ-PathP-iso) p = ap fst p , ap snd p
isIso.right-inverse (snd Σ-PathP-iso) x = refl
isIso.left-inverse (snd Σ-PathP-iso) x = refl

Σ-Path-iso : {a b : _} {A : Type a} {B : A → Type b}
           → {x y : Σ B}
           → Iso (Σ[ p ∈ x .fst ≡ y .fst ] (subst B p (x .snd) ≡ y .snd))
                 (x ≡ y)
Σ-Path-iso {B = B} {x} {y} =
  transport (λ i → Iso (Σ[ p ∈ x .fst ≡ y .fst ] (PathP≡Path (λ j → B (p j)) (x .snd) (y .snd) i))
                       (x ≡ y))
            Σ-PathP-iso
```
-->