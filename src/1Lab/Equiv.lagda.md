```agda
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type

open isContr

module 1Lab.Equiv where
```

# Equivalences

The big idea of homotopy type theory is that isomorphic types can be
identified: the [univalence axiom]. However, the notion of
`isomorphism`{.Agda ident=isIso}, is, in a sense, not "coherent" enough
to be used in the definition. For that, we need a coherent definition of
_equivalence_, where "being an equivalence" is [a
proposition](agda://1Lab.HLevel#isProp).

[univalence axiom]: 1Lab.Univalence.html

To be more specific, what we need for a notion of equivalence
$\mathrm{isEquiv}(f)$ to be "coherent" is:

- Being an `isomorphism`{.Agda ident=isIso} implies being an
`equivalence`{.Agda ident=isEquiv} ($\mathrm{isIso}(f) \to
\mathrm{isEquiv}(f)$)

- Being an equivalence implies being an isomorphism
($\mathrm{isEquiv}(f) \to \mathrm{isIso}(f)$); Taken together with the
first point we may summarise: "Being an equivalence and being an
isomorphism are logically equivalent."

- Most importantly, being an equivalence _must_ be a proposition.

The notion we adopt is due to Voevodsky: An equivalence is one that has
`contractible`{.Agda ident=isContr} `fibres`{.Agda ident=fibre}. Other
definitions are possible (e.g.: [bi-inverible maps]) --- but
contractible fibres are "privileged" in Cubical Agda because for
[glueing] to work, we need a proof that `equivalences have contractible
fibres`{.Agda ident=isEqv'} anyway.

[bi-inverible maps]: 1Lab.Equiv.Biinv.html
[glueing]: 1Lab.Univalence.html#Glue

```agda
private
  variable
    ℓ₁ ℓ₂ : Level
    A B : Type ℓ₁
```

A _homotopy fibre_, _fibre_ or _preimage_ of a function `f` at a point
`y : B` is the collection of all elements of `A` that `f` maps to `y`.
Since many choices of name are possible, we settle on the one that is
shortest and most aesthetic: `fibre`{.Agda}.

```agda
fibre : (A → B) → B → Type _
fibre f y = Σ λ x → f x ≡ y
```

A function `f` is an equivalence if every one of its fibres is
[contractible](agda://1Lab.HLevel#isContr) - that is, for any element
`y` in the range, there is exactly one element in the domain which `f`
maps to `y`. Using set-theoretic language, `f` is an equivalence if the
preimage of every element of the codomain is a singleton.

```agda
record isEquiv (f : A → B) : Type (level-of A ⊔ level-of B) where
  no-eta-equality
  field
    isEqv : (y : B) → isContr (fibre f y)

open isEquiv public

_≃_ : ∀ {ℓ₁ ℓ₂} → Type ℓ₁ → Type ℓ₂ → Type _
_≃_ A B = Σ (isEquiv {A = A} {B = B})

idEquiv : isEquiv {A = A} (λ x → x)
idEquiv .isEqv y = contr (y , λ i → y) λ { (y' , p) i → p (~ i) , λ j → p (~ i ∨ j) } 
```

<!--
```
-- This helper is for functions f, g that cancel eachother, up to
-- definitional equality, without any case analysis on the argument:

strict-fibres : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} (g : B → A) (b : B)
  → Σ[ t ∈ fibre f (f (g b)) ]
    ((t' : fibre f b) → Path (fibre f (f (g b))) t
                          (g (f (t' .fst)) , ap (f ∘ g) (t' .snd)))
strict-fibres {f = f} g b .fst = (g b , refl)
strict-fibres {f = f} g b .snd (a , p) i = (g (p (~ i)) , λ j → f (g (p (~ i ∨ j))))

-- This is more efficient than using Iso→Equiv. When f (g x) is definitionally x,
-- the type reduces to essentially isContr (fibre f b).
```
-->

For Cubical Agda, the type of equivalences is distinguished, so we have
to make a small wrapper to match the interface Agda expects. This is the
[geometric definition of contractibility], in terms of [partial
elements].

[geometric definition of contractibility]: 1Lab.Path.Partial.html#contractibility
[partial elements]: 1Lab.Path.Partial.html

```agda
{-# BUILTIN EQUIV _≃_ #-}
{-# BUILTIN EQUIVFUN fst #-}

isEqv' : ∀ {a b} (A : Type a) (B : Type b)
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

<!--
```
equiv-centre : (e : A ≃ B) (y : B) → fibre (e .fst) y
equiv-centre e y = e .snd .isEqv y .centre

equiv-path : (e : A ≃ B) (y : B) →
  (v : fibre (e .fst) y) → Path _ (equiv-centre e y) v
equiv-path e y = e .snd .isEqv y .paths
```
-->

## isEquiv is propositional

A function can be an equivalence in at most one way. This follows from
propositions being closed under dependent products, and `isContr`{.Agda}
being a proposition.

```agda
isProp-isEquiv : (f : A → B) → isProp (isEquiv f)
isProp-isEquiv f x y i .isEqv p = isProp-isContr (x .isEqv p) (y .isEqv p) i
```

# Isomorphisms from equivalences

For this section, we need a definition of _isomorphism_. This is the
same as ever! An isomorphism is a function that has a two-sided inverse.
We first define what it means for a function to invert another on the
left and on the right:

```agda
isLeftInverse : (B → A) → (A → B) → Type _
isLeftInverse g f = (x : _) → g (f x) ≡ x

isRightInverse : (B → A) → (A → B) → Type _
isRightInverse g f = (x : _) → f (g x) ≡ x
```

A proof that a function $f$ is an isomorphism consists of a function $g$
in the other direction, together with homotopies exhibiting $g$ as a
left- and right- inverse to $f$.

```agda
record isIso (f : A → B) : Type (level-of A ⊔ level-of B) where
  no-eta-equality
  constructor iso
  field
    inv : B → A
    rinv : isRightInverse inv f
    linv : isLeftInverse inv f

  inverse : isIso inv
  inv inverse = f
  rinv inverse = linv
  linv inverse = rinv

Iso : ∀ {ℓ₁ ℓ₂} → Type ℓ₁ → Type ℓ₂ → Type _
Iso A B = Σ (isIso {A = A} {B = B})
```

Any function that is an equivalence is an isomorphism:

```agda
equiv→inverse : {f : A → B} → isEquiv f → B → A
equiv→inverse eqv y = eqv .isEqv y .centre .fst

equiv→section : {f : A → B} (eqv : isEquiv f) → isRightInverse (equiv→inverse eqv) f
equiv→section eqv y = eqv .isEqv y .centre .snd

equiv→retraction : {f : A → B} (eqv : isEquiv f) → isLeftInverse (equiv→inverse eqv) f
equiv→retraction {f = f} eqv x i = eqv .isEqv (f x) .paths (x , refl) i .fst

isEquiv→isIso : {f : A → B} → isEquiv f → isIso f
isIso.inv (isEquiv→isIso eqv) = equiv→inverse eqv
```

We can get an element of `x` from the proof that `f` is an equivalence -
it's the point of `A` mapped to `y`, which we get from centre of
contraction for the fibres of `f` over `y`.

```agda
isIso.rinv (isEquiv→isIso eqv) y =
  eqv .isEqv y .centre .snd
```

Similarly, that one fibre gives us a proof that the function above is a
right inverse to `f`.

```agda
isIso.linv (isEquiv→isIso {f = f} eqv) x i =
  eqv .isEqv (f x) .paths (x , refl) i .fst
```

The proof that the function is a _left_ inverse comes from the fibres of
`f` over `y` being contractible. Since we have a fibre - namely, `f`
maps `x` to `f x` by `refl`{.Agda} - we can get any other we want!

# Equivalences from isomorphisms

Any isomorphism can be made into a coherent equivalence. The proof here
is _efficient_, at the cost of being done with an impenetrable cubical
argument. To understand the details of the construction, there is an
[alternative proof] that factors through [half-adjoint equivalences].

[alternative proof]: 1Lab.Equiv.HalfAdjoint.html#isIso→isEquiv'
[half-adjoint equivalences]: 1Lab.Equiv.HalfAdjoint.html#adjoint-equivalences

```agda
module _ {f : A → B} (i : isIso f) where
```

<details> <summary>The details of this proof are hidden in a `<details>`
tag so you can collapse them away. Click on the black triangle to expand
it, if you want to. </summary>

```agda
  open isIso i renaming ( inv to g
                        ; rinv to s
                        ; linv to t
                        )

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

```agda
  isIso→isEquiv : isEquiv f
  isIso→isEquiv .isEqv y .centre .fst = g y
  isIso→isEquiv .isEqv y .centre .snd = s y
  isIso→isEquiv .isEqv y .paths z = lemIso y (g y) (fst z) (s y) (snd z)
```

Applying this to the `Iso`{.Agda} and `_≃_`{.Agda} pairs, we can turn
any isomorphism into a coherent equivalence.

```agda
Iso→Equiv : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂}
          → Iso A B
          → A ≃ B
Iso→Equiv (f , is-iso) = f , isIso→isEquiv is-iso
```

A helpful lemma: Any function between contractible types is an equivalence:

```agda
isContr→isEquiv : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂}
                → isContr A → isContr B → {f : A → B}
                → isEquiv f
isContr→isEquiv cA cB = isIso→isEquiv f-is-iso where
  f-is-iso : isIso _
  isIso.inv f-is-iso _ = cA .centre
  isIso.rinv f-is-iso _ = isContr→isProp cB _ _
  isIso.linv f-is-iso _ = isContr→isProp cA _ _
```

# Equivalence Reasoning

To make composing equivalences more intuitive, we implement operators to
do equivalence reasoning in the same style as equational reasoning.

```agda
_∙e_ : ∀ {ℓ ℓ₁ ℓ₂} {A : Type ℓ} {B : Type ℓ₁} {C : Type ℓ₂}
     → A ≃ B → B ≃ C → A ≃ C

_e¯¹ : ∀ {ℓ ℓ₁} {A : Type ℓ} {B : Type ℓ₁}
    → A ≃ B → B ≃ A
_e¯¹ eqv = Iso→Equiv ( equiv→inverse (eqv .snd)
                     , record { inv  = eqv .fst
                              ; rinv = equiv→retraction (eqv .snd)
                              ; linv = equiv→section (eqv .snd)
                              })
```
<!--
```
_∙e_ (f , e) (g , e') = (λ x → g (f x)) , eqv where
  g¯¹ : isIso g
  g¯¹ = isEquiv→isIso e'

  f¯¹ : isIso f
  f¯¹ = isEquiv→isIso e

  inv : _ → _
  inv x = f¯¹ .isIso.inv (g¯¹ .isIso.inv x)

  abstract
    right : isRightInverse inv (λ x → g (f x))
    right z =
      g (f (f¯¹ .isIso.inv (g¯¹ .isIso.inv z))) ≡⟨ ap g (f¯¹ .isIso.rinv _) ⟩
      g (g¯¹ .isIso.inv z)                      ≡⟨ g¯¹ .isIso.rinv _ ⟩
      z                                         ∎

    left : isLeftInverse inv (λ x → g (f x))
    left z =
      f¯¹ .isIso.inv (g¯¹ .isIso.inv (g (f z))) ≡⟨ ap (f¯¹ .isIso.inv) (g¯¹ .isIso.linv _) ⟩
      f¯¹ .isIso.inv (f z)                      ≡⟨ f¯¹ .isIso.linv _ ⟩
      z                                         ∎
    eqv : isEquiv (λ x → g (f x))
    eqv = isIso→isEquiv (iso (λ x → f¯¹ .isIso.inv (g¯¹ .isIso.inv x)) right left)

∙-isEquiv : ∀ {ℓ ℓ₁ ℓ₂} {A : Type ℓ} {B : Type ℓ₁} {C : Type ℓ₂}
          → {f : A → B} {g : B → C}
          → isEquiv f
          → isEquiv g
          → isEquiv (λ x → g (f x))
∙-isEquiv {f = f} {g = g} e e' = ((f , e) ∙e (g , e')) .snd
```
-->

The proofs that equivalences are closed under composition assemble
nicely into transitivity operators resembling equational reasoning:

```agda
_≃⟨_⟩_ : ∀ {ℓ ℓ₁ ℓ₂} (A : Type ℓ) {B : Type ℓ₁} {C : Type ℓ₂}
       → A ≃ B → B ≃ C → A ≃ C
A ≃⟨ f ⟩ g = f ∙e g

_≃⟨⟩_ : ∀ {ℓ ℓ₁} (A : Type ℓ) {B : Type ℓ₁} → A ≃ B → A ≃ B
x ≃⟨⟩ x≡y = x≡y

_≃∎ : ∀ {ℓ} (A : Type ℓ) → A ≃ A
x ≃∎ = _ , idEquiv

infixr 30 _∙e_
infixr 2 _≃⟨⟩_ _≃⟨_⟩_
infix  3 _≃∎
```

# Transport is an equivalence

The canonical example of equivalence are those generated by transport
along paths. In a sense, the univalence axiom ensures that these are the
_only_ examples:

```agda
isEquiv-transport : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) → isEquiv (transport p)
isEquiv-transport p = J (λ y p → isEquiv (transport p)) (isIso→isEquiv e) p where
  e : isIso (transport refl)
  isIso.inv e x = x
  isIso.rinv e x = transport-refl _
  isIso.linv e x = transport-refl _
```

# Propositional Extensionality

The following observation is not very complex, but it is incredibly
useful: Equivalence of propositions is the same as biimplication.

```agda
propExt : ∀ {ℓ ℓ'} {P : Type ℓ} {Q : Type ℓ'}
        → isProp P → isProp Q
        → (P → Q) → (Q → P)
        → P ≃ Q
propExt pprop qprop p→q q→p .fst = p→q
propExt pprop qprop p→q q→p .snd .isEqv y .centre = q→p y , qprop _ _
propExt pprop qprop p→q q→p .snd .isEqv y .paths (p' , path) =
  Σ-Path (pprop _ _) (isProp→isSet qprop _ _ _ _)
```
