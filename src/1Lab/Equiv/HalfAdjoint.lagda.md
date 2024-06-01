---
description: |
  We formalise the theory of _half-adjoint equivalences_, another
  well-behaved alternative to the notion of isomorphism. Then, we use
  half-adjoint equivalences as a stepping stone to show that
  isomorphisms are equivalences.
---
<!--
```agda
open import 1Lab.Reflection.Marker
open import 1Lab.HLevel.Closure
open import 1Lab.Path.Groupoid
open import 1Lab.Type.Sigma
open import 1Lab.Univalence
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.Equiv.HalfAdjoint where
```

# Adjoint equivalences {defines="half-adjoint-equivalence"}

An **adjoint equivalence** is an [isomorphism] $(f, g, \eta,
\varepsilon)$ where the [homotopies] ($\eta$, $\varepsilon$) satisfy the
[triangle identities], thus witnessing $f$ and $g$ as [[adjoint
functors]]. In Homotopy Type Theory, we can use a _half_ adjoint
equivalence - satisfying only _one_ of the triangle identities - as a
[good notion of equivalence].

[isomorphism]: 1Lab.Equiv.html#improving-isomorphisms
[homotopies]: 1Lab.Path.html#π-types
[triangle identities]: https://ncatlab.org/nlab/show/triangle+identities
[good notion of equivalence]: 1Lab.Equiv.html#equivalences

```agda
is-half-adjoint-equiv : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B) → Type _
is-half-adjoint-equiv {A = A} {B = B} f =
  Σ[ g ∈ (B → A) ]
  Σ[ η ∈ ((x : A) → g (f x) ≡ x) ]
  Σ[ ε ∈ ((y : B) → f (g y) ≡ y) ]
  ((x : A) → ap f (η x) ≡ ε (f x))
```

The argument is an adaptation of a standard result of both category
theory and homotopy theory - where we can "improve" an equivalence of
categories into an adjoint equivalence, or a homotopy equivalence into a
strong homotopy equivalence (Vogt's lemma). In HoTT, we show this
synthetically for equivalences between $\infty$-groupoids.

```agda
is-iso→is-half-adjoint-equiv
  : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B}
  → is-iso f → is-half-adjoint-equiv f
is-iso→is-half-adjoint-equiv {A = A} {B} {f} iiso =
  g , η , ε' , λ x → sym (zig x)
  where
    open is-iso iiso renaming (inv to g ; linv to η ; rinv to ε)
```

For $g$ and $\eta$, we can take the values provided by `is-iso`{.Agda}.
However, if we want $(\eta, \varepsilon)$ to satisfy the triangle
identities, we can not in general take $\varepsilon' = \varepsilon$.  We
can, however, alter it like thus:

```agda
    ε' : (y : B) → f (g y) ≡ y
    ε' y = sym (ε (f (g y))) ∙ ap f (η (g y)) ∙ ε y
```

Drawn as a diagram, the path above factors like:

~~~{.quiver}
\[\begin{tikzcd}
  {f(g(y))} && y \\
  {f(g(f(g(y))))} && {f(g(y))}
  \arrow["{\rm{sym}\ (\varepsilon(f(g(y))))}"', from=1-1, to=2-1]
  \arrow["{\ap{f}{(\eta(g(y)))}}"', from=2-1, to=2-3]
  \arrow["{\varepsilon \ y}"', from=2-3, to=1-3]
  \arrow["{\varepsilon'\ y}", dashed, from=1-1, to=1-3]
\end{tikzcd}\]
~~~

There is a great deal of redundancy in this definition, given that
$\varepsilon y$ and $\varepsilon' y$ have the same boundary! The point
is that while the definition of $\varepsilon$ is entirely opaque to us,
$\varepsilon'$ is written in such a way that we can use properties of
paths to make the $\rm{sym}\ (\varepsilon ...)$ and $\varepsilon$
cancel:

```agda
    zig : (x : A) → ε' (f x) ≡ ap f (η x)
    zig x =
      ε' (f x)                                                    ≡⟨⟩
      sym (ε (f (g (f x))))  ∙ ap f ⌜ (η (g (f x))) ⌝ ∙ ε (f x)   ≡⟨ ap (λ e → sym (ε _) ∙ ap f e ∙ ε _) (homotopy-invert η) ⟩
      sym (ε (f (g (f x))))  ∙ ⌜ ap (f ∘ g ∘ f) (η x) ∙ ε (f x) ⌝ ≡˘⟨ ap¡ (homotopy-natural ε _) ⟩
      sym (ε (f (g (f x))))  ∙ ε (f (g (f x)))      ∙ ap f (η x)  ≡⟨ ∙-cancell (ε (f (g (f x)))) (ap f (η x)) ⟩
      ap f (η x)                                                  ∎
```

The notion of `half-adjoint equivalence`{.Agda ident=is-half-adjoint-equiv} is a useful
stepping stone in writing a more comprehensible proof that `isomorphisms
are equivalences`{.Agda ident=Iso→Equiv}. Since this result is
fundamental, the proof we actually use is written with efficiency of
computation in mind - hence, cubically. The proof here is intended to be
more educational.

First, we give an equivalent characterisation of paths in
`fibre`{.Agda}s, which will be used in proving that `half adjoint
equivalences are equivalences`{.Agda ident=is-half-adjoint-equiv→is-equiv}.

```agda
fibre-paths : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B} {y : B}
            → {f1 f2 : fibre f y}
            → (f1 ≡ f2)
            ≃ (Σ[ γ ∈ f1 .fst ≡ f2 .fst ] (ap f γ ∙ f2 .snd ≡ f1 .snd))
```

<details>
<summary>The proof of this is not very enlightening, but it's included
here (rather than being completely invisible) for
completeness:</summary>

```agda
fibre-paths {f = f} {y} {f1} {f2} =
  Path (fibre f y) f1 f2                                                       ≃⟨ Iso→Equiv Σ-path-iso e⁻¹ ⟩
  (Σ[ γ ∈ f1 .fst ≡ f2 .fst ] (subst (λ x₁ → f x₁ ≡ _) γ (f1 .snd) ≡ f2 .snd)) ≃⟨ Σ-ap-snd (λ x → path→equiv (lemma x)) ⟩
  (Σ[ γ ∈ f1 .fst ≡ f2 .fst ] (ap f γ ∙ f2 .snd ≡ f1 .snd))                    ≃∎
  where
    helper : (p' : f (f1 .fst) ≡ y)
           → (subst (λ x → f x ≡ y) refl (f1 .snd) ≡ p')
           ≡ (ap f refl ∙ p' ≡ f1 .snd)
    helper p' =
      subst (λ x → f x ≡ y) refl (f1 .snd) ≡ p' ≡⟨ ap₂ _≡_ (transport-refl _) refl ⟩
      (f1 .snd) ≡ p'                            ≡⟨ Iso→Path (sym , iso sym (λ x → refl) (λ x → refl)) ⟩
      ⌜ p' ⌝ ≡ f1 .snd                          ≡˘⟨ ap¡ (∙-idl _) ⟩
      refl ∙ p' ≡ f1 .snd                       ≡⟨⟩
      ap f refl ∙ p' ≡ f1 .snd                  ∎

    lemma : ∀ {x'} {p'} → (γ : f1 .fst ≡ x')
          → (subst (λ x → f x ≡ _) γ (f1 .snd) ≡ p')
          ≡ (ap f γ ∙ p' ≡ f1 .snd)
    lemma {x'} {p'} p =
      J (λ x' γ → ∀ p' → (subst (λ x → f x ≡ _) γ (f1 .snd) ≡ p')
                       ≡ (ap f γ ∙ p' ≡ f1 .snd))
        helper p p'
```
</details>

Then, given an element $y : B$, we can construct a fibre of of $f$, and,
using the above characterisation of paths, prove that this fibre is a
centre of contraction:

```agda
is-half-adjoint-equiv→is-equiv
  : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B}
  → is-half-adjoint-equiv f → is-equiv f
is-half-adjoint-equiv→is-equiv {A = A} {B} {f} (g , η , ε , zig) .is-eqv y = contr fib contract where
  fib : fibre f y
  fib = g y , ε y
```

The fibre is given by $(g(y), ε(y))$, which we can prove identical to
another $(x, p)$ using a very boring calculation:

```agda
  contract : (fib₂ : fibre f y) → fib ≡ fib₂
  contract (x , p) = (fibre-paths e⁻¹) .fst (x≡gy , path) where
    x≡gy = ap g (sym p) ∙ η x

    path : ap f (ap g (sym p) ∙ η x) ∙ p ≡ ε y
    path =
      ap f (ap g (sym p) ∙ η x) ∙ p                   ≡⟨ ap₂ _∙_ (ap-∙ f (ap g (sym p)) (η x)) refl ∙ sym (∙-assoc _ _ _) ⟩
      ap (λ x → f (g x)) (sym p) ∙ ⌜ ap f (η x) ⌝ ∙ p ≡⟨ ap! (zig _) ⟩ -- by the triangle identity
      ap (f ∘ g) (sym p) ∙ ⌜ ε (f x) ∙ p ⌝            ≡⟨ ap! (homotopy-natural ε p)  ⟩ -- by naturality of ε
```

The calculation of `path`{.Agda} factors as a bunch of boring
adjustments to paths using the groupoid structure of types, and the two
interesting steps above: The triangle identity says that
$\ap(f)(\eta x) = \varepsilon(f x)$, and naturality of
$\varepsilon$ lets us "push it past $p$" to get something we can cancel:

```agda
      ap (f ∘ g) (sym p) ∙ ap (f ∘ g) p ∙ ε y     ≡⟨ ∙-assoc _ _ _ ⟩
      ⌜ ap (f ∘ g) (sym p) ∙ ap (f ∘ g) p ⌝ ∙ ε y ≡˘⟨ ap¡ (ap-∙ (f ∘ g) (sym p) p) ⟩
      ap (f ∘ g) ⌜ sym p ∙ p ⌝ ∙ ε y              ≡⟨ ap! (∙-invr _) ⟩
      ap (f ∘ g) refl ∙ ε y                       ≡⟨⟩
      refl ∙ ε y                                  ≡⟨ ∙-idl (ε y) ⟩
      ε y                                         ∎
```

Putting these together, we get an alternative definition of
`is-iso→is-equiv`{.Agda}:

```agda
is-iso→is-equiv'
  : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B}
  → is-iso f → is-equiv f
is-iso→is-equiv' = is-half-adjoint-equiv→is-equiv ∘ is-iso→is-half-adjoint-equiv
```

<!--
```agda
_ = is-iso→is-equiv
is-equiv→is-half-adjoint-equiv
  : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B}
  → is-equiv f → is-half-adjoint-equiv f
is-equiv→is-half-adjoint-equiv {f = f} eqv =
    equiv→inverse eqv
  , equiv→unit eqv
  , equiv→counit eqv
  , equiv→zig eqv
```
-->
