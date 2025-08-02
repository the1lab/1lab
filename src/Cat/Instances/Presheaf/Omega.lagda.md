<!--
```agda
open import Cat.Diagram.Pullback.Properties
open import Cat.Functor.Adjoint.Continuous
open import Cat.Diagram.Pullback.Along
open import Cat.Functor.Adjoint.Hom
open import Cat.Instances.Functor
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Functor.Adjoint
open import Cat.Instances.Sets
open import Cat.Diagram.Omega
open import Cat.Diagram.Sieve
open import Cat.Prelude

import Cat.Displayed.Instances.Subobjects.Reasoning as Sub
import Cat.Functor.Reasoning.Presheaf as PSh
import Cat.Instances.Presheaf.Limits as Lim
import Cat.Reasoning as Cat

open Subobject-classifier
open is-generic-subobject
open is-pullback-along
open is-pullback
```
-->

```agda
module Cat.Instances.Presheaf.Omega {ℓ} (C : Precategory ℓ ℓ) where
```

# The subobject classifier presheaf {defines="subobject-classifier-presheaf"}

The purpose of this module is to prove that the category $\psh(\cC)$
over a small precategory $\cC$ has a [[subobject classifier]]: the
object $\Omega$ is the presheaf of [[sieves]] and the generic subobject
$\top$ sends each $U : \cC$ to the maximal sieve on $U$.

<!--
```agda
open Lim ℓ C
open Sub PSh-pullbacks
open Functor
open Cat C
open _=>_
```
-->

```agda
tru : ⊤PSh => Sieves
tru .η x _            = maximal'
tru .is-natural x y f = ext λ a {V} f → Ω-ua _ _
```

We must now show that each [[subobject]] $P$ of a presheaf $A$ is
naturally associated to a map $\name{P} : A \to \Omega$, and that $P$ is
the unique pullback of $\operatorname{true}$ along $\name{P}$. Being a
natural transformation of presheaves, we must construct, naturally in $x
: \cC$, a function of sets sending each $e : A(x)$ to a sieve on $x$.

To this end, at a map $h : y \to x$, we produce the [[fibre]]
$P_y^*(A(h)(e))$ of the subobject inclusion $P \mono A$ over the
restriction $A(h)(e) : A(y)$ of $e$ along $h$. The proof that this is
closed under precomposition boils down to applications of functoriality
and naturality, while the proof of naturality for the overall
construction is just functoriality of $P$.

```agda
psh-name : {A : ⌞ PSh ℓ C ⌟} → Subobject A → A => Sieves
psh-name {A} P .η x e .arrows {y} h = elΩ (fibre (P .map .η y) (A ⟪ h ⟫ e))
psh-name {A} P .η x e .closed {f = f} = elim! λ x p g →
  let
    q =
      P .map .η _ (P .domain ⟪ g ⟫ x) ≡⟨ P .map .is-natural _ _ _ $ₚ _ ⟩
      A ⟪ g ⟫ (P .map .η _ x)         ≡⟨ ap₂ (A .F₁) refl p ⟩
      A ⟪ g ⟫ (A ⟪ f ⟫ e)             ≡⟨ PSh.collapse A refl ⟩
      A ⟪ f ∘ g ⟫ e                   ∎
  in inc (_ , q)
psh-name {P} so .is-natural x y f = ext λ x {V} f → Ω-ua
  (□-map λ (e , p) → e , p ∙ PSh.collapse P refl)
  (□-map λ (e , p) → e , p ∙ PSh.expand P refl)
```

<!--
```agda
PSh-omega : Subobject-classifier (PSh ℓ C)
PSh-omega .Subobject-classifier.Ω = Sieves
PSh-omega .Subobject-classifier.true .Sub.domain      = _
PSh-omega .Subobject-classifier.true .Sub.map         = tru
PSh-omega .Subobject-classifier.true .Sub.monic _ _ _ = ext λ _ _ → refl
PSh-omega .generic .name = psh-name
```
-->

We must now show that $P \mono A$ is the pullback of
$\operatorname{true} : \{*\} \mono \Omega$ along $\name{P}$. To start
with, we show that given any $p_1 : P' \to X$ making the outer
(deformed) square in the diagram

~~~{.quiver}
\begin{tikzcd}[ampersand replacement=\&]
  {P'} \\
  \& P \&\& \top \\
  \\
  \& A \&\& \Omega
  \arrow[curve={height=-12pt}, from=1-1, to=2-4]
  \arrow[curve={height=12pt}, from=1-1, to=4-2]
  \arrow[dotted, from=1-1, to=2-2]
  \arrow["{!}", from=2-2, to=2-4]
  \arrow["P"', hook, from=2-2, to=4-2]
  \arrow["{\rm{true}}", from=2-4, to=4-4]
  \arrow["{\name{P}}"', from=4-2, to=4-4]
\end{tikzcd}
~~~

commute, we can turn sections $b : P'(a)$ into points in the fibre of
$P_a$ over $p_1(b)$. This will be used to define the desired "universal"
map $P' \to P$ which appears dotted in the diagram.

```agda
PSh-omega .generic .classifies {A} P = record { has-is-pb = pb } where
  emb : ∀ {x} → is-embedding (P .map .η x)
  emb = is-monic→is-embedding-at (P .monic)

  square→pt
    : ∀ {P'} {p₁' : P' => A} {p₂' : P' => ⊤PSh}
    → psh-name P ∘nt p₁' ≡ tru ∘nt p₂'
    → ∀ {a} (b : P' ʻ a) → fibre (P .map .η a) (p₁' .η a b)
  square→pt {p₁' = p₁'} p {a} b =
    let
      prf : maximal' ≡ psh-name P .η _ (p₁' .η _ b)
      prf = sym (p ηₚ _ $ₚ b)

      memb : Σ[ e ∈ P .domain ʻ a ] P .map .η _ e ≡ (A ⟪ id ⟫ p₁' .η a b)
      memb = □-out (emb _) (subst (id ∈_) prf tt)
    in memb .fst , memb .snd ∙ PSh.F-id A
```

The construction works because commutativity of the diagram means that,
over $b$, the value of the composition $\name{P} \circ p_1'$ is the
maximal presheaf, so it contains the identity morphism, which, following
the type annotation above, means that we have some section $e : P(a)$ sent
by the inclusion $P \mono A$ to $A(\id)(p_1(b))$. And since a
monomorphism of presheaves is, componentwise, an embedding, there can be
at most one such $e$; so we're free to use it as the result of a
function.

<details>
<summary>Some more boring naturality + functoriality computations show
that this assignment is natural; And setting up so that the natural
transformation $P' \to P$ is projecting from a fibre of $P \mono A$
means that, by construction, it satisfies the universal property of a
pullback.</summary>

```agda
  pb : is-pullback (PSh ℓ C) (P .map) (psh-name P) (NT (λ _ _ → _) (λ x y f → refl)) tru
  pb .square = ext λ i x {V} f → to-is-true (inc (_ , P .map .is-natural _ _ _ $ₚ _))

  pb .universal path .η i e = square→pt path e .fst
  pb .universal {P' = P'} {p₁'} p .is-natural x y f = ext λ a → ap fst $
    let
      (pt , q) = square→pt p a
      r =
        P .map .η y (P .domain ⟪ f ⟫ pt) ≡⟨ P .map .is-natural _ _ _ $ₚ _ ⟩
        A ⟪ f ⟫ P .map .η x pt           ≡⟨ ap₂ (A .F₁) refl q ⟩
        A ⟪ f ⟫ (p₁' .η x a)             ≡˘⟨ p₁' .is-natural _ _ _ $ₚ _ ⟩
        p₁' .η y (P' ⟪ f ⟫ a)            ∎
    in emb _ (square→pt p _) (_ , r)

  pb .p₁∘universal {p = p} = ext λ a b → square→pt p b .snd
  pb .p₂∘universal = ext λ _ _ → refl
  pb .unique {p = p} q r = ext λ a b → ap fst $
    emb _ (_ , q ηₚ a $ₚ b) (square→pt p _)
```

</details>

We must now show that $\name{P}$ is the *unique* natural transformation
that can make the square above a pullback. The gist of the proof is to
assume that we have some other pullback diagram (with, say, name
function $n : P \to \Omega$), and to use its universal property to
"replay" the correspondence between fibres of $P \mono A$ and fibres of
the universal natural transformation.

```agda
PSh-omega .generic .unique {A} {m = P} {nm} pb = ext λ i x {U} f →
  let
    emb = is-monic→is-embedding-at (P .monic)
```

First, we start with a fibre of $P \mono A$ over $A(f)(x)$, and turn
this into a proof that $f$ is in the sieve $n(x)$. Because the pullback
diagram commutes, we know that $n(P(a))$ is the maximal sieve; but our
fibre is exactly an element $a$ satisfying $A(f)(x) = P(a)$, so
$n(A(f)(x))$ is also the maximal sieve. By naturality, this is the
pullback of $n(x)$ along $f$; and for a sieve $S$ to contain $f$ is
precisely the statement that $f^*(S)$ is maximal.

```agda
    from : □ (fibre (P .map .η U) (A ⟪ f ⟫ x)) → f ∈ nm .η i x
    from fib =
      let
        (a , prf) = □-out (emb _) fib

        proof =
          maximal'                ≡˘⟨ pb .square ηₚ U $ₚ a ⟩
          nm .η U (P .map .η U a) ≡⟨ ap (nm .η U) prf ⟩
          nm .η U (A ⟪ f ⟫ x)     ≡⟨ nm .is-natural _ _ _ $ₚ _ ⟩
          pullback f (nm .η i x)  ∎
      in subst (_∈ nm .η i x) (idr f) (subst (id ∈_) proof tt)
```

In the other direction, first note that we a natural transformation $f$
(`fold-memb`{.Agda} below) from $n(x)$-qua-presheaf to $A$, and this
transformation makes the diagram

~~~{.quiver}
\begin{tikzcd}[ampersand replacement=\&]
  {n(x)} \&\& \top \\
  \\
  A \&\& \Omega
  \arrow["{!}", from=1-1, to=1-3]
  \arrow["f"', from=1-1, to=3-1]
  \arrow["{\operatorname{true}}", from=1-3, to=3-3]
  \arrow["n"', from=3-1, to=3-3]
\end{tikzcd}
~~~

commute. By the assumed universality of $n : P \to A$, we have a natural
transformation $n(x) \to P$ which composes with the inclusion $P \mono
A$ to give back $f$ --- in particular, it sends arrows $f \in n(x)$ to
fibres of $P \mono A$ over $A(f)(x)$.

```agda
    to : f ∈ nm .η i x → □ (fibre (P .map .η U) (A ⟪ f ⟫ x))
    to wit =
      let
        fold-memb : to-presheaf (nm .η i x) => A
        fold-memb = λ where
          .η i (h , p) → A ⟪ h ⟫ x
          .is-natural x y f → ext λ g e → PSh.expand A refl

        includes : nm ∘nt fold-memb ≡ tru ∘nt Terminal.! PSh-terminal
        includes = ext λ j g hg {U} h →
          nm .η j (A ⟪ g ⟫ x) .arrows h ≡⟨ ap (λ e → e .arrows h) (nm .is-natural _ _ _ $ₚ _) ⟩
          nm .η i x .arrows (g ∘ h)     ≡⟨ to-is-true (nm .η i x .closed hg h) ⟩
          ⊤Ω                            ∎

        members→names : to-presheaf (nm .η i x) => P .domain
        members→names = pb .universal includes

        it = members→names .η U (f , wit)
        prf =
          P .map .η U it ≡⟨ pb .p₁∘universal ηₚ _ $ₚ _ ⟩
          A ⟪ f ⟫ x      ∎
      in inc (it , prf)
  in Ω-ua to from
```
