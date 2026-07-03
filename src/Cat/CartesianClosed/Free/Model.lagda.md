<!--
```agda
open import Cat.CartesianClosed.Free.Signature
open import Cat.Displayed.Diagram.Total.Exponential
open import Cat.Displayed.Diagram.Total.Terminal
open import Cat.Displayed.Diagram.Total.Product
open import Cat.Displayed.Instances.Chaotic
open import Cat.CartesianClosed.Functor
open import Cat.Diagram.Exponential
open import Cat.Displayed.Section
open import Cat.Cartesian
open import Cat.Prelude
```
-->

```agda
module
  Cat.CartesianClosed.Free.Model
    {ℓ oc ℓc} (S : λ-Signature ℓ) {C : Precategory oc ℓc}
    (cart : Cartesian-category C) (cc : Cartesian-closed C cart)
  where
```

<!--
```agda
open import Cat.CartesianClosed.Free S

open λ-Signature S renaming (Ob to Node ; Hom to Edge)
open Cartesian-closed-functor
open is-exponential-over
open is-terminal-over
open Cartesian-functor
open is-product-over
open Cartesian-over
open ExponentialP
open TerminalP
open ProductP
open Section
open Functor

private
  module C where
    open Cartesian-category cart public
    open Cartesian-closed cc public
```
-->

# Models of a lambda-signature {defines="model-of-a-lambda-signature compiling-to-categories"}

A **model** of a [[λ-signature]] $\Sigma$ in a [[cartesian closed
category]] $\cC$ is an interpretation of the base types of $\Sigma$ as
objects of $\cC$, together with an interpretation of the operations of
$\Sigma$ as morphisms. The universal property of the [[free cartesian
closed category]] $\Syn_\Sigma$ says that a model is all it takes to
interpret *every* type and *every* term of the simply-typed
$\lambda$-calculus over $\Sigma$ in $\cC$: the model extends to a
functor $\Syn_\Sigma \to \cC$, and this functor preserves all the
cartesian closed structure.

This is the categorical semantics underlying "compiling to categories"
[@Elliott:compiling]: a program written once, in the syntax of the
$\lambda$-calculus — say, the evolution law of a physical system, as a
function between sets — can be re-interpreted along any model, in any
cartesian closed category whatsoever, without changing a single line of
the program.

The induction principle for $\Syn_\Sigma$ is stated in terms of
[[displayed categories]]; to extract the functor, we instantiate it at
the [[chaotic bifibration]] of $\cC$ over $\Syn_\Sigma$, whose sections
are precisely functors $\Syn_\Sigma \to \cC$. The first step is to
observe that the cartesian closed structure of $\cC$ makes the chaotic
bifibration cartesian closed *over* $\Syn_\Sigma$: all the displayed
data is just the corresponding data in $\cC$, since displayed objects
and morphisms of the chaotic bifibration do not depend on the base at
all.

```agda
chaotic-cartesian : Cartesian-over (Chaotic Free-ccc C) Free-cartesian
chaotic-cartesian .terminal' .top' = C.top
chaotic-cartesian .terminal' .has⊤' .!' = C.!
chaotic-cartesian .terminal' .has⊤' .!-unique' = C.!-unique
chaotic-cartesian .products' x' y' .apex' = x' C.⊗₀ y'
chaotic-cartesian .products' x' y' .π₁' = C.π₁
chaotic-cartesian .products' x' y' .π₂' = C.π₂
chaotic-cartesian .products' x' y' .has-is-product' .⟨_,_⟩' = C.⟨_,_⟩
chaotic-cartesian .products' x' y' .has-is-product' .π₁∘⟨⟩' = C.π₁∘⟨⟩
chaotic-cartesian .products' x' y' .has-is-product' .π₂∘⟨⟩' = C.π₂∘⟨⟩
chaotic-cartesian .products' x' y' .has-is-product' .unique' = C.⟨⟩-unique

chaotic-closed
  : Cartesian-closed-over (Chaotic Free-ccc C) chaotic-cartesian Free-closed
chaotic-closed A' B' .B^A' = C.[ A' , B' ]
chaotic-closed A' B' .ev' = C.ev
chaotic-closed A' B' .has-is-exponential' .ƛ' = C.ƛ
chaotic-closed A' B' .has-is-exponential' .commutes' = C.commutes
chaotic-closed A' B' .has-is-exponential' .unique' = C.unique
```

A model is then exactly the data that the induction principle asks for:
objects interpreting the base types, and morphisms interpreting the
operations — the type of the latter being computed by `Ty-elim`{.Agda},
which sends `` `⊤ ``{.Agda} to the terminal object, products to
products, and function types to exponentials.

```agda
module model
    (Vₒ : Node → C.Ob)
    (ops : elim.base-method chaotic-cartesian chaotic-closed Vₒ)
  where

  open elim chaotic-cartesian chaotic-closed Vₒ public

  private
    sect : Section (Chaotic Free-ccc C)
    sect = Free-ccc-elim ops
```

Since a section of the chaotic bifibration assigns objects to objects
and morphisms to morphisms, functorially, it *is* a functor — the
**compilation** of the syntax into $\cC$.

```agda
  compile : Functor Free-ccc C
  compile .F₀ = sect .S₀
  compile .F₁ = sect .S₁
  compile .F-id {x} = sect .S-id {x}
  compile .F-∘ = sect .S-∘
```

Because the eliminator interprets each piece of cartesian closed
*syntax* by the corresponding piece of cartesian closed *structure*,
compilation preserves all of it, definitionally so: the [[product
comparison map|cartesian functor]] is $\langle \pi_1, \pi_2 \rangle$,
which is inverse to the identity.

```agda
  compile-cartesian : Cartesian-functor compile Free-cartesian cart
  compile-cartesian .pres-products a b = C.make-invertible C.id
    (C.idr _ ∙ sym (C.⟨⟩-unique (C.idr _) (C.idr _)))
    (C.idl _ ∙ sym (C.⟨⟩-unique (C.idr _) (C.idr _)))
  compile-cartesian .pres-terminal = C.has⊤
```

Likewise, the [[exponential comparison map|cartesian closed functor]]
computes to $\lambda(\rm{ev} \circ \id)$, which is equal to the
identity by the $\eta$-law for exponentials.

```agda
  compile-closed : Cartesian-closed-functor compile Free-closed cc
  compile-closed .cartesian = compile-cartesian
  compile-closed .pres-exponentials A B = subst C.is-invertible
    (sym (ap C.ƛ (C.idr _) ∙ C.lambda-ev))
    C.id-invertible
```
