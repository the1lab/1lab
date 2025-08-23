<!--
```agda
open import Cat.Displayed.Diagram.Total.Exponential
open import Cat.Displayed.Diagram.Total.Terminal
open import Cat.Displayed.Diagram.Total.Product
open import Cat.Displayed.Instances.Pullback
open import Cat.Displayed.Instances.Slice
open import Cat.Diagram.Exponential
open import Cat.Instances.Product
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Instances.Slice
open import Cat.Displayed.Base
open import Cat.Cartesian
open import Cat.Prelude

import Cat.Functor.Bifunctor as Bifunctor
import Cat.Functor.Reasoning as Fr
import Cat.Reasoning

open Cartesian-closed
open is-exponential
open Exponential
open is-product
open Terminal
open Product
```
-->

```agda
module Cat.Displayed.Instances.Gluing
  {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'} {F : Functor D C}
  (ccart : Cartesian-category C)
  (dcart : Cartesian-category D)
  (pres  : Cartesian-functor F dcart ccart)
  where
```

# Artin gluing

<!--
```agda
private
  module F  = Fr F
  module C  = Cartesian-category ccart
  module D  = Cartesian-category dcart

open Cartesian-functor pres renaming (module preserved to is)
open /-Obj public

open Displayed
```
-->

:::{.definition #artin-gluing}
Let $\cC$ and $\cD$ be [[Cartesian categories]], and $F : \cD \to \cC$
be a [[Cartesian functor]] between them. The **(Artin) gluing** along
$F$ is the [[pullback|pullback fibration]] of $\cC$'s [[fundamental
fibration]] along $F$, i.e. the left display map in the diagram

~~~{.quiver .attach-above}
\[\begin{tikzcd}[ampersand replacement=\&]
  {\Gl(F)} \&\& {\underline{\cC}} \\
  \\
  \cD \&\& {\cC\text{.}}
  \arrow[dashed, from=1-1, to=1-3]
  \arrow[lies over, from=1-1, to=3-1]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
  \arrow[lies over, from=1-3, to=3-3]
  \arrow["F"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~
:::

We write out the definition of gluing in components to get slightly
better definitional behaviour. Note that, in some cases of interest,
$\cC$ will not have pullbacks, meaning that neither $\underline{\cC}$ or
$\thecat{Gl}(F)$ will be [[Cartesian fibrations]].

```agda
Gl : Displayed D (o ⊔ ℓ) ℓ
Gl = Change-of-base F (Slices C)
```

<!--
```agda
module Gl = Displayed Gl

open is-terminal-over
open TerminalP
```
-->

To be explicit, an object of $\Gl(F)$ over $X \colon \cD$ is a pair
$(X', f)$ of an object $X' \colon \cC$ and a morphism $f : X' \to F(X)$.
A map $(X', f) \to (Y', g)$ over $h : X \to Y$ is a map $h' : X' \to Y'$
such that the square

~~~{.quiver .attach-around}
\[\begin{tikzcd}[ampersand replacement=\&]
  {X'} \&\& {Y'} \\
  \\
  {F(X)} \&\& {F(Y)}
  \arrow["{h'}", from=1-1, to=1-3]
  \arrow["f"', from=1-1, to=3-1]
  \arrow["g", from=1-3, to=3-3]
  \arrow["{F(h)}"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

commutes.

## Displayed Cartesian structure

We will now show that $\Gl(F)$ is a family of Cartesian categories
*over* $\cD$. In particular, it has a [[total terminal object]] as soon
as $F$ preserves the terminal object, and [[total products]] as soon as
$F$ preserves products. The structure is "componentwise," in that the
domain of (e.g.) the total terminal object is the terminal object in
$\cC$, while the morphisms are induced by $F$'s comparison maps.

```agda
Gl-terminal : TerminalP Gl D.terminal
Gl-terminal .top'      = cut {dom = C.top} (pres-terminal _ .centre)
Gl-terminal .has⊤' .!' = record
  { map = C.!
  ; com = is-contr→is-prop (pres-terminal _) _ _
  }
Gl-terminal .has⊤' .!-unique' h = Slice-pathp (C.!-unique _)
```

<!--
```agda
open is-product-over
open ProductP
```
-->

The case for products is similar: the domain of $(A', f) \times' (B',
g)$ is $A' \times B'$, and the map into $F(A \times B)$ is induced by
the preserved product structure on $F$.

```agda
Gl-products : has-products-over Gl D.products
Gl-products {x} {y} a b = done module Gl-products where
  apx : Gl ʻ (x D.⊗₀ y)
  apx .dom = a .dom C.⊗₀ b .dom
  apx .map = is.⟨ a .map C.∘ C.π₁ , b .map C.∘ C.π₂ ⟩

  done : ProductP Gl _ a b
  done .apex' = apx
  done .π₁' = record { com = sym is.π₁∘⟨⟩ }
  done .π₂' = record { com = sym is.π₂∘⟨⟩ }
  done .has-is-product' .⟨_,_⟩'  {f = f} {a' = a'} {g = g} f' g' =
    record { com = coh }
    where abstract
    coh : apx .map C.∘ C.⟨ f' .map , g' .map ⟩ ≡ F.₁ (D.⟨ f , g ⟩) C.∘ a' .map
    coh = C.pullr (C.⟨⟩∘ _) ∙ sym (is.unique
      (F.pulll D.π₁∘⟨⟩ ∙ sym (f' .com) ∙ sym (C.pullr C.π₁∘⟨⟩))
      (F.pulll D.π₂∘⟨⟩ ∙ sym (g' .com) ∙ sym (C.pullr C.π₂∘⟨⟩)))

  done .has-is-product' .π₁∘⟨⟩' = Slice-pathp C.π₁∘⟨⟩
  done .has-is-product' .π₂∘⟨⟩' = Slice-pathp C.π₂∘⟨⟩
  done .has-is-product' .unique' p q = Slice-pathp $ C.⟨⟩-unique
    (λ i → p i .map)
    (λ i → q i .map)
```

<!--
```agda
open Gl-products renaming (apx to _×Gl_) using () public
open Cartesian-over

Gl-cartesian : Cartesian-over Gl dcart
Gl-cartesian .terminal' = Gl-terminal
Gl-cartesian .products' = Gl-products
```
-->

## Cartesian closed structure

::: source
The construction in this section is adapted to the displayed setting
from that given by Johnstone [-@Elephant, A2.1.12].
:::

Now suppose that each of $\cC$ and $\cD$ are [[Cartesian closed]], and
that $\cC$ additionally admits [[pullbacks]]. With no further
assumptions on $F$, the Artin gluing $\Gl(F)$ is made into a Cartesian
closed category over $\cD$, in that it has [[total exponential
objects]].

```agda
Gl-closed
  : Cartesian-closed C ccart
  → (dcl : Cartesian-closed D dcart)
  → has-pullbacks C
  → Cartesian-closed-over Gl Gl-cartesian dcl
Gl-closed ccl dcl pullbacks {A} {B} A' B' = done where
```

<!--
```agda
  module Cλ = Cartesian-closed ccl
  module Dλ = Cartesian-closed dcl

  open is-exponential-over
  open ExponentialP

  open /-Obj A' renaming (dom to X ; map to f)
  open /-Obj B' renaming (dom to Y ; map to g)
```
-->

To explain the construction of the exponential $g^f$, for $f : X \to F(A)$
and $g : Y \to F(B)$,[^shorthand] let us
pretend that $\cD$ is the *syntactic category* of some theory with
function types, $\cC$ is a category of *semantic objects*, and the
functor $F$ embeds syntactic objects into semantic ones. In this
situation, we think of the maps in each object of $\Gl(F)$ as mapping
semantic things to witnesses for their *definability* in terms of
$\cD$'s syntax. In general, the semantic exponential $Y^X$ will contain
many "exotic" operations which can not be syntactically defined, for
example those defined by adversarial knowledge of the internal
structures of $X$ and $Y$, so we have no hope of writing a map $Y^X \to
F(B^A)$.

[^shorthand]:
    In this section, for notational convenience, we will refer to the
    objects of $\Gl(F)$ metonymically by their maps.

Instead, we observe that the commutativity condition for morphisms in
$\Gl(F)$ described above can be *internalised* using a pullback in $\cD$:
we want to restrict the exponential $Y^X$ to those maps which fit into
a commutative square with a map from $F(B^A)$.
To that end, we define the map $\psi : F(B^A) \to F(B)^X$ as the
exponential transpose of
$$
F(B^A) \times X
  \xto{{\id} \times f}       F(B^A) \times F(A)
  \to                        F(B^A \times A)
  \xto{F(\operatorname{ev})} F(B)
$$
where the middle map is the inverse of $F$'s [[product comparison map]].
We therefore think of it as turning *syntactic* functions to ones which
take a *semantic* argument, by passing to the "definability witnesses"
of the domain.

```agda
  ψ : C.Hom (F.₀ Dλ.[ A , B ]) Cλ.[ X , F.₀ B ]
  ψ = Cλ.ƛ (F.₁ Dλ.ev C.∘ comparison.inv C.∘ (C.id C.⊗₁ f))
```

The map $\phi : Y^X \to F(B)^X$ is much more simply defined as the
functorial action of $(-)^X$ on $g : Y \to F(B)$. It therefore takes
*semantic* functions to ones producing a *syntactic* result, by passing
to the "definability witnesses" of each result. The pullback

~~~{.quiver .attach-around}
\[\begin{tikzcd}[ampersand replacement=\&]
  {F(B^A)\mathbin{\times_{F(B)^X}}Y^X} \&\& {Y^X} \\
  \\
  {F(B^A)} \&\& {F(B)^X}
  \arrow[dashed, "{p_2}", from=1-1, to=1-3]
  \arrow[dashed, "{g^f}"', from=1-1, to=3-1]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
  \arrow["\phi", from=1-3, to=3-3]
  \arrow["\psi"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

can thus be thought of as consisting of semantic functions $f : Y^X$
paired with syntactic terms $\sf{f} : F(B^A)$ which "pointwise"
witnesses their definability, in the sense that if $\sf{x} : F(A)$
witnesses the definability of some $x : X$, then the syntactic
application $\sf{f}\, \sf{x} : F(B)$ is a definability witness of $f\, x
: Y$. As indicated in the diagram, the projection onto $F(B^A)$ is
precisely the exponential in $\Gl(F)$.

<!--
```agda
  φ : C.Hom Cλ.[ X , Y ] Cλ.[ X , F.₀ B ]
  φ = Cλ.ƛ (g C.∘ Cλ.ev)
```
-->

```agda
  module pb = Pullback (pullbacks ψ φ)

  pow : Gl ʻ Dλ.[ A , B ]
  pow .dom = pb.apex
  pow .map = pb.p₁
```

The evaluation map $g^f \times f \to g$, lying over $\cD$'s evaluation
map, is defined in terms of the projection $p_2$ onto $Y^X$ and $\cC$'s
evaluation map, explicitly as the composition
$$
\left(F(B^A)\mathbin{\times_{F(B)^X}}Y^X\right) \times X
  \xto{p_2 \times {\id}} Y^X \times X
  \xto{\rm{ev}} Y
$$.

```agda
  evm : Gl.Hom[ Dλ.ev ] (pow ×Gl A') B'
  evm .map = Cλ.ev C.∘ pb.p₂ C.⊗₁ C.id
```

<details>
<summary>We must also calculate that this evaluation map is actually
displayed over $\rm{ev}_\cD$.

Finally, if we have some other $h : Z \to F(C)$, the exponential
transpose of a map $m' : h \times f \to g$ over $m : C \times A \to B$
has semantic component $(\lambda\, m') : Z \to Y^X$, and syntactic
component the composition
$$
Z \xto{h} F(C) \xto{F(\lambda\, m)} F(B^A)\text{,}
$$
which is forced on us by the definition of maps in $\Gl(F)$. We omit the
verification that this satisfies the pullback condition, and that it is
indeed an exponential transpose.
</summary>

```agda
  evm .com = Equiv.injective (_ , Cλ.lambda-is-equiv) $
    Cλ.ƛ (g C.∘ Cλ.ev C.∘ (pb.p₂ C.⊗₁ C.id))
      ≡⟨ ap Cλ.ƛ (C.pulll refl) ⟩
    Cλ.ƛ ((g C.∘ Cλ.ev) C.∘ (pb.p₂ C.⊗₁ C.id))
      ≡⟨ Cλ.ƛ-∘' _ _ _ ⟩
    Cλ.ƛ (Cλ.ev C.∘ (C.id C.⊗₁ C.id)) C.∘ Cλ.ƛ (g C.∘ Cλ.ev) C.∘ pb.p₂
      ≡⟨ C.eliml (ap Cλ.ƛ (C.elimr (C.×-functor .Functor.F-id)) ∙ Cλ.lambda-ev) ⟩
    Cλ.ƛ (g C.∘ Cλ.ev) C.∘ pb.p₂
      ≡⟨ sym pb.square ⟩
    Cλ.ƛ (F.₁ Dλ.ev C.∘ comparison.inv C.∘ (C.id C.⊗₁ f)) C.∘ pb.p₁
      ≡˘⟨ Cλ.ƛ-∘-idr _ _ ⟩
    Cλ.ƛ ((F.₁ Dλ.ev C.∘ comparison.inv C.∘ (C.id C.⊗₁ f)) C.∘ (pb.p₁ C.⊗₁ C.id))
      ≡⟨ ap Cλ.ƛ (C.pullr (C.pullr (Fr.collapse C.×-functor (C.idl _ ,ₚ C.idr _)))) ⟩
    Cλ.ƛ (F.₁ Dλ.ev C.∘ comparison.inv C.∘ (pb.p₁ C.⊗₁ f))
      ∎

  done : ExponentialP Gl Gl-cartesian _ A' B'
  done .B^A' = pow
  done .ev'  = evm
  done .has-is-exponential' .ƛ' {Γ' = Γ} {m = mβ} m .map = alpha module alpha where
    abstract
      coh : ψ C.∘ F.₁ (Dλ.ƛ mβ) C.∘ Γ .map ≡ φ C.∘ Cλ.ƛ (m .map)
      coh = Equiv.injective₂ (Equiv.inverse (_ , Cλ.lambda-is-equiv))
        (
          Cλ.unlambda (Cλ.ƛ (F.₁ Dλ.ev C.∘ comparison.inv C.∘ (C.id C.⊗₁ f)) C.∘ F.₁ (Dλ.ƛ mβ) C.∘ Γ .map)
            ≡⟨ Cλ.unlambda-∘ _ _ ⟩
          Cλ.unlambda (Cλ.ƛ (F.₁ Dλ.ev C.∘ comparison.inv C.∘ (C.id C.⊗₁ f))) C.∘ ((F.₁ (Dλ.ƛ mβ) C.∘ Γ .map) C.⊗₁ C.id)
            ≡⟨ C.pushl (Cλ.commutes _) ⟩
          F.₁ Dλ.ev C.∘ (comparison.inv C.∘ (C.id C.⊗₁ f)) C.∘ ((F.₁ (Dλ.ƛ mβ) C.∘ Γ .map) C.⊗₁ C.id)
            ≡⟨ ap₂ C._∘_ refl (C.pullr (Fr.weave C.×-functor (C.pulll (C.idl _) ,ₚ C.elimr refl ∙ C.introl F.F-id))) ⟩
          F.₁ Dλ.ev C.∘ comparison.inv C.∘ (F.₁ (Dλ.ƛ mβ) C.⊗₁ F.₁ D.id) C.∘ (Γ .map C.⊗₁ f)
            ≡⟨ ap₂ C._∘_ refl (C.extendl (comparison-nat _ _ _)) ⟩
          F.₁ Dλ.ev C.∘ F.₁ (Dλ.ƛ mβ D.⊗₁ D.id) C.∘ comparison.inv C.∘ (Γ .map C.⊗₁ f)
            ≡⟨ C.pulll (F.collapse (Dλ.commutes _)) ⟩
          F.₁ mβ C.∘ comparison.inv C.∘ (Γ .map C.⊗₁ f)
            ≡˘⟨ m .com ⟩
          g C.∘ m .map ∎)
        (
          Cλ.unlambda (Cλ.ƛ (g C.∘ Cλ.ev) C.∘ Cλ.ƛ (m .map))
            ≡⟨ Cλ.unlambda-∘ _ _ ⟩
          Cλ.unlambda (Cλ.ƛ (g C.∘ Cλ.ev)) C.∘ (Cλ.ƛ (m .map) C.⊗₁ C.id)
            ≡⟨ C.pushl (Cλ.commutes _) ⟩
          g C.∘ Cλ.unlambda (Cλ.ƛ (m .map))
            ≡⟨ ap₂ C._∘_ refl (Cλ.commutes _) ⟩
          g C.∘ m .map ∎)

    alpha = pb.universal {p₁' = F.₁ (Dλ.ƛ mβ) C.∘ Γ .map} {p₂' = Cλ.ƛ (m .map)} coh

  done .has-is-exponential' .ƛ' m .com = pb.p₁∘universal
  done .has-is-exponential' .commutes' m = Slice-pathp comm1 where abstract
    comm1 : (Cλ.ev C.∘ (pb.p₂ C.⊗₁ C.id)) C.∘ (alpha.alpha m C.⊗₁ C.id) ≡ m .map
    comm1 = C.pullr (sym (Bifunctor.first∘first C.×-functor))
          ∙∙ ap (Cλ.ev C.∘_) (ap₂ C._⊗₁_ pb.p₂∘universal refl)
          ∙∙ Cλ.commutes _

  done .has-is-exponential' .unique' {Γ' = Γ} {m = mβ} {m'β} {p} {m' = m} m' q =
    Slice-pathp (pb.unique coh₁ coh₂)
    where

    coh₁ : pb.p₁ C.∘ m' .map ≡ F.₁ (Dλ.ƛ mβ) C.∘ Γ .map
    coh₁ =
      pb.p₁ C.∘ m' .map
        ≡⟨ m' .com ⟩
      F.₁ (m'β) C.∘ Γ .map
        ≡⟨ ap₂ C._∘_ (ap F.₁ (Dλ.unique _ p)) refl ⟩
      F.₁ (Dλ.ƛ mβ) C.∘ Γ .map
        ∎

    coh₂ : pb.p₂ C.∘ m' .map ≡ Cλ.ƛ (m .map)
    coh₂ = Cλ.unique _ $
      Cλ.ev C.∘ (pb.p₂ C.∘ m' .map) C.⊗₁ C.id
        ≡⟨ ap₂ C._∘_ refl (Bifunctor.first∘first C.×-functor) ⟩
      Cλ.ev C.∘ pb.p₂ C.⊗₁ C.id C.∘ m' .map C.⊗₁ C.id
        ≡⟨ C.pulll refl ∙ (λ i → q i .map) ⟩
      m .map
        ∎
```

</details>
