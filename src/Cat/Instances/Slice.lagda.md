<!--
```agda
open import Cat.Functor.Adjoint.Comonadic
open import Cat.Functor.Adjoint.Comonad
open import Cat.Diagram.Comonad.Writer
open import Cat.Diagram.Limit.Finite
open import Cat.Functor.Conservative
open import Cat.Instances.Coalgebras
open import Cat.Functor.Equivalence
open import Cat.Functor.Naturality
open import Cat.Functor.Properties
open import Cat.Instances.Discrete
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Diagram.Comonad
open import Cat.Diagram.Product
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import Cat.Functor.Base
open import Cat.Cartesian
open import Cat.Prelude

open import Data.Sum

import Cat.Reasoning

open Coalgebra-on
open is-pullback
open ∫Hom
```
-->

```agda
module Cat.Instances.Slice where
```

<!--
```agda
private variable
  o ℓ o' ℓ' : Level
open Functor
open _=>_
open _⊣_

module _ {o ℓ} {C : Precategory o ℓ} where
  private
    module C = Cat.Reasoning C
    variable a b c : C.Ob
```
-->

# Slice categories {defines="slice-category"}

When working in $\Sets$, there is an evident notion of _family indexed
by a set_: a family of sets $(F_i)_{i \in I}$ is equivalently a functor
$[\rm{Disc}(I), \Sets]$, where we have equipped the set $I$ with the
[discrete category] structure. This works essentially because of the
[discrete category-global sections][coh] adjunction, but in general this
can not be applied to other categories, like $\rm{Groups}$. How,
then, should we work with "indexed families" in general categories?

[discrete category]: Cat.Instances.Discrete.html
[coh]: Cat.Instances.StrictCat.Cohesive.html#disc-γ

The answer is to consider, rather than families themselves, the
_projections from their total spaces_ as the primitive objects. A family
indexed by $I$, then, would consist of an object $A$ and a morphism $t :
A \to I$, where $A$ is considered as the "total space" object and $t$
assigns gives the "tag" of each object. By analysing how $t$ [pulls
back] along maps $B \to I$, we recover a notion of "fibres": the
collection with index $i$ can be recovered as the pullback $t^*i$.

[pulls back]: Cat.Diagram.Pullback.html

Note that, since the discussion in the preceding paragraph made no
mention of the category of sets, it applies in any category! More
generally, for any category $\cC$ and object $c : \cC$, we have a
_category of objects indexed by $c$_, the **slice category** $\cC/c$.
An object of "the slice over $c$" is given by an object $d : \cC$ to
serve as the domain, and a map $f : d \to c$.

```agda
  record /-Obj (c : C.Ob) : Type (o ⊔ ℓ) where
    constructor cut
    field
      {dom} : C.Ob
      map   : C.Hom dom c
```

A map between $f : a \to c$ and $g : b \to c$ is given by a map $h : a
\to b$ such that the triangle below commutes. Since we're thinking of
$f$ and $g$ as _families indexed by $c$_, commutativity of the triangle
says that the map $h$ "respects reindexing", or less obliquely
"preserves fibres".

~~~{.quiver}
\[\begin{tikzcd}
  a && b \\
  & c
  \arrow["f"', from=1-1, to=2-2]
  \arrow["g", from=1-3, to=2-2]
  \arrow["h", from=1-1, to=1-3]
\end{tikzcd}\]
~~~

```agda
  record /-Hom (a b : /-Obj c) : Type ℓ where
    no-eta-equality
    private
      module a = /-Obj a
      module b = /-Obj b
    field
      map : C.Hom a.dom b.dom
      com : b.map C.∘ map ≡ a.map
```

<!--
```agda
  /-Obj-path : ∀ {c} {x y : /-Obj c}
             → (p : x ./-Obj.dom ≡ y ./-Obj.dom)
             → PathP (λ i → C.Hom (p i) c) (x ./-Obj.map) (y ./-Obj.map)
             → x ≡ y
  /-Obj-path p q i ./-Obj.dom = p i
  /-Obj-path p q i ./-Obj.map = q i

  /-Hom-pathp : ∀ {c a a' b b'} (p : a ≡ a') (q : b ≡ b')
                {x : /-Hom {c = c} a b} {y : /-Hom a' b'}
              → PathP (λ i → C.Hom (p i ./-Obj.dom) (q i ./-Obj.dom))
                        (x ./-Hom.map) (y ./-Hom.map)
              → PathP (λ i → /-Hom (p i) (q i)) x y
  /-Hom-pathp p q {x} {y} r = path where
    open /-Hom

    path : PathP (λ i → /-Hom (p i) (q i))  x y
    path i .map = r i
    path i .com =
      is-prop→pathp
        (λ i → C.Hom-set (p i ./-Obj.dom) _
                         (q i ./-Obj.map C.∘ r i) (p i ./-Obj.map))
        (x .com) (y .com) i

  /-Hom-path : ∀ {c a b} {x y : /-Hom {c = c} a b}
             → x ./-Hom.map ≡ y ./-Hom.map
             → x ≡ y
  /-Hom-path = /-Hom-pathp refl refl

  instance
    Extensional-/-Hom
      : ∀ {c a b ℓ} ⦃ sa : Extensional (C.Hom (/-Obj.dom a) (/-Obj.dom b)) ℓ ⦄
      → Extensional (/-Hom {c = c} a b) ℓ
    Extensional-/-Hom ⦃ sa ⦄ = injection→extensional! (/-Hom-pathp refl refl) sa

unquoteDecl H-Level-/-Hom = declare-record-hlevel 2 H-Level-/-Hom (quote /-Hom)
```
-->

The slice category $\cC/c$ is given by the `/-Obj`{.Agda} and
`/-Hom`{.Agda}s.

```agda
Slice : (C : Precategory o ℓ) → ⌞ C ⌟ → Precategory _ _
Slice C c = precat where
  import Cat.Reasoning C as C
  open Precategory
  open /-Hom
  open /-Obj

  precat : Precategory _ _
  precat .Ob = /-Obj {C = C} c
  precat .Hom = /-Hom
  precat .Hom-set x y = hlevel 2
  precat .id .map = C.id
  precat .id .com = C.idr _
```

For composition in the slice over $c$, note that if the triangle (the
commutativity condition for $f$) and the rhombus (the commutativity
condition for $g$) both commute, then so does the larger triangle (the
commutativity for $g \circ f$).

~~~{.quiver}
\[\begin{tikzcd}
  x && y && z \\
  & c \\
  && c
  \arrow["{x_m}"', from=1-1, to=2-2]
  \arrow["{y_m}", from=1-3, to=2-2]
  \arrow["f", from=1-1, to=1-3]
  \arrow["g", from=1-3, to=1-5]
  \arrow["{z_m}", from=1-5, to=3-3]
  \arrow[Rightarrow, no head, from=2-2, to=3-3]
\end{tikzcd}\]
~~~

```agda
  precat ._∘_ {x} {y} {z} f g = fog where
    module f = /-Hom f
    module g = /-Hom g
    fog : /-Hom _ _
    fog .map = f.map C.∘ g.map
    fog .com =
      z .map C.∘ f.map C.∘ g.map ≡⟨ C.pulll f.com ⟩
      y .map C.∘ g.map           ≡⟨ g.com ⟩
      x .map                     ∎
  precat .idr f = ext (C.idr _)
  precat .idl f = ext (C.idl _)
  precat .assoc f g h = ext (C.assoc _ _ _)
```

There is an evident projection functor from $\cC/c$ to $\cC$ that only
remembers the domains.

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} {c} where
  open /-Hom
  open /-Obj
  private
    module C = Cat.Reasoning C
    module C/c = Cat.Reasoning (Slice C c)
```
-->

```agda
  Forget/ : Functor (Slice C c) C
  Forget/ .F₀ o = o .dom
  Forget/ .F₁ f = f .map
  Forget/ .F-id = refl
  Forget/ .F-∘ _ _ = refl
```

Furthermore, this forgetful functor is easily seen to be [[faithful]]
and [[conservative]]: if $f$ is a morphism in $\cC/c$ whose underlying
map has an inverse $f^{-1}$ in $\cC$, then $f^{-1}$ clearly also makes
the triangle commute, so that $f$ is invertible in $\cC/c$.

```agda
  Forget/-is-faithful : is-faithful Forget/
  Forget/-is-faithful p = ext p

  Forget/-is-conservative : is-conservative Forget/
  Forget/-is-conservative {f = f} i =
    C/c.make-invertible f⁻¹ (ext i.invl) (ext i.invr)
    where
      module i = C.is-invertible i
      f⁻¹ : /-Hom _ _
      f⁻¹ .map = i.inv
      f⁻¹ .com = C.rswizzle (sym (f .com)) i.invl
```

## Finite limits {defines="finite-limits-in-slices"}

We discuss the construction of _finite_ limits in the slice of $\cC/c$.
First, every slice category has a [[terminal object]], given by the
identity map $\id : c \to c$.

```agda
module _ {o ℓ} {C : Precategory o ℓ} {c : ⌞ C ⌟} where
  import Cat.Reasoning C as C
  import Cat.Reasoning (Slice C c) as C/c
  open /-Hom
  open /-Obj

  Slice-terminal-object' : is-terminal (Slice C c) (cut C.id)
  Slice-terminal-object' obj .centre .map = obj .map
  Slice-terminal-object' obj .centre .com = C.idl _
  Slice-terminal-object' obj .paths other =
    ext (sym (other .com) ∙ C.idl _)

  Slice-terminal-object : Terminal (Slice C c)
  Slice-terminal-object .Terminal.top  = _
  Slice-terminal-object .Terminal.has⊤ = Slice-terminal-object'
```

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} {c : ⌞ C ⌟} where
  import Cat.Reasoning C as C
  import Cat.Reasoning (Slice C c) as C/c
  private variable
    a b : C.Ob
    f g π₁ π₂ : C.Hom a b
  open /-Hom
  open /-Obj
```
-->

:::{.definition #products-in-a-slice}
Products in a slice category are slightly more complicated --- but if
you've ever heard a pullback referred to as a "fibre(d) product", you
already know what we're up to! Indeed, in defining [[pullback]]
diagrams, we noted that the pullback of $f : X \to Z$ and $g : Y \to Z$
is exactly the product $f \times g$ in the slice over $Z$.
:::

Suppose we have a pullback diagram like the one below, i.e., a limit of
the diagram $a \xrightarrow{f} c \xleftarrow{g} b$, in the category
$\cC$. We'll show that it's also a limit of the (discrete) diagram
consisting of $f$ and $g$, but now in the slice category $\cC/c$.

~~~{.quiver}
\[\begin{tikzcd}
  {a \times_c b} && a \\
  \\
  b && c
  \arrow["{\pi_2}"', from=1-1, to=3-1]
  \arrow["{\pi_1}", from=1-1, to=1-3]
  \arrow["f", from=1-3, to=3-3]
  \arrow["g"', from=3-1, to=3-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

For starters, we have to define a map $a \times_c b \to c$, to serve as
the actual object in the slice. It seems like there are _two_ choices,
depending on how you trace out the square. But the square commutes,
which by definition means that we don't really have a choice. We choose
$f\pi_1$, i.e. following the top face then the right face, for
definiteness.

<!--
```agda
  module
    _ {f g : /-Obj c} {Pb : C.Ob} {π₁ : C.Hom Pb (f .dom)}
                                  {π₂ : C.Hom Pb (g .dom)}
      (pb : is-pullback C {X = f .dom} {Z = c} {Y = g .dom} {P = Pb}
        π₁ (map {_} {_} {C} {c} f) π₂ (map {_} {_} {C} {c} g))
    where
    private module pb = is-pullback pb
```
-->

```agda
    is-pullback→product-over : C/c.Ob
    is-pullback→product-over = cut (f .map C.∘ π₁)
```

Let us turn to the projection maps. Again by commutativity of the
square, the pullback projection maps $\pi_1$ and $\pi_2$ extend directly
to maps from $f\pi_1$ into $f$ and $g$ over $c$. In the nontrivial case,
we have to show that $g\pi_2 = f\pi_1$, which is _exactly_ what
commutativity of the square gets us.

```agda
    is-pullback→π₁ : C/c.Hom is-pullback→product-over f
    is-pullback→π₁ .map = π₁
    is-pullback→π₁ .com = refl

    is-pullback→π₂ : C/c.Hom is-pullback→product-over g
    is-pullback→π₂ .map = π₂
    is-pullback→π₂ .com = sym pb.square

    open is-product
```

Now we turn to showing that these projections are universal, in the
slice $\cC/c$. Given a family $Q : Q \to c$, the data of maps $p : p \to
f$ and $q : p \to g$ over $c$ is given precisely by evidence that $fq =
gp$, meaning that they fit neatly around our pullback diagram, as shown
in the square below.

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  Q \\
  \& {a\times_bc} \&\& a \\
  \\
  \& b \&\& c
  \arrow["g"', from=4-2, to=4-4]
  \arrow["f", from=2-4, to=4-4]
  \arrow["q", curve={height=-12pt}, from=1-1, to=2-4]
  \arrow["p"', curve={height=12pt}, from=1-1, to=4-2]
  \arrow["{\pi_1}"{description}, from=2-2, to=2-4]
  \arrow["{\pi_2}"{description}, from=2-2, to=4-2]
  \arrow["{l}"{description}, dashed, from=1-1, to=2-2]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=2-2, to=4-4]
\end{tikzcd}\]
~~~

And, as indicated in the diagram, since this square is a pullback, we
can obtain the dashed map $l : Q \to a \times_c b$, which we can
calculate satisfies

$$
f\pi_1l = fp = Q
$$,

so that it is indeed a map $Q \to f \times g$ over $c$, as required.
Reading out the rest of $(a \times_c b)$'s universal property, we see
that $l$ is the unique map which satisfies $\pi_1l = p$ and $\pi_2l =
q$, exactly as required for the pairing $\langle p, q \rangle$ of a
product in $\cC/c.$

```agda
    is-pullback→is-fibre-product
      : is-product (Slice C c) is-pullback→π₁ is-pullback→π₂
    is-pullback→is-fibre-product .⟨_,_⟩ {Q} p q = factor where
      module p = /-Hom p
      module q = /-Hom q

      factor : C/c.Hom Q _
      factor .map = pb.universal (p.com ∙ sym q.com)
      factor .com =
        (f .map C.∘ π₁) C.∘ pb.universal _ ≡⟨ C.pullr pb.p₁∘universal ⟩
        f .map C.∘ p.map                   ≡⟨ p.com ⟩
        Q .map                             ∎
```

<!--
```agda
    is-pullback→is-fibre-product .π₁∘⟨⟩ = ext pb.p₁∘universal
    is-pullback→is-fibre-product .π₂∘⟨⟩ = ext pb.p₂∘universal
    is-pullback→is-fibre-product .unique p q =
      ext (pb.unique (ap map p) (ap map q))

  Pullback→Fibre-product
    : ∀ {f g : /-Obj c}
    → Pullback C (f .map) (g .map) → Product (Slice C c) f g
  Pullback→Fibre-product pb .Product.apex = _
  Pullback→Fibre-product pb .Product.π₁ = _
  Pullback→Fibre-product pb .Product.π₂ = _
  Pullback→Fibre-product pb .Product.has-is-product =
    is-pullback→is-fibre-product (pb .Pullback.has-is-pb)
```
-->

<!--
```agda
  module _
    {f g : /-Obj c} {p : /-Obj c} {π₁ : C/c.Hom p f} {π₂ : C/c.Hom p g}
    (prod : is-product (Slice C c) π₁ π₂)
    where
    private module prod = is-product prod
```
-->

We can go in the other direction as well, hence products in a slice
category correspond precisely to pullbacks in the base category.

```agda
    open is-pullback

    is-fibre-product→is-pullback : is-pullback C (π₁ .map) (f .map) (π₂ .map) (g .map)
    is-fibre-product→is-pullback .square = π₁ .com ∙ sym (π₂ .com)
    is-fibre-product→is-pullback .universal {P} {p₁} {p₂} square =
      prod.⟨ record { map = p₁ ; com = refl }
           , record { map = p₂ ; com = sym square } ⟩ .map
    is-fibre-product→is-pullback .p₁∘universal = ap map prod.π₁∘⟨⟩
    is-fibre-product→is-pullback .p₂∘universal = ap map prod.π₂∘⟨⟩
    is-fibre-product→is-pullback .unique {lim' = lim'} fac₁ fac₂ = ap map $
      prod.unique
        {other = record
          { map = lim'
          ; com = ap (C._∘ lim') (sym (π₁ .com)) ∙ C.pullr fac₁ }}
        (ext fac₁) (ext fac₂)
```

While products and terminal objects in $\cC/X$ do not correspond to
those in $\cC$, _pullbacks_ (and equalisers) are precisely equivalent. A
square is a pullback in $\cC/X$ _precisely if_ its image in $\cC$,
forgetting the maps to $X$, is a pullback.

The "if" direction (what is `pullback-above→pullback-below`{.Agda}) in
the code is essentially an immediate consequence of the fact that
equality of morphisms in $\cC/X$ may be tested in $\cC$, but we do
have to take some care when extending the "universal" morphism back down
to the slice category (see the calculation marked `{- * -}`{.Agda}).

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} {X : ⌞ C ⌟}
         {P A B c} {p1 f p2 g}
  where
  open Cat.Reasoning C
  open is-pullback
  open /-Obj
  open /-Hom
```
-->

```agda
  pullback-above→pullback-below
    : is-pullback C (p1 .map) (f .map) (p2 .map) (g .map)
    → is-pullback (Slice C X) {P} {A} {B} {c} p1 f p2 g
  pullback-above→pullback-below pb = pb' where
    pb' : is-pullback (Slice _ _) _ _ _ _
    pb' .square           = ext (pb .square)
    pb' .universal p .map = pb .universal (ap map p)
    pb' .universal {P'} {p₁' = p₁'} p .com =
      (c .map ∘ pb .universal (ap map p))           ≡˘⟨ pulll (p1 .com) ⟩
      (P .map ∘ p1 .map ∘ pb .universal (ap map p)) ≡⟨ ap (_ ∘_) (pb .p₁∘universal) ⟩
      (P .map ∘ p₁' .map)                           ≡⟨ p₁' .com ⟩
      P' .map                                       ∎ {- * -}
    pb' .p₁∘universal = ext (pb .p₁∘universal)
    pb' .p₂∘universal = ext (pb .p₂∘universal)
    pb' .unique p q   = ext (pb .unique (ap map p) (ap map q))

  pullback-below→pullback-above
    : is-pullback (Slice C X) {P} {A} {B} {c} p1 f p2 g
    → is-pullback C (p1 .map) (f .map) (p2 .map) (g .map)
  pullback-below→pullback-above pb = pb' where
    pb' : is-pullback _ _ _ _ _
    pb' .square = ap map (pb .square)
    pb' .universal p = pb .universal
      {p₁' = record { com = refl }}
      {p₂' = record { com = sym (pulll (g .com))
                         ∙∙ sym (ap (_ ∘_) p)
                         ∙∙ pulll (f .com) }}
      (ext p) .map
    pb' .p₁∘universal = ap map $ pb .p₁∘universal
    pb' .p₂∘universal = ap map $ pb .p₂∘universal
    pb' .unique p q   = ap map $ pb .unique
      {lim' = record { com = sym (pulll (p1 .com)) ∙ ap (_ ∘_) p }}
      (ext p) (ext q)
```

It follows that any slice of a category with pullbacks is finitely
complete. Note that we could have obtained the products abstractly,
since any category with pullbacks and a terminal object has products,
but expanding on the definition in components helps clarify both their
construction _and_ the role of pullbacks.

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C
  open Pullback
  open /-Obj
  open /-Hom
```
-->

```agda
  Slice-pullbacks : ∀ {b} → has-pullbacks C → has-pullbacks (Slice C b)
  Slice-products  : ∀ {b} → has-pullbacks C → has-products (Slice C b)
  Slice-lex : ∀ {b} → has-pullbacks C → Finitely-complete (Slice C b)
```

<details>
<summary>This is one of the rare moments when the sea of theory has
already risen to meet our prose --- put another way, the proofs of the
statements above are just putting things together. We leave them in this
`<details>` block for the curious reader.
</summary>

```agda
  Slice-pullbacks pullbacks {A = A} f g = pb where
    pb : Pullback (Slice C _) _ _
    pb .apex = cut (A .map ∘ pullbacks _ _ .p₁)
    pb .p₁ = record { com = refl }
    pb .p₂ = record { com =
         sym (pushl (sym (f .com))
      ∙∙ ap₂ _∘_ refl (pullbacks _ _ .square)
      ∙∙ pulll (g .com)) }
    pb .has-is-pb = pullback-above→pullback-below $
      pullbacks (f .map) (g .map) .has-is-pb

  Slice-products pullbacks f g = Pullback→Fibre-product (pullbacks _ _)

  Slice-lex pb = with-pullbacks (Slice C _)
    Slice-terminal-object
    (Slice-pullbacks pb)

  Slice-cartesian : ∀ {b} → has-pullbacks C → Cartesian-category (Slice C b)
  Slice-cartesian pb = record
    { terminal = Slice-terminal-object
    ; products = Slice-products pb
    }
```

</details>

## Slices of Sets

<!--
```agda
module _ {I : Set ℓ} where
  open /-Obj
  open /-Hom
```
-->

Having tackled some properties of slice categories in general, we now
turn to characterising the slice $\cC/x$ as the category of *families of
$\cC$-objects indexed by $x$*, by formalising the aforementioned
equivalence $\Sets/I \cong [I, \Sets]$. Let us trace our route before we
depart, and write down an outline of the proof.

- A functor $F : I \to \Sets$ is sent to the first projection $\pi_1 :
  (\Sigma F) \to I$, functorially. Since $\Sigma F$ is the _total space_
  of $F$, we refer to this as the `Total-space`{.Agda} functor.

- We define a procedure that, given a morphism $\Sigma F \to \Sigma G$
  over $I$, recovers a natural transformation $F \To G$; We then calculate
  that this procedure is an inverse to the action on morphisms of
  `Total-space`{.Agda}, so that it is [[fully faithful]].

- Finally, we show that, given $p : X \to I$, the assignment $i \mapsto
  p\inv(i)$, sending an index to the fibre of $p$ over it, gives a
  functor $P$; and that $\int P \cong p$ over $I$, so that
  `Total-space`{.Agda} is a [[split essential surjection]], hence an
  equivalence of categories.

Let's begin. The `Total-space`{.Agda} functor gets out of our way very
fast:

```agda
  Total-space : Functor Cat[ Disc' I , Sets ℓ ] (Slice (Sets ℓ) I)
  Total-space .F₀ F .dom = el! (Σ _ (∣_∣ ⊙ F₀ F))
  Total-space .F₀ F .map = fst

  Total-space .F₁ nt .map (i , x) = i , nt .η _ x
  Total-space .F₁ nt .com         = refl

  Total-space .F-id    = ext λ _ _ → refl
  Total-space .F-∘ _ _ = ext λ _ _ → refl
```

Since the construction of the functor itself is straightforward, we turn
to showing it is fully faithful. The content of a morphism $h : \Sigma F
\to \Sigma G$ over $I$ is a function

$$
h : (\Sigma F) \to (\Sigma G)
$$

which _preserves the first projection_, i.e. we have $\pi_1(h(i, x)) =
i$. This means that it corresponds to a dependent function $h : F(i) \to
G(i)$, and, since the morphisms in $I$-qua-category are trivial, this
dependent function is automatically a natural transformation.

```agda
  Total-space-is-ff : is-fully-faithful Total-space
  Total-space-is-ff {F} {G} = is-iso→is-equiv $
    iso from linv (λ x → ext λ _ _ → transport-refl _) where

    from : /-Hom (Total-space .F₀ F) (Total-space .F₀ G) → F => G
    from mp = nt where
      eta : ∀ i → F ʻ i → G ʻ i
      eta i j = subst (G ʻ_) (mp .com · _) (mp .map (i , j) .snd)

      nt : F => G
      nt .η = eta
      nt .is-natural _ _ reflᵢ =
        eta _ ⊙ F .F₁ reflᵢ ≡⟨ ap (eta _ ⊙_) (F .F-id) ⟩
        eta _               ≡˘⟨ ap (_⊙ eta _) (G .F-id) ⟩
        G .F₁ reflᵢ ⊙ eta _ ∎
```

<!--
```agda
    linv : is-left-inverse (F₁ Total-space) from
    linv x = ext λ y s → Σ-pathp (sym (x .com $ₚ _)) (to-pathp⁻ refl)
```
-->

All that remains is showing that sending a map $p$ to the total space of
its family of fibres gets us all the way back around to $p$.
Fortunately, our proof that universes are [[object classifiers]]
grappled with many of the same concerns, so we have a reusable
equivalence `Total-equiv`{.Agda} which slots right in. By univalence, we
can finish in style: not only is $\Sigma (x \mapsto p\inv(x))$
_isomorphic_ to $p$ in $\Sets/I$, it's actually _identical_ to $p$!

```agda
  Total-space-is-eso : is-split-eso Total-space
  Total-space-is-eso fam = functor , path→iso path where
    functor : Functor _ _
    functor = Disc-diagram (λ i → el! (fibre (fam .map) i))

    path : Total-space .F₀ functor ≡ fam
    path = /-Obj-path (n-ua (Total-equiv _  e⁻¹)) (ua→ λ a → sym (a .snd .snd))
```

# Slices preserve univalence

In passing, we can put together the following result: any slice of a
[[univalent category]] is univalent again. That's because an
_identification_ $p : (X, f) \equiv (Y, g) : \cC/x$ is given by an
identification $p' : X \equiv Y$ and a proof that $f = g$ over $p$.  We
already have a characterisation of dependent identifications in a space
of morphisms, in terms of composition with the induced isomorphisms, so
that this latter condition reduces to showing $p \circ f = g$.

<!--
```agda
module _ {C : Precategory o ℓ} {o : ⌞ C ⌟} (isc : is-category C) where
  private
    module C   = Cat.Reasoning C
    module C/o = Cat.Reasoning (Slice C o)

    open /-Obj
    open /-Hom
    open C/o._≅_
    open C._≅_
```
-->

Therefore, if we have an isomorphism $i : f \cong g$ over $x$, and its
component in $\cC$ corresponds to an identification $X \equiv Y$, then
the commutativity of $i$ is exactly the data we need to extend this to
an identification $(X, f) \equiv (Y, g)$.

```agda
  slice-is-category : is-category (Slice C o)
  slice-is-category .to-path x = /-Obj-path (isc .to-path $
    C.make-iso (x .to .map) (x .from .map)
      (ap map (C/o._≅_.invl x)) (ap map (C/o._≅_.invr x)))
    (Univalent.Hom-pathp-refll-iso isc (x .from .com))
  slice-is-category .to-path-over x = C/o.≅-pathp refl _ $
    /-Hom-pathp _ _ (Univalent.Hom-pathp-reflr-iso isc (C.idr _))
```

<!--
```agda
open /-Obj
open /-Hom
```
-->

# Constant families {defines="constant-family"}

If $\cC/B$ is the category of _families of $\cC$-objects indexed by
$B$_, it stands to reason that we should be able to consider _any_
object $A : \cC$ as a family over $B$, where each fibre of the family is
isomorphic to $A$. Type-theoretically, this would correspond to taking a
closed type and trivially regarding it as living in a context $\Gamma$
by ignoring the context entirely.

From the perspective of slice categories, the **constant families
functor**, $\Delta : \cC \to \cC/B$, sends an object $A : \cC$ to the
projection morphism $\pi_2 : A \times B \to B$.

```agda
module _ {o ℓ} {C : Precategory o ℓ} {B} (prod : has-products C) where
  open Binary-products C prod
  open Cat.Reasoning C

  constant-family : Functor C (Slice C B)
  constant-family .F₀ A = cut (π₂ {a = A})
  constant-family .F₁ f .map = ⟨ f ∘ π₁ , π₂ ⟩
  constant-family .F₁ f .com = π₂∘⟨⟩
  constant-family .F-id    = ext (sym (⟨⟩-unique id-comm (idr _)))
  constant-family .F-∘ f g = ext $ sym $
      ⟨⟩-unique (pulll π₁∘⟨⟩ ∙ extendr π₁∘⟨⟩) (pulll π₂∘⟨⟩ ∙ π₂∘⟨⟩)
```

We can observe that this really is a _constant families_ functor by
performing the following little calculation: If we have a map $h : Y \to
B$, then the fibre of $\Delta_B(A)$ over $h$ is isomorphic to $A \times Y$;
that is, we have the following pullback square:

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  {A \times Y} \&\& {A \times B} \\
  \\
  Y \&\& {B\text{.}}
  \arrow["{\pi_2}"', from=1-1, to=3-1]
  \arrow["h"', from=3-1, to=3-3]
  \arrow["{A \times h}", from=1-1, to=1-3]
  \arrow["{\pi_2}", from=1-3, to=3-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

The extra generality makes it a bit
harder to see the constancy, but if $h$ were a point $h : \top \to B$,
the fibre over $h$ would correspondingly be isomorphic to $A \times \top
\cong A$.

```agda
  constant-family-fibre
    : ∀ {A Y} (h : Hom Y B)
    → is-pullback C π₂ h (id {A} ⊗₁ h) π₂
  constant-family-fibre {A} h .square =
    sym π₂∘⟨⟩
  constant-family-fibre {A} h .universal {p₁' = p₁'} {p₂' = p₂'} sq =
    ⟨ π₁ ∘ p₂' , p₁' ⟩
  constant-family-fibre {A} h .p₁∘universal = π₂∘⟨⟩
  constant-family-fibre {A} h .p₂∘universal {p = p} =
    ⟨⟩∘ _ ∙ sym (⟨⟩-unique
      (sym (idl _) ∙ pushr (sym π₁∘⟨⟩))
      (sym p ∙ pushr (sym π₂∘⟨⟩)))
  constant-family-fibre {A} h .unique c₁ c₂ =
    ⟨⟩-unique
      (sym (idl _) ∙ extendl (sym π₁∘⟨⟩) ∙ (refl⟩∘⟨ c₂))
      c₁
```

The constant families functor is a [[right adjoint]] to the projection
$\cC/B \to \cC$. This can be understood in terms of [[base change|pullback functor]]:
if $\cC$ has a [[terminal object]] $\top$, then the slice $\cC/\top$ is
equivalent to $\cC$, and the unique map $B \to \top$ induces a pullback
functor $\cC \to \cC/B$ that is just the constant families functor.
On the other hand, the "dependent sum" functor sends a map $A \to B$
to the unique composite $A \to B \to \top$: it simply `Forget/`{.Agda}s the
map. Thus the following adjunction is a special case of the
adjunction between [[dependent sum]] and base change.

```agda
  Forget⊣constant-family : Forget/ ⊣ constant-family
  Forget⊣constant-family .unit .η X .map = ⟨ id , X .map ⟩
  Forget⊣constant-family .unit .η X .com = π₂∘⟨⟩
  Forget⊣constant-family .unit .is-natural _ _ f = ext (⟨⟩-unique₂
    (pulll π₁∘⟨⟩ ∙ id-comm-sym)
    (pulll π₂∘⟨⟩ ∙ f .com)
    (pulll π₁∘⟨⟩ ∙ pullr π₁∘⟨⟩)
    (pulll π₂∘⟨⟩ ∙ π₂∘⟨⟩))
  Forget⊣constant-family .counit .η x = π₁
  Forget⊣constant-family .counit .is-natural _ _ f = π₁∘⟨⟩
  Forget⊣constant-family .zig = π₁∘⟨⟩
  Forget⊣constant-family .zag = ext (⟨⟩-unique₂
    (pulll π₁∘⟨⟩ ∙ pullr π₁∘⟨⟩)
    (pulll π₂∘⟨⟩ ∙ π₂∘⟨⟩)
    refl
    (idr _))
```

Furthermore, this adjunction is [[comonadic]]! First, notice
that the [[induced comonad|comonad from an adjunction]] $U \circ \Delta$
on $\cC$ is none other than the [[writer comonad]] $B \times -$, up to
swapping.

```agda
  UΔ≡Writer : Forget/ F∘ constant-family ≅ⁿ Writer C B (prod B)
  UΔ≡Writer = iso→isoⁿ
    (λ _ → invertible→iso swap swap-is-iso)
    λ f → (ap ⟨_, f ∘ π₂ ⟩ (sym (idl _)) ⟩∘⟨refl)
       ∙∙ swap-natural (f , id)
       ∙∙ (refl⟩∘⟨ ap ⟨ f ∘ π₁ ,_⟩ (idl _))
```

It remains to ponder what a $U\Delta$-coalgebra on $A$ is: this should
consist of a map $\langle f, g \rangle : A \to A \times B$ obeying some
laws. In particular, the `counit law`{.Agda ident=ρ-counit} implies that
$f = \id$, so that we are left with $g : A \to B$, an object of $\cC/B$!

```agda
  Forget/-comonadic : is-comonadic Forget⊣constant-family
  Forget/-comonadic = is-precat-iso→is-equivalence
    (iso (is-iso→is-equiv ff) (is-iso→is-equiv eso))
    where
      open is-iso

      eso : is-iso (Comparison-CoEM Forget⊣constant-family .F₀)
      eso .from (X , c) = cut (π₂ ∘ c .ρ)
      eso .rinv (X , c) = refl ,ₚ ext (sym (⟨⟩-unique (c .ρ-counit) refl))
      eso .linv _ = /-Obj-path refl π₂∘⟨⟩
```

A short computation shows that morphisms of $U\Delta$-coalgebras also
precisely correspond to commuting triangles, so we get an [[isomorphism
of precategories]] between the category of $U\Delta$-coalgebras and
$\cC/B$.

```agda
      ff : ∀ {x y} → is-iso (Comparison-CoEM Forget⊣constant-family .F₁ {x} {y})
      ff .from f .map = f .fst
      ff {x} {y} .from f .com =
        y .map ∘ f .fst                             ≡˘⟨ pulll π₂∘⟨⟩ ⟩
        π₂ ∘ ⟨ id , y .map ⟩ ∘ f .fst               ≡˘⟨ refl⟩∘⟨ f .snd ⟩
        π₂ ∘ ⟨ f .fst ∘ π₁ , π₂ ⟩ ∘ ⟨ id , x .map ⟩ ≡⟨ pulll π₂∘⟨⟩ ⟩
        π₂ ∘ ⟨ id , x .map ⟩                        ≡⟨ π₂∘⟨⟩ ⟩
        x .map                                      ∎
      ff .rinv _ = ext refl
      ff .linv _ = ext refl
```
