```agda
open import Cat.Prelude

open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product

module Cat.Instances.Slice where
```

<!--
```agda
private variable
  o ℓ : Level

module _ {o ℓ} {C : Precategory o ℓ} where
  import Cat.Reasoning C as C
  private variable
    a b c : C.Ob
```
-->

# Slice categories

When working in $\sets$, there is an evident notion of _family indexed
by a set_: a family of sets $(F_i)_{i \in I}$ is equivalently a functor
$[\mathrm{Disc}(I), \sets]$, where we have equipped the set $I$ with the
[discrete category] structure. This works essentially because of the
[discrete category-global sections][coh] adjunction, but in general this
can not be applied to other categories, like $\mathrm{Groups}$. How,
then, should we work with "indexed families" in general categories?

[discrete category]: Cat.Instances.Discrete.html
[coh]: Cat.Instances.StrictCat.Cohesive.html#disc-γ

The answer is to consider, rather than families themselves, the
_projections from their total spaces_ as the primitive objects. A family
indexed by $I$, then, would consist of an object $A$ and a morphism $t :
A \to I$, where $A$ is considered as the "total space" object and $t$
assigns gives the "tag" of each object. By analysing how $t$ [pulls
back] along maps $B \to I$, we recover a notion of "fibres": the
collection with index $i$ can be recovered as the pullback $t*i$.

[pulls back]: Cat.Diagram.Pullback.html

Note that, since the discussion in the preceding paragraph made no
mention of the category of sets, it applies in any category! More
generally, for any category $\ca{C}$ and object $c : \ca{C}$, we have a
_category of objects indexed by $c$_, the **slice category** $\ca{C}/c$.
An object of "the slice over $c$" is given by an object $d : \ca{C}$ to
serve as the domain, and a map $f : d \to c$.

```agda
  record /-Obj (c : C.Ob) : Type (o ⊔ ℓ) where
    no-eta-equality
    constructor cut
    field
      {domain} : C.Ob
      map      : C.Hom domain c
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
      map      : C.Hom a.domain b.domain
      commutes : b.map C.∘ map ≡ a.map
```

<!--
```agda
  /-Hom-pathp : ∀ {c a a′ b b′} (p : a ≡ a′) (q : b ≡ b′)
                {x : /-Hom {c = c} a b} {y : /-Hom a′ b′}
              → PathP (λ i → C.Hom (p i ./-Obj.domain) (q i ./-Obj.domain)) 
                        (x ./-Hom.map) (y ./-Hom.map)
              → PathP (λ i → /-Hom (p i) (q i)) x y
  /-Hom-pathp p q {x} {y} r = path where
    open /-Hom

    path : PathP (λ i → /-Hom (p i) (q i))  x y
    path i .map = r i
    path i .commutes = 
      is-prop→pathp 
        (λ i → C.Hom-set (p i ./-Obj.domain) _ 
                         (q i ./-Obj.map C.∘ r i) (p i ./-Obj.map)) 
        (x .commutes) (y .commutes) i

  /-Hom-path : ∀ {c a b} {x y : /-Hom {c = c} a b}
             → x ./-Hom.map ≡ y ./-Hom.map
             → x ≡ y
  /-Hom-path = /-Hom-pathp refl refl

  /-Hom-is-set : ∀ {c a b} → is-set (/-Hom {c = c} a b)
  /-Hom-is-set {a = a} {b} = 
    retract→is-hlevel 2 pack unpack inv T-is-set 
    where abstract
      module a = /-Obj a
      module b = /-Obj b

      T : Type ℓ
      T = Σ[ map ∈ C.Hom a.domain b.domain ] (b.map C.∘ map ≡ a.map)

      T-is-set : is-set T
      T-is-set = Σ-is-hlevel 2 (C.Hom-set _ _) 
                               (λ _ → is-prop→is-set (C.Hom-set _ _ _ _))

      pack : T → /-Hom a b
      pack (f , g) ./-Hom.map = f
      pack (f , g) ./-Hom.commutes = g

      unpack : /-Hom a b → T
      unpack x = x ./-Hom.map , x ./-Hom.commutes

      inv : is-left-inverse pack unpack
      inv x = /-Hom-path refl
```
-->

The slice category $\ca{C}/c$ is given by the `/-Obj`{.Agda} and
`/-Hom`{.Agda}s.

```agda
Slice : (C : Precategory o ℓ) → Precategory.Ob C → Precategory _ _
Slice C c = precat where
  import Cat.Reasoning C as C
  open Precategory
  open /-Hom
  open /-Obj

  precat : Precategory _ _
  precat .Ob = /-Obj {C = C} c
  precat .Hom = /-Hom
  precat .Hom-set x y = /-Hom-is-set
  precat .id .map      = C.id
  precat .id .commutes = C.idr _
```

For composition in the slice over $c$, note that if the triangle (the
commutativity condition for $f$) and the rhombus (the commutativity
condition for $g$) both commute, then so does the larger triangle (the
commutativity for $g \circ f$).

~~~{.quiver .tall-1}
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
    fog .commutes = 
      z .map C.∘ f.map C.∘ g.map ≡⟨ C.pulll f.commutes ⟩
      y .map C.∘ g.map           ≡⟨ g.commutes ⟩
      x .map                     ∎
  precat .idr f = /-Hom-path (C.idr _)
  precat .idl f = /-Hom-path (C.idl _)
  precat .assoc f g h = /-Hom-path (C.assoc _ _ _)
```

## Limits

We discuss some limits in the slice of $\ca{C}$ over $c$. First, every
slice category has a terminal object, given by the identity map
$\mathrm{id} : c \to c$.

```agda
module _ {o ℓ} {C : Precategory o ℓ} {c : Precategory.Ob C} where
  import Cat.Reasoning C as C
  import Cat.Reasoning (Slice C c) as C/c
  open /-Hom
  open /-Obj

  Slice-terminal-object : is-terminal (Slice C c) (cut C.id)
  Slice-terminal-object obj .centre .map = obj .map
  Slice-terminal-object obj .centre .commutes = C.idl _
  Slice-terminal-object obj .paths other = 
    /-Hom-path (sym (other .commutes) ∙ C.idl _)
```

Products in a slice category are slightly more complicated, but recall
that another word for pullback is "fibred product". Indeed, in the
pullback page we noted that the pullback of $X \to Z$ and $Y \to Z$ is
exactly the product of those maps in the slice over $Z$.

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} {c : Precategory.Ob C} where
  import Cat.Reasoning C as C
  import Cat.Reasoning (Slice C c) as C/c
  private variable
    a b : C.Ob
    f g π₁ π₂ : C.Hom a b
  open /-Hom
  open /-Obj
```
-->

Suppose we have a pullback diagram like the one below, i.e., a limit of
the diagram $a \xrightarrow{f} c \xleftarrow{g} b$, in the category
$\ca{C}$. We'll show that it's also a limit of the (discrete) diagram
consisting of $f$ and $g$, but now in the slice category $\ca{C}/c$. 

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

For starters, note that we have seemingly "two" distinct choices for
maps $a \times_c b \to c$, but since the square above commutes, either
one will do. For definiteness, we go with the composite $f \circ \pi_1$.

```agda
  module _ {f : C.Hom a c} {g : C.Hom b c} (pb : is-pullback C π₁ f π₂ g) where
    private module pb = is-pullback pb

    is-pullback→product-over : C/c.Ob
    is-pullback→product-over = cut (f C.∘ π₁)
```

Now, by commutativity of the square, the maps $\pi_1$ and $\pi_2$ in the
diagram above extend to maps $(f \circ \pi_1) \to f$ and $(f \circ
\pi_1) \to g$ in $\ca{C}/c$. Indeed, note that by scribbling a red line
across the diagonal of the diagram, we get the two needed triangles as
the induced subdivisions.

~~~{.quiver}
\[\begin{tikzcd}
  {X \times_Z Y} && X \\
  \\
  Y && Z
  \arrow["{\pi_2}"', from=1-1, to=3-1]
  \arrow["{\pi_1}", from=1-1, to=1-3]
  \arrow["f", from=1-3, to=3-3]
  \arrow["g"', from=3-1, to=3-3]
  \arrow["{f \circ \pi_1}"{description}, color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

```agda
    is-pullback→π₁ : C/c.Hom is-pullback→product-over (cut f)
    is-pullback→π₁ .map      = π₁
    is-pullback→π₁ .commutes = refl

    is-pullback→π₂ : C/c.Hom is-pullback→product-over (cut g)
    is-pullback→π₂ .map      = π₂
    is-pullback→π₂ .commutes = sym pb.square

    open is-product
```

Unfolding what it means for a diagram to be a universal cone over the
discrete diagram consisting of $f$ and $g$ in the category $\ca{C}/c$,
we see that it is exactly the data of the pullback of $f$ and $g$ in
$\ca{C}$, as below:

```agda
    is-pullback→is-fibre-product 
      : is-product (Slice C c) is-pullback→π₁ is-pullback→π₂
    is-pullback→is-fibre-product .⟨_,_⟩ {Q} /f /g = factor
      where
        module f = /-Hom /f
        module g = /-Hom /g

        factor : C/c.Hom Q _
        factor .map = pb.limiting (f.commutes ∙ sym g.commutes)
        factor .commutes = 
          (f C.∘ π₁) C.∘ pb.limiting _ ≡⟨ C.pullr pb.p₁∘limiting ⟩
          f C.∘ f.map                  ≡⟨ f.commutes ⟩
          Q .map                       ∎

    is-pullback→is-fibre-product .π₁∘factor = /-Hom-path pb.p₁∘limiting
    is-pullback→is-fibre-product .π₂∘factor = /-Hom-path pb.p₂∘limiting
    is-pullback→is-fibre-product .unique other p q = 
      /-Hom-path (pb.unique (ap map p) (ap map q))

  Pullback→Fibre-product 
    : ∀ {f : C.Hom a c} {g : C.Hom b c}
    → Pullback C f g → Product (Slice C c) (cut f) (cut g)
  Pullback→Fibre-product pb .Product.apex = _
  Pullback→Fibre-product pb .Product.π₁ = _
  Pullback→Fibre-product pb .Product.π₂ = _
  Pullback→Fibre-product pb .Product.has-is-product = 
    is-pullback→is-fibre-product (pb .Pullback.has-is-pb)
```