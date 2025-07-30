<!--
```agda
open import Cat.Bi.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Bi.Diagram.Adjunction where
```

<!--
```agda
open _=>_

module _ {o ℓ ℓ'} (B : Prebicategory o ℓ ℓ') where
  private module B = Prebicategory B
```
-->

# Adjunctions in a bicategory

Let $\bf{B}$ be a [[bicategory]], $A, B : \bf{B}$ be objects, and $f : A \to
B$ and $g : B \to A$ be 1-cells. Generalising the situation where $f$
and $g$ are [[functors]], we say they are **adjoints** if there exist
2-cells $\eta : \id \to gf$ and $\eps : fg \to \id$ (the
**unit** and **counit** respectively), satisfying the equations

<div class=mathpar>

~~~{.quiver}
\[\begin{tikzcd}
  & fgf \\
  f && f
  \arrow["{\varepsilon \blacktriangleleft f}", from=1-2, to=2-3]
  \arrow["{f \blacktriangleright \eta}", from=2-1, to=1-2]
  \arrow["{\mathrm{id}}"', from=2-1, to=2-3]
\end{tikzcd}\]
~~~

and

~~~{.quiver}
\[\begin{tikzcd}
  g && {g,} \\
  & gfg
  \arrow["{\mathrm{id}}", from=1-1, to=1-3]
  \arrow["{\eta \blacktriangleleft g}"', from=1-1, to=2-2]
  \arrow["{g \blacktriangleright \varepsilon}"', from=2-2, to=1-3]
\end{tikzcd}\]
~~~

</div>

called the **triangle identities** (because of their shape) or **zigzag
identities** (because it sounds cool). Note that we have to insert
appropriate associators and unitors in order to translate the diagrams
above into equations that are well-typed in a (weak) bicategory.

```agda
  record _⊣_ {a b : B.Ob} (f : a B.↦ b) (g : b B.↦ a) : Type ℓ' where
    field
      η : B.id B.⇒ (g B.⊗ f)
      ε : (f B.⊗ g) B.⇒ B.id

      zig : B.Hom.id ≡ B.λ← f B.∘ (ε B.◀ f) B.∘ B.α← f g f B.∘ (f B.▶ η) B.∘ B.ρ→ f
      zag : B.Hom.id ≡ B.ρ← g B.∘ (g B.▶ ε) B.∘ B.α→ g f g B.∘ (η B.◀ g) B.∘ B.λ→ g
```

This means the triangle identities, rather
than simply expressing a compatibility relation between $\eta$ and
$\eps$ as is the case for [[adjoint functors]], instead exhibit a
complicated compatibility relation between $\eta$, $\eps$, and the
structural isomorphisms (the unitors and associator) of the ambient
bicategory.
