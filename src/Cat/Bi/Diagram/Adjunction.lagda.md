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

Let $\bf{B}$ be a bicategory, $A, B : \bf{B}$ be objects, and $f : A \to
B$ and $g : B \to A$ be 1-cells. Generalising the situation where $f$
and $g$ are functors, we say they are **adjoints** if there exist
2-cells $\eta : \id \to gf$ and $\eps : fg \to \id$ (the
**unit** and **counit** respectively), satisfying the equations

<div class=mathpar>

~~~{.quiver}
\[\begin{tikzcd}
  f && {(fg)f} \\
  && f
  \arrow["{\mathrm{id}}"', from=1-1, to=2-3]
  \arrow["{\alpha\otimes(f\blacktriangleright \eta)\otimes\rho}", from=1-1, to=1-3]
  \arrow["{(\varepsilon \blacktriangleleft f)\otimes\lambda}", from=1-3, to=2-3]
\end{tikzcd}\]
~~~

and

~~~{.quiver}
\[\begin{tikzcd}
  g & {g\mathrm{id}} & gfg \\
  \\
  && {g\text{,}}
  \arrow["\rho", from=1-1, to=1-2]
  \arrow["{g \blacktriangleright \eta}", from=1-2, to=1-3]
  \arrow["{\mathrm{id}}"', from=1-1, to=3-3]
  \arrow["{\varepsilon \blacktriangleleft g}", from=1-3, to=3-3]
\end{tikzcd}\]
~~~

</div>

called the **triangle identities** (because of their shape) or **zigzag
identities** (because it sounds cool).

```agda
  record _⊣_ {a b : B.Ob} (f : a B.↦ b) (g : b B.↦ a) : Type ℓ' where
    field
      η : B.id B.⇒ (g B.⊗ f)
      ε : (f B.⊗ g) B.⇒ B.id

      zig : B.Hom.id ≡ B.λ← f B.∘ (ε B.◀ f) B.∘ B.α← f g f B.∘ (f B.▶ η) B.∘ B.ρ→ f
      zag : B.Hom.id ≡ B.ρ← g B.∘ (g B.▶ ε) B.∘ B.α→ g f g B.∘ (η B.◀ g) B.∘ B.λ→ g
```

Working in a fully weak bicategory means the triangle identities, rather
than simply expressing a compatibility relation between $\eta$ and
$\eps$ as is the case for [[adjoint functors]], instead exhibit a
complicated compatibility relation between $\eta$, $\eps$, and the
structural isomorphisms (the unitors and associator) of the ambient
bicategory.

We have taken pains to draw the triangle identities as triangles, but
counting the morphisms involved you'll find that they really want to be
commutative pentagons instead (which we draw in this website as
commutative altars):

~~~{.quiver}
\[\begin{tikzcd}
  & fgf && {(fg)f} \\
  \\
  {f\mathrm{id}} && f && {\mathrm{id}f}
  \arrow["\lambda"', from=3-5, to=3-3]
  \arrow["\rho"', from=3-3, to=3-1]
  \arrow["{f\blacktriangleright \eta}", from=3-1, to=1-2]
  \arrow["\alpha"', from=1-2, to=1-4]
  \arrow["{\varepsilon \blacktriangleleft f}", from=1-4, to=3-5]
\end{tikzcd}\]
~~~
