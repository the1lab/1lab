```agda
open import Cat.Prelude
open import Cat.Univalent

open import Order.Base

import Cat.Reasoning

module Order.Instances.Subobjects where
```

# Posets of subobjects

Let $\ca{C}$ be a [category] and $A : \ca{C}$ an arbitrary object. We're
interested here in the restriction of the slice category $\ca{C}/A$ to
those objects whose map is a monomorphism. This restriction turns out to
be a poset.

[category]: Cat.Univalent.html#univalent-categories

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) (c-cat : is-category C) (A : Precategory.Ob C) where
  private module C = Cat.Reasoning C
  open C._↪_
```
-->

Here's why: First, we define the $\le$ relation "as usual", i.e., $X \le
Y$ consists of the commuting triangles as in the diagram below.

~~~{.quiver .short-15}
\[\begin{tikzcd}
  B && C \\
  \\
  & A
  \arrow["f", from=1-1, to=1-3]
  \arrow["X"', from=1-1, to=3-2]
  \arrow["Y", from=1-3, to=3-2]
\end{tikzcd}\]
~~~

```agda
  Subobjects : C.Ob → Poset _ _
  Subobjects A = to-poset (Σ C.Ob λ B → B C.↪ A) mk where
    open make-poset

    mk : make-poset ℓ (Σ (C .Precategory.Ob) (λ B → B C.↪ A))
    mk .rel (B , f) (C , h) = Σ (C.Hom B C) λ g → h .mor C.∘ g ≡ f .mor
    mk .id = C.id , C.idr _
    mk .trans (f , α) (g , β) = g C.∘ f , C.pulll β ∙ α
```

The first thing we must verify is that this is indeed a proposition:
there is at most one such triangle. Why? Well, $Y$ is a monomorphism!
Suppose we have $f, f' : B \to C$ as in the diagram. Then we have $Yf =
g = Yf'$, so $f = f'$.

```agda
    mk .thin {y = y} (f , α) (g , β) = Σ-prop-path! (y .snd .monic _ _ (α ∙ sym β))
```

Now, it's certainly _not_ the case that you can get an isomorphism $A
\cong B$ from any ol' pair of morphisms $f : A \to B$ and $g : B \to A$.
But if we're talking morphisms in a slice between monomorphisms, then we
have a much better shot: Instead of having to show $fg = \rm{id}$
(hard), we can show $Yfg = Y$, which follows from commutativity of the
triangles. So the subjects of $A$ are a poset!

```agda
    mk .antisym {X , x} {Y , y} (f , α) (g , β) =
      Σ-pathp (c-cat .to-path im) (C.↪-pathp (Univalent.Hom-pathp-refll-iso c-cat β))
      where
        im : X C.≅ Y
        im = C.make-iso f g (y .monic _ _ (C.pulll α ·· β ·· C.intror refl))
                            (x .monic _ _ (C.pulll β ·· α ·· C.intror refl))
```
