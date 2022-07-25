```agda
open import Cat.Prelude

import Cat.Diagram.Pullback
import Cat.Reasoning

module Cat.Diagram.Pullback.Properties {o ℓ} {C : Precategory o ℓ} where
```

<!--
```agda
open Cat.Diagram.Pullback C
open Cat.Reasoning C
open is-pullback

private variable
  A B P : Ob
  f g h : Hom A B
```
-->

# Properties of pullbacks

This module chronicles some general properties of [pullbacks].

[pullbacks]: Cat.Diagram.Pullback.html

## Pasting law

The pasting law for pullbacks says that, if in the _commutative_ diagram
below the the right square is a pullback, then the left square is
universal if, and only if, the outer rectangle is, too. Note the
emphasis on the word commutative: if we don't know that both squares
(and the outer rectangle) all commute, the pasting law does not go
through.

~~~{.quiver}
\[\begin{tikzcd}
  a && b && c \\
  \\
  d && e && f
  \arrow[from=1-1, to=3-1]
  \arrow[from=1-1, to=1-3]
  \arrow[from=1-3, to=1-5]
  \arrow[from=1-3, to=3-3]
  \arrow[from=3-1, to=3-3]
  \arrow[from=1-5, to=3-5]
  \arrow[from=3-3, to=3-5]
\end{tikzcd}\]
~~~

```
module _ {a b c d e f : Ob}
         {a→d : Hom a d} {a→b : Hom a b} {b→c : Hom b c}
         {d→e : Hom d e} {b→e : Hom b e} {e→f : Hom e f}
         {c→f : Hom c f}
         (right-pullback : is-pullback b→c c→f b→e e→f)
  where

  private module right = is-pullback right-pullback
```

Let's start with proving that, if the outer rectangle is a pullback,
then so is the left square. Assume, then, that we have some other object
$x$, which fits into a cone, like in the diagram below. I've coloured
the two arrows we assume commutative.

~~~{.quiver .tall-2}
\[\begin{tikzcd}
  x \\
  & a && b && c \\
  \\
  & d && e && f
  \arrow[from=2-2, to=4-2]
  \arrow[from=2-2, to=2-4]
  \arrow[from=2-4, to=2-6]
  \arrow[color={rgb,255:red,214;green,92;blue,92}, from=2-4, to=4-4]
  \arrow[color={rgb,255:red,214;green,92;blue,92}, from=4-2, to=4-4]
  \arrow[from=2-6, to=4-6]
  \arrow[from=4-4, to=4-6]
  \arrow[color={rgb,255:red,214;green,92;blue,92}, curve={height=-12pt}, from=1-1, to=2-4]
  \arrow[color={rgb,255:red,214;green,92;blue,92}, curve={height=12pt}, from=1-1, to=4-2]
\end{tikzcd}\]
~~~

```agda
  pasting-outer→left-is-pullback
    : is-pullback (b→c ∘ a→b) c→f a→d (e→f ∘ d→e)
    → (square : b→e ∘ a→b ≡ d→e ∘ a→d)
    → is-pullback a→b b→e a→d d→e
  pasting-outer→left-is-pullback outer square = pb where
    module outer = is-pullback outer
```

To appeal to the universal property of the outer pullback, we must
somehow extend our red cone over $b \to e \ot d$ to one over $c \to f
\ot e$. Can we do this? Yes! By assumption, the square on the right
commutes, which lets us apply commutativity of the red diagram (the
assumption $p$ in the code). Check out the calculation below:

```agda
    abstract
      path : ∀ {P} {P→b : Hom P b} {P→d : Hom P d} (p : b→e ∘ P→b ≡ d→e ∘ P→d)
           → c→f ∘ b→c ∘ P→b ≡ (e→f ∘ d→e) ∘ P→d
      path {_} {P→b} {P→d} p =
        c→f ∘ b→c ∘ P→b   ≡⟨ extendl right.square ⟩
        e→f ∘ b→e ∘ P→b   ≡⟨ ap (e→f ∘_) p ⟩
        e→f ∘ d→e ∘ P→d   ≡⟨ solve! C ⟩
        (e→f ∘ d→e) ∘ P→d ∎

    pb : is-pullback _ _ _ _
    pb .is-pullback.square =
      b→e ∘ a→b ≡⟨ square ⟩
      d→e ∘ a→d ∎
```

We thus have an induced map $x \to a$, which, since $a$ is a pullback,
makes everything in sight commute, and does so uniquely.

```agda
    pb .limiting {p₁' = P→b} {p₂' = P→d} p =
      outer.limiting {p₁' = b→c ∘ P→b} {p₂' = P→d} (path p)

    pb .p₁∘limiting {p₁' = P→b} {p₂' = P→d} {p = p} =
      right.unique₂ {p = pulll right.square ∙ pullr p}
        (assoc _ _ _ ∙ outer.p₁∘limiting)
        (pulll square ∙ pullr outer.p₂∘limiting)
        refl p

    pb .p₂∘limiting {p₁' = P→b} {p₂' = P→d} {p = p} = outer.p₂∘limiting

    pb .unique {p = p} q r =
      outer.unique (sym (ap (_ ∘_) (sym q) ∙ assoc _ _ _)) r
```

For the converse, suppose that both small squares are a pullback, and we
have a cone over $c \to f \ot d$. By the universal property of the right
pullback, we can find a map $x \to b$ forming the left leg of a cone
over $b \to e \ot d$; By the universal property of the _left_ square, we
then have a map $x \to a$, as we wanted.

```agda
  pasting-left→outer-is-pullback
    : is-pullback a→b b→e a→d d→e
    → (square : c→f ∘ b→c ∘ a→b ≡ (e→f ∘ d→e) ∘ a→d)
    → is-pullback (b→c ∘ a→b) c→f a→d (e→f ∘ d→e)
  pasting-left→outer-is-pullback left square = pb where
    module left = is-pullback left

    pb : is-pullback (b→c ∘ a→b) c→f a→d (e→f ∘ d→e)
    pb .is-pullback.square =
      c→f ∘ b→c ∘ a→b   ≡⟨ square ⟩
      (e→f ∘ d→e) ∘ a→d ∎
    pb .limiting {p₁' = P→c} {p₂' = P→d} x =
      left.limiting {p₁' = right.limiting (x ∙ sym (assoc _ _ _))} {p₂' = P→d}
        right.p₂∘limiting
    pb .p₁∘limiting = pullr left.p₁∘limiting ∙ right.p₁∘limiting
    pb .p₂∘limiting = left.p₂∘limiting
    pb .unique {p₁' = P→c} {P→d} {p = p} {lim'} q r =
      left.unique (right.unique (assoc _ _ _ ∙ q) s) r
      where
        s : b→e ∘ a→b ∘ lim' ≡ d→e ∘ P→d
        s =
          b→e ∘ a→b ∘ lim'   ≡⟨ pulll left.square ⟩
          (d→e ∘ a→d) ∘ lim' ≡⟨ pullr r ⟩
          d→e ∘ P→d          ∎
```

## Monomorphisms

Being a monomorphism is a "limit property". Specifically, $f : A \to B$
is a monomorphism iff. the square below is a pullback.

~~~{.quiver}
\[\begin{tikzcd}
  a && a \\
  \\
  a && b
  \arrow["f", from=1-3, to=3-3]
  \arrow["f"', from=3-1, to=3-3]
  \arrow["{\mathrm{id}}", from=1-1, to=1-3]
  \arrow["{\mathrm{id}}"', from=1-1, to=3-1]
\end{tikzcd}\]
~~~

```agda
module _ {a b} {f : Hom a b} where
  is-monic→is-pullback : is-monic f → is-pullback id f id f
  is-monic→is-pullback mono .square = refl
  is-monic→is-pullback mono .limiting {p₁' = p₁'} p = p₁'
  is-monic→is-pullback mono .p₁∘limiting = idl _
  is-monic→is-pullback mono .p₂∘limiting {p = p} = idl _ ∙ mono _ _ p
  is-monic→is-pullback mono .unique p q = introl refl ∙ p

  is-pullback→is-monic : is-pullback id f id f → is-monic f
  is-pullback→is-monic pb f g p = sym (pb .p₁∘limiting {p = p}) ∙ pb .p₂∘limiting
```

Pullbacks additionally preserve monomorphisms, as shown below:

```agda
is-monic→pullback-is-monic
  : ∀ {x y z} {f : Hom x z} {g : Hom y z} {p} {p1 : Hom p x} {p2 : Hom p y}
  → is-monic f
  → is-pullback p1 f p2 g
  → is-monic p2
is-monic→pullback-is-monic {f = f} {g} {p1 = p1} {p2} mono pb h j p = eq
  where
    module pb = is-pullback pb
    q : f ∘ p1 ∘ h ≡ f ∘ p1 ∘ j
    q =
      f ∘ p1 ∘ h ≡⟨ extendl pb.square ⟩
      g ∘ p2 ∘ h ≡⟨ ap (g ∘_) p ⟩
      g ∘ p2 ∘ j ≡˘⟨ extendl pb.square ⟩
      f ∘ p1 ∘ j ∎

    r : p1 ∘ h ≡ p1 ∘ j
    r = mono _ _ q

    eq : h ≡ j
    eq = pb.unique₂ {p = extendl pb.square} r p refl refl
```

<!--
```agda
rotate-pullback
  : ∀ {x y z} {f : Hom x z} {g : Hom y z} {p} {p1 : Hom p x} {p2 : Hom p y}
  → is-pullback p1 f p2 g
  → is-pullback p2 g p1 f
rotate-pullback pb .square = sym (pb .square)
rotate-pullback pb .limiting p = pb .limiting (sym p)
rotate-pullback pb .p₁∘limiting = pb .p₂∘limiting
rotate-pullback pb .p₂∘limiting = pb .p₁∘limiting
rotate-pullback pb .unique p q = pb .unique q p

is-pullback-iso
  : ∀ {p p′ x y z} {f : Hom x z} {g : Hom y z} {p1 : Hom p x} {p2 : Hom p y}
  → (i : p ≅ p′)
  → is-pullback p1 f p2 g
  → is-pullback (p1 ∘ _≅_.from i) f (p2 ∘ _≅_.from i) g
is-pullback-iso {f = f} {g} {p1} {p2} i pb = pb′ where
  module i = _≅_ i
  pb′ : is-pullback _ _ _ _
  pb′ .square = extendl (pb .square)
  pb′ .limiting p = i.to ∘ pb .limiting p
  pb′ .p₁∘limiting = cancel-inner i.invr ∙ pb .p₁∘limiting
  pb′ .p₂∘limiting = cancel-inner i.invr ∙ pb .p₂∘limiting
  pb′ .unique p q = invertible→monic (iso→invertible (i Iso⁻¹)) _ _ $ sym $
    cancell i.invr ∙ sym (pb .unique (assoc _ _ _ ∙ p) (assoc _ _ _ ∙ q))

pullback-unique
  : ∀ {p p′ x y z} {f : Hom x z} {g : Hom y z} {p1 : Hom p x} {p2 : Hom p y}
      {p1′ : Hom p′ x} {p2′ : Hom p′ y}
  → is-pullback p1 f p2 g
  → is-pullback p1′ f p2′ g
  → p ≅ p′
pullback-unique {f = f} {g} {p1} {p2} {p1′} {p2′} pb pb′
  = make-iso pb→pb′ pb′→pb il ir
  where
    pb→pb′ = pb′ .limiting (pb .square)
    pb′→pb = pb .limiting (pb′ .square)
    il = unique₂ pb′ {p = pb′ .square}
      (pulll (pb′ .p₁∘limiting) ∙ pb .p₁∘limiting)
      (pulll (pb′ .p₂∘limiting) ∙ pb .p₂∘limiting)
      (idr _) (idr _)
    ir = unique₂ pb {p = pb .square}
      (pulll (pb .p₁∘limiting) ∙ pb′ .p₁∘limiting)
      (pulll (pb .p₂∘limiting) ∙ pb′ .p₂∘limiting)
      (idr _) (idr _)
```
-->
