<!--
```agda
open import Cat.Diagram.Pullback
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Pullback.Properties where
```

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C
  open is-pullback

  private variable
    A B P : Ob
    f g h : Hom A B
```
-->

# Properties of pullbacks

This module chronicles some general properties of [[pullbacks]].

## Identity

Degenerate squares where two opposite sides are identities are pullbacks.

~~~{.quiver}
\[\begin{tikzcd}
  a & a \\
  b & b
  \arrow[Rightarrow, no head, from=1-1, to=1-2]
  \arrow["f"', from=1-1, to=2-1]
  \arrow["f", from=1-2, to=2-2]
  \arrow[Rightarrow, no head, from=2-1, to=2-2]
\end{tikzcd}\]
~~~

```agda
  id-is-pullback : ∀ {a b : Ob} {f : Hom a b} → is-pullback C id f f id
  id-is-pullback .square = id-comm
  id-is-pullback .universal {p₁' = p₁'} _ = p₁'
  id-is-pullback .p₁∘universal = idl _
  id-is-pullback .p₂∘universal {p = p} = p ∙ idl _
  id-is-pullback .unique q r = sym q ∙ idl _
```

## Pasting law {defines="pasting-law-for-pullbacks"}

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

```agda
  module _ {a b c d e f : Ob}
           {a→d : Hom a d} {a→b : Hom a b} {b→c : Hom b c}
           {d→e : Hom d e} {b→e : Hom b e} {e→f : Hom e f}
           {c→f : Hom c f}
           (right-pullback : is-pullback C b→c c→f b→e e→f)
    where

    private module right = is-pullback right-pullback
```

Let's start with proving that, if the outer rectangle is a pullback,
then so is the left square. Assume, then, that we have some other object
$x$, which fits into a cone, like in the diagram below. I've coloured
the two arrows we assume commutative.

~~~{.quiver}
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
      : is-pullback C (b→c ∘ a→b) c→f a→d (e→f ∘ d→e)
      → (square : b→e ∘ a→b ≡ d→e ∘ a→d)
      → is-pullback C a→b b→e a→d d→e
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
          e→f ∘ d→e ∘ P→d   ≡⟨ cat! C ⟩
          (e→f ∘ d→e) ∘ P→d ∎

      pb : is-pullback C _ _ _ _
      pb .is-pullback.square =
        b→e ∘ a→b ≡⟨ square ⟩
        d→e ∘ a→d ∎
```

We thus have an induced map $x \to a$, which, since $a$ is a pullback,
makes everything in sight commute, and does so uniquely.

```agda
      pb .universal {p₁' = P→b} {p₂' = P→d} p =
        outer.universal {p₁' = b→c ∘ P→b} {p₂' = P→d} (path p)

      pb .p₁∘universal {p₁' = P→b} {p₂' = P→d} {p = p} =
        right.unique₂ {p = pulll right.square ∙ pullr p}
          (assoc _ _ _ ∙ outer.p₁∘universal)
          (pulll square ∙ pullr outer.p₂∘universal)
          refl p

      pb .p₂∘universal {p₁' = P→b} {p₂' = P→d} {p = p} = outer.p₂∘universal

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
      : is-pullback C a→b b→e a→d d→e
      → is-pullback C (b→c ∘ a→b) c→f a→d (e→f ∘ d→e)
    pasting-left→outer-is-pullback left = pb where
      module left = is-pullback left

      pb : is-pullback C (b→c ∘ a→b) c→f a→d (e→f ∘ d→e)
      pb .is-pullback.square =
        c→f ∘ b→c ∘ a→b   ≡⟨ extendl right.square ⟩
        e→f ∘ b→e ∘ a→b   ≡⟨ pushr left.square ⟩
        (e→f ∘ d→e) ∘ a→d ∎
      pb .universal {p₁' = P→c} {p₂' = P→d} x =
        left.universal {p₁' = right.universal (x ∙ sym (assoc _ _ _))} {p₂' = P→d}
          right.p₂∘universal
      pb .p₁∘universal = pullr left.p₁∘universal ∙ right.p₁∘universal
      pb .p₂∘universal = left.p₂∘universal
      pb .unique {p₁' = P→c} {P→d} {p = p} {lim'} q r =
        left.unique (sym (right.unique (assoc _ _ _ ∙ q) s)) r
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
    is-monic→is-pullback : is-monic f → is-pullback C id f id f
    is-monic→is-pullback mono .square = refl
    is-monic→is-pullback mono .universal {p₁' = p₁'} p = p₁'
    is-monic→is-pullback mono .p₁∘universal = idl _
    is-monic→is-pullback mono .p₂∘universal {p = p} = idl _ ∙ mono _ _ p
    is-monic→is-pullback mono .unique p q = sym p ∙ eliml refl

    is-pullback→is-monic : is-pullback C id f id f → is-monic f
    is-pullback→is-monic pb f g p = sym (pb .p₁∘universal {p = p}) ∙ pb .p₂∘universal
```

Pullbacks additionally preserve monomorphisms, as shown below:

```agda
  abstract
    is-monic→pullback-is-monic
      : ∀ {x y z} {f : Hom x z} {g : Hom y z} {p} {p1 : Hom p x} {p2 : Hom p y}
      → is-monic f
      → is-pullback C p1 f p2 g
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

A similar result holds for isomorphisms.

```agda
  is-invertible→pullback-is-invertible
    : ∀ {x y z} {f : Hom x z} {g : Hom y z} {p} {p1 : Hom p x} {p2 : Hom p y}
    → is-invertible f
    → is-pullback C p1 f p2 g
    → is-invertible p2
  is-invertible→pullback-is-invertible {f = f} {g} {p1 = p1} {p2} f-inv pb =
    make-invertible
      (pb.universal {p₁' = f.inv ∘ g} {p₂' = id} (cancell f.invl ∙ sym (idr _)))
      pb.p₂∘universal
      (pb.unique₂ {p = pulll (cancell f.invl)}
        (pulll pb.p₁∘universal)
        (cancell pb.p₂∘universal)
        (idr _ ∙ introl f.invr ∙ extendr pb.square)
        (idr _))
    where
      module f = is-invertible f-inv
      module pb = is-pullback pb
```


<!--
```agda
  rotate-pullback
    : ∀ {x y z} {f : Hom x z} {g : Hom y z} {p} {p1 : Hom p x} {p2 : Hom p y}
    → is-pullback C p1 f p2 g
    → is-pullback C p2 g p1 f
  rotate-pullback pb .square = sym (pb .square)
  rotate-pullback pb .universal p = pb .universal (sym p)
  rotate-pullback pb .p₁∘universal = pb .p₂∘universal
  rotate-pullback pb .p₂∘universal = pb .p₁∘universal
  rotate-pullback pb .unique p q = pb .unique q p

  invertible≃pullback
    : ∀ {p p' x y z} {f : Hom x z} {g : Hom y z} {p1 : Hom p x} {p2 : Hom p y}
        {p1' : Hom p' x} {p2' : Hom p' y}
    → (pb : is-pullback C p1 f p2 g)
    → (sq : f ∘ p1' ≡ g ∘ p2')
    → is-invertible (pb .universal sq)
    ≃ is-pullback C p1' f p2' g
  invertible≃pullback {f = f} {g} {p1} {p2} {p1'} {p2'} pb sq
    = prop-ext! inv→pb pb→inv
    where
    module _ (inv : is-invertible (pb .universal sq)) where
      module i = is-invertible inv
      open is-pullback
      inv→pb : is-pullback C p1' f p2' g
      inv→pb .square = sq
      inv→pb .universal p = i.inv ∘ pb .universal p
      inv→pb .p₁∘universal = pulll (rswizzle (sym (pb .p₁∘universal)) i.invl) ∙ pb .p₁∘universal
      inv→pb .p₂∘universal = pulll (rswizzle (sym (pb .p₂∘universal)) i.invl) ∙ pb .p₂∘universal
      inv→pb .unique p q =
        lswizzle (pb .unique (pulll (pb .p₁∘universal) ∙ p) (pulll (pb .p₂∘universal) ∙ q)) i.invr
    pb→inv : is-pullback C p1' f p2' g → is-invertible (pb .universal sq)
    pb→inv pb' = make-invertible (pb' .universal (pb .square))
      (unique₂ pb {p = pb .square}
        (pulll (pb .p₁∘universal) ∙ pb' .p₁∘universal)
        (pulll (pb .p₂∘universal) ∙ pb' .p₂∘universal)
        (idr _) (idr _))
      (unique₂ pb' {p = pb' .square}
        (pulll (pb' .p₁∘universal) ∙ pb .p₁∘universal)
        (pulll (pb' .p₂∘universal) ∙ pb .p₂∘universal)
        (idr _) (idr _))

  pullback-unique
    : ∀ {p p' x y z} {f : Hom x z} {g : Hom y z} {p1 : Hom p x} {p2 : Hom p y}
        {p1' : Hom p' x} {p2' : Hom p' y}
    → (pb : is-pullback C p1 f p2 g)
    → (pb' : is-pullback C p1' f p2' g)
    → is-invertible (pb .universal (pb' .square))
  pullback-unique pb pb' =
    Equiv.from (invertible≃pullback pb (pb' .square)) pb'

  is-pullback-iso
    : ∀ {p p' x y z} {f : Hom x z} {g : Hom y z} {p1 : Hom p x} {p2 : Hom p y}
    → (i : p ≅ p')
    → is-pullback C p1 f p2 g
    → is-pullback C (p1 ∘ _≅_.from i) f (p2 ∘ _≅_.from i) g
  is-pullback-iso i pb = Equiv.to
    (invertible≃pullback pb (extendl (pb .square)))
    (subst is-invertible (sym (pb .unique refl refl)) (iso→invertible (i Iso⁻¹)))

  is-pullback-iso'
    : ∀ {p p' x y z} {f : Hom x z} {g : Hom y z} {p1 : Hom p x} {p2 : Hom p y}
        {p1' : Hom p' x} {p2' : Hom p' y}
    → (i : p' ≅ p)
    → (pb : is-pullback C p1 f p2 g)
    → p1 ∘ i .to ≡ p1'
    → p2 ∘ i .to ≡ p2'
    → is-pullback C p1' f p2' g
  is-pullback-iso' i pb com₁ com₂ = subst-is-pullback
    com₁ refl com₂ refl
    (is-pullback-iso (i Iso⁻¹) pb)

  Pullback-unique
    : ∀ {x y z} {f : Hom x z} {g : Hom y z}
    → is-category C
    → is-prop (Pullback C f g)
  Pullback-unique c-cat x y =
    Pullback-path
      apices
      (Univalent.Hom-pathp-refll-iso c-cat (x .p₁∘universal))
      (Univalent.Hom-pathp-refll-iso c-cat (x .p₂∘universal))
    where
      open Pullback
      apices = c-cat .to-path (invertible→iso _ (Equiv.from (invertible≃pullback (y .has-is-pb) (x .square)) (x .has-is-pb)))

  canonically-stable
    : ∀ {ℓ'} (P : ∀ {a b} → Hom a b → Type ℓ')
    → is-category C
    → (pb : ∀ {a b c} (f : Hom a c) (g : Hom b c) → Pullback C f g)
    → ( ∀ {A B X} (f : Hom A B) (g : Hom X B)
      → P f → P (pb g f .Pullback.p₁) )
    → is-pullback-stable C P
  canonically-stable P C-cat pbs stab f g Pf pb =
    transport (λ i → P (Pullback-unique C-cat (pbs g f) pb' i .Pullback.p₁))
      (stab f g Pf)
    where
      pb' : Pullback C _ _
      pb' = record { has-is-pb = pb }
```
-->
