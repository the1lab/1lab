<!--
```agda
open import Cat.Functor.Bifunctor
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Diagram.Pullback
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Bi.Instances.Spans {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
private module C = Cat.Reasoning C
open C
```
-->

# The bicategory of spans

Let $\cC$ be a [precategory]. By a span in $\cC$ (from an object
$A : \cC$ to an object $B : \cC$), we mean a diagram of the form
$A \ot C \to B$. Note that the "apex" of this span, the object $C$, is
part of the data, so that the collection of "spans in $\cC$" will not
be [a set] (unless $\cC$ is [strict]) --- so we can not construct a
category where $\hom(a,b)$ is the collection of spans from $a$ to $b$.

[precategory]: Cat.Base.html
[a set]: 1Lab.HLevel.html#is-set
[strict]: Cat.Instances.StrictCat.html

However, we can make spans in $\cC$ the _objects_ of a category, and
the hom-sets are the maps in $\cC$ between the apices which
"commute with the legs". Diagrammatically, a map between spans is the
dashed line in

~~~{.quiver}
\[\begin{tikzcd}
  & C \\
  A && {B\text{,}} \\
  & {C'}
  \arrow[from=1-2, to=2-1]
  \arrow[from=1-2, to=2-3]
  \arrow[from=3-2, to=2-1]
  \arrow[from=3-2, to=2-3]
  \arrow[dashed, from=1-2, to=3-2]
\end{tikzcd}\]
~~~

where both the left and right triangles must commute.

```agda
record Span (a b : Ob) : Type (o ⊔ ℓ) where
  constructor span
  field
    apex  : Ob
    left  : Hom apex a
    right : Hom apex b

open Span

record Span-hom {a b : Ob} (x y : Span a b) : Type ℓ where
  no-eta-equality
  field
    map   : Hom (x .apex) (y .apex)
    left  : x .left  ≡ y .left ∘ map
    right : x .right ≡ y .right ∘ map
```

<!--
```agda
open Span-hom
unquoteDecl H-Level-Span-hom = declare-record-hlevel 2 H-Level-Span-hom (quote Span-hom)

instance
  Underlying-Span : ∀ {a b} ⦃ _ : Underlying Ob ⦄ → Underlying (Span a b)
  Underlying-Span = record { ⌞_⌟ = λ S → ⌞ S .apex ⌟ }

Span-hom-path
  : {a b : Ob} {x y : Span a b} {f g : Span-hom x y}
  → f .map ≡ g .map → f ≡ g
Span-hom-path p i .map = p i
Span-hom-path {x = x} {y} {f} {g} p i .left j =
  is-set→squarep (λ i j → Hom-set _ _)
    (λ _ → x .left) (λ j → f .left j) (λ j → g .left j) (λ j → y .left ∘ p j) i j
Span-hom-path {x = x} {y} {f} {g} p i .right j =
  is-set→squarep (λ i j → Hom-set _ _)
    (λ _ → x .right) (λ j → f .right j) (λ j → g .right j) (λ j → y .right ∘ p j) i j
```
-->

The category $\Spans_\cC(A, B)$ of spans between $A$ and $B$ admits a
[[faithful functor]] to $\cC$ (projecting the apex and the "middle
map", respectively), so that equality of maps of spans can be compared
at the level of maps in $\cC$.

```agda
Spans : Ob → Ob → Precategory _ _
Spans x y .Precategory.Ob = Span x y
Spans x y .Precategory.Hom = Span-hom
Spans x y .Precategory.Hom-set _ _ = hlevel 2
Spans x y .Precategory.id .map = id
Spans x y .Precategory.id .left = intror refl
Spans x y .Precategory.id .right = intror refl
Spans x y .Precategory._∘_ f g .map = f .map ∘ g .map
Spans x y .Precategory._∘_ f g .left = g .left ∙ pushl (f .left)
Spans x y .Precategory._∘_ f g .right = g .right ∙ pushl (f .right)
Spans x y .Precategory.idr f = Span-hom-path (idr _)
Spans x y .Precategory.idl f = Span-hom-path (idl _)
Spans x y .Precategory.assoc f g h = Span-hom-path (assoc _ _ _)
```

Now suppose that $\cC$ admits pullbacks for arbitrary pairs of maps.
Supposing that we have some spans $S : A \to B$ and $S' : B \to C$, we
can fit them in an M-shaped diagram like

~~~{.quiver}
\[\begin{tikzcd}
  & S && {S'} \\
  A && B && C
  \arrow[from=1-2, to=2-3]
  \arrow[from=1-2, to=2-1]
  \arrow[from=1-4, to=2-3]
  \arrow[from=1-4, to=2-5]
\end{tikzcd}\]
~~~

so that taking the pullback of the diagram $S \to B \ot S'$ gives us an
universal solution to the problem of finding a span $A \ot (S \times_B
S') \to C$. Since pullbacks are _universal_, this composition operation
is functorial, and so extends to a composition operation `Span-∘`{.Agda}:

```agda
module _ (pb : ∀ {a b c} (f : Hom a b) (g : Hom c b) → Pullback C f g) where
  open Make-bifunctor
  open Pullback
  open Functor

  private
    open module Pb {a b c} {f : Hom a b} {g : Hom c b} = Pullback (pb f g) renaming (p₁∘universal to β₁ ; p₂∘universal to β₂) using ()

  Span-∘ : ∀ {a b c} → Bifunctor (Spans b c) (Spans a b) (Spans a c)
  Span-∘ {a} {b} {c} = make-bifunctor mk where
    mk : Make-bifunctor {C = Spans b c} {Spans a b} {Spans a c}
    mk .F₀ sp1 sp2 = span pb.apex (sp2 .left ∘ pb.p₂) (sp1 .right ∘ pb.p₁)
      where module pb = Pullback (pb (sp1 .left) (sp2 .right))
    mk .lmap {x1} {x2} {a} f = res where
      module x = Pullback (pb (x1 .left) (a .right))
      module y = Pullback (pb (x2 .left) (a .right))

      res : Span-hom _ _
      res .map   = y.universal {p₁' = f .map ∘ x.p₁} {x.p₂} p where abstract
        p : x2 .left ∘ f .map ∘ x.p₁ ≡ a .right ∘ x.p₂
        p = pulll (sym (f .left)) ∙ x.square
      res .left  = sym (pullr y.p₂∘universal)
      res .right = sym (pullr y.p₁∘universal ∙ pulll (sym (f .right)))
    mk .rmap {x1} {x2} {a} f = res where
      module x = Pullback (pb (a .left) (x1 .right))
      module y = Pullback (pb (a .left) (x2 .right))

      res : Span-hom _ _
      res .map   = y.universal {p₁' = x.p₁} {p₂' = f .map ∘ x.p₂} p where abstract
        p : a .left ∘ x.p₁ ≡ x2 .right ∘ f .map ∘ x.p₂
        p = sym (pulll (sym (f .right)) ∙ sym (x.square))
      res .left  = sym (pullr y.p₂∘universal ∙ pulll (sym (f .left)))
      res .right = sym (pullr y.p₁∘universal)
    mk .lmap-id = Span-hom-path (sym (pb _ _ .unique id-comm (idr _)))
    mk .rmap-id = Span-hom-path (sym (pb _ _ .unique (idr _) id-comm))
    mk .lmap-∘ f g = Span-hom-path $ sym $ pb _ _ .unique
      (pulll β₁ ∙ extendr β₁)
      (pulll β₂ ∙ β₂)
    mk .rmap-∘ f g = Span-hom-path $ sym $ pb _ _ .unique
      (pulll β₁ ∙ β₁)
      (pulll β₂ ∙ extendr β₂)
    mk .lrmap f g = Span-hom-path $ unique₂ (pb _ _)
      {p = pulll (sym (f .left)) ∙∙ pb _ _ .square ∙∙ pushl (g .right)}
      (pulll (pb _ _.p₁∘universal) ∙ pullr β₁)
      (pulll (pb _ _.p₂∘universal) ∙ β₂)
      (pulll β₁ ∙ β₁)
      (pulll β₂ ∙ pullr β₂)
```

What we'll show in the rest of this module is that `Span-∘`{.Agda} lets
us make `Spans`{.Agda} into the categories of 1-cells of a
_prebicategory_, the **(pre)bicategory of spans** (of $\cC$),
$\Spans(\cC)$. As mentioned before, this prebicategory has (a priori) no
upper bound on the h-levels of its 1-cells, so it is not locally strict.
We remark that when $\cC$ is univalent, then $\Spans(\cC)$ is locally
so, and when $\cC$ is gaunt, then $\Spans(\cC)$ is strict.

Since the details of the full construction are _grueling_, we will
present only an overview of the unitors and the associator. For the left
unitor, observe that the composition $\id \circ S$ is implemented by
a pullback diagram like

~~~{.quiver}
\[\begin{tikzcd}
  && {A \times_A S} && {A \times_A S} \\
  & A && S \\
  A && A && {B\text{,}}
  \arrow["{p_1}"', from=1-3, to=2-2]
  \arrow["{p_2}", from=1-3, to=2-4]
  \arrow["f"', from=2-4, to=3-3]
  \arrow["{\mathrm{id}}", from=2-2, to=3-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125, rotate=-45}, draw=none, from=1-3, to=3-3]
  \arrow["{\mathrm{id}}"', from=2-2, to=3-1]
  \arrow["g", from=2-4, to=3-5]
  \arrow["{\exists!}"', dashed, from=2-4, to=1-5]
  \arrow["{\mathrm{id}}"{description}, from=1-3, to=1-5]
\end{tikzcd}\]
~~~

but observe that the maps $S \xto{f} A$ and $S \xto{\id} S$ also
form a cone over the cospan $A \to A \xot{f} S$, so that there is a
unique map filling the dashed line in the diagram above such that
everything commutes: hence there is an invertible 2-cell $\id \circ
S \To S$. The right unitor is analogous.

```agda
  open Prebicategory
  open Pullback

  private
    _¤_ : ∀ {a b c} (x : Span b c) (y : Span a b) → Span a c
    f ¤ g = Span-∘ · f · g

    sλ← : ∀ {A B} (x : Span A B) → Span-hom x (span _ C.id C.id ¤ x)
    sλ← x .map   = pb _ _ .universal id-comm-sym
    sλ← x .left  = sym $ pullr β₂ ∙ idr _
    sλ← x .right = sym $ pullr β₁ ∙ idl _

    sρ← : ∀ {A B} (x : Span A B) → Span-hom x (x ¤ span _ C.id C.id)
    sρ← x .map   = pb _ _ .universal id-comm
    sρ← x .left  = sym $ pullr β₂ ∙ idl _
    sρ← x .right = sym $ pullr β₁ ∙ idr _
```

For the associator, while doing the construction in elementary terms is
quite complicated, we observe that, diagrammatically, the composite of
three morphisms fits into a diagram like

~~~{.quiver}
\[\begin{tikzcd}
  && {S\times_BS'} && {S'\times_CS''} \\
  & S && {S'} && {S''} \\
  A && B && C && D
  \arrow["f", from=2-2, to=3-1]
  \arrow["g"', from=2-2, to=3-3]
  \arrow["h", from=2-4, to=3-3]
  \arrow["i"', from=2-4, to=3-5]
  \arrow["j", from=2-6, to=3-5]
  \arrow["k"', from=2-6, to=3-7]
  \arrow[from=1-3, to=2-2]
  \arrow[from=1-3, to=2-4]
  \arrow[from=1-5, to=2-4]
  \arrow[from=1-5, to=2-6]
  \arrow["\lrcorner"{anchor=center, pos=0.125, rotate=-45}, draw=none, from=1-3, to=3-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125, rotate=-45}, draw=none, from=1-5, to=3-5]
\end{tikzcd}\]
~~~

so that, at a high level, there is no confusion as to which composite is
meant. From then, it's just a matter of proving pullbacks are
associative (in a standard, but annoying, way), and showing that these
canonically-obtained isomorphisms (are natural in all the possible
variables and) satisfy the triangle and pentagon identities.

<details>
<summary>On second thought, let's not read that. T'is a silly theorem.</summary>

```agda
    sα← : ∀ {A B C D} ((f , g , h) : Span C D × Span B C × Span A B)
        → Span-hom ((f ¤ g) ¤ h) (f ¤ (g ¤ h))
    sα← (f , g , h) .map = pb _ _ .universal resp' where
      abstract
        resp : g .left C.∘ pb (f .left) (g .right) .p₂
           C.∘ pb ((f ¤ g) .left) (h .right) .p₁
             ≡ h .right C.∘ pb ((f ¤ g) .left) (h .right) .p₂
        resp = assoc _ _ _ ∙ pb _ _ .square

      shuffle = pb _ _ .universal {p₁' = pb _ _ .p₂ C.∘ pb _ _ .p₁} {p₂' = pb _ _ .p₂} resp

      abstract
        resp' : f .left C.∘ pb (f .left) (g .right) .p₁
            C.∘ pb ((f ¤ g) .left) (h .right) .p₁
              ≡ (g ¤ h) .right C.∘ shuffle
        resp' = sym $ pullr β₁ ∙ extendl (sym (pb _ _ .square))

    sα← (f , g , h) .left = sym $ pullr β₂ ∙ pullr β₂
    sα← (f , g , h) .right = sym $ pullr β₁ ∙ assoc _ _ _

    sα→ : ∀ {A B C D} ((f , g , h) : Span C D × Span B C × Span A B)
        → Span-hom (f ¤ (g ¤ h)) ((f ¤ g) ¤ h)
    sα→ (f , g , h) .map = pb _ _ .universal resp' where
      abstract
        resp : f .left C.∘ pb (f .left) ((g ¤ h) .right) .p₁
             ≡ g .right C.∘ pb (g .left) (h .right) .p₁
           C.∘ pb (f .left) ((g ¤ h) .right) .p₂
        resp = pb _ _ .square ∙ sym (assoc _ _ _)

      shuffle = pb _ _ .universal {p₁' = pb _ _ .p₁} {p₂' = pb _ _ .p₁ C.∘ pb _ _ .p₂} resp

      abstract
        resp' : (f ¤ g) .left C.∘ shuffle
              ≡ h .right C.∘ pb (g .left) (h .right) .p₂
            C.∘ pb (f .left) ((g ¤ h) .right) .p₂
        resp' = pullr β₂ ∙ extendl (pb _ _ .square)

    sα→ (f , g , h) .left = sym $ pullr β₂ ∙ assoc _ _ _
    sα→ (f , g , h) .right = sym $ pullr β₁ ∙ pullr β₁

  open make-natural-iso
  Spanᵇ : Prebicategory _ _ _
  Spanᵇ .Ob = C.Ob
  Spanᵇ .Hom = Spans
  Spanᵇ .id = span _ C.id C.id
  Spanᵇ .compose = Span-∘
  Spanᵇ .unitor-l = to-natural-iso ni where
    ni : make-natural-iso (Id {C = Spans _ _}) _
    ni .eta = sλ←
    ni .inv x .map = pb _ _ .p₂
    ni .inv x .left = refl
    ni .inv x .right = pb _ _ .square
    ni .eta∘inv x = Span-hom-path (Pullback.unique₂ (pb _ _) {p = idl _ ∙ ap₂ C._∘_ refl (introl refl)}
      (pulll β₁)
      (pulll β₂)
      (id-comm ∙ pb _ _ .square)
      id-comm)
    ni .inv∘eta x = Span-hom-path β₂
    ni .natural x y f = Span-hom-path $ Pullback.unique₂ (pb _ _) {p = idl _ ∙ f .right}
      (pulll β₁ ∙ β₁)
      (pulll β₂ ∙ pullr β₂ ∙ idr _)
      (pulll β₁ ∙ sym (f .right))
      (pulll β₂ ∙ idl _)
  Spanᵇ .unitor-r = to-natural-iso ni where
    ni : make-natural-iso (Id {C = Spans _ _}) _
    ni .eta = sρ←
    ni .inv _ .map = pb _ _ .p₁
    ni .inv _ .left = sym (pb _ _ .square)
    ni .inv _ .right = refl
    ni .eta∘inv x = Span-hom-path (Pullback.unique₂ (pb _ _) {p = introl refl}
      (pulll β₁ ∙ idl _)
      (pulll β₂)
      (idr _)
      (id-comm ∙ sym (pb _ _ .square)))
    ni .inv∘eta x = Span-hom-path β₁
    ni .natural x y f = Span-hom-path $ Pullback.unique₂ (pb _ _) {p = sym (f .left) ∙ introl refl}
      (pulll β₁ ∙ pullr β₁ ∙ idr _)
      (pulll β₂ ∙ β₂)
      (pulll β₁ ∙ idl _)
      (pulll β₂ ∙ sym (f .left))
  Spanᵇ .associator = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .eta = sα←
    ni .inv = sα→
    ni .eta∘inv x = Span-hom-path $
      Pullback.unique₂ (pb _ _) {p = pb _ _ .square}
      (pulll β₁ ∙ pullr β₁ ∙ β₁)
      (pulll β₂ ∙ unique₂ (pb _ _) {p = extendl (pb _ _ .square)}
          (pulll β₁ ∙ pullr β₁ ∙ β₂)
          (pulll β₂ ∙ β₂)
          refl refl)
      (idr _)
      (idr _)
    ni .inv∘eta x = Span-hom-path $
      Pullback.unique₂ (pb _ _) {p = pb _ _ .square}
      (pulll β₁ ∙ unique₂ (pb _ _) {p = extendl (pb _ _ .square)}
        (pulll β₁ ∙ β₁)
        (pulll β₂ ∙ pullr β₂ ∙ β₁)
        refl refl)
      (pulll β₂ ∙ pullr β₂ ∙ β₂)
      (idr _)
      (idr _)
    ni .natural x y f = Span-hom-path $ Pullback.unique₂ (pb _ _)
      {p = sym (pullr (pulll (pulll β₁) ∙∙ pullr3 (pulll β₁) ∙∙ ap₂ C._∘_ refl β₁)
             ∙∙ pulll (sym (f .snd .fst .right))
             ∙∙ extendl (sym (pb _ _ .square)) ∙ pushl (f .fst .left))}
      (pulll (pulll β₁ ∙ pullr β₁) ∙ pullr β₁)
      (pulll (pulll β₂ ∙ β₂) ∙ pullr β₂)
      (pulll β₁ ∙ pullr (pulll β₁ ∙ pullr β₁) ∙ pulll (pulll β₁ ∙ pullr β₁) ∙ pullr refl)
      (pulll β₂ ∙ Pullback.unique₂ (pb _ _)
        {p = pulll (sym (f .snd .fst .left)) ∙ pulll refl ∙ pb _ _ .square ∙ pushl (f .snd .snd .right)}
        (pulll β₁ ∙ pullr (pulll β₁ ∙ pullr β₁) ∙ pulll (pulll β₂ ∙ β₂) ∙ pullr refl)
        (pulll β₂ ∙ pulll β₂ ∙ β₂)
        (pulll (pulll β₁ ∙ pullr β₁) ∙ pullr β₁)
        (pulll (pulll β₂ ∙ β₂) ∙ pullr β₂))
  Spanᵇ .triangle f g = Span-hom-path $ pb _ _ .unique
    (pulll β₁ ∙ pullr β₁ ∙ β₁)
    (pulll β₂ ∙ β₂)
  Spanᵇ .pentagon f g h i = Span-hom-path $ unique₂ (pb _ _)
    {p = pullr (pulll β₂ ∙ extendr (pulll β₂) ∙ extendr (pullr β₂) ∙ extendl (pullr β₁)) ∙ ap₂ C._∘_ refl (extendl β₂) ∙ extendl (pb _ _ .square)}
    (pulll β₁ ∙ pullr (pulll β₁))
    (pulll β₂ ∙ pulll β₂ ∙ pullr β₂ ∙ extendl β₂)
    (pulll β₁ ∙ unique₂ (pb _ _)
      {p = pullr β₂ ∙ extendl (pb _ _ .square) ∙ pullr refl}
      (pulll β₁ ∙ β₁)
      (pulll β₂ ∙ pullr β₂)
      (pulll β₁ ∙ pb _ _ .unique (pulll β₁ ∙ pulll β₁ ∙ β₁) (pulll β₂ ∙ pullr (pulll β₂ ∙ pullr β₂) ∙ ap₂ C._∘_ refl (pulll β₁) ∙ pulll β₁))
      (pulll β₂ ∙ pullr (pulll β₂ ∙ pullr β₂ ∙ pulll β₁) ∙ extendl β₂))
    (pulll β₂ ∙ pullr β₂)
```
</details>
