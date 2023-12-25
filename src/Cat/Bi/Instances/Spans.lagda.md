<!--
```agda
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
$A \ot C \to B$. Note that the "vertex" of this span, the object $C$, is
part of the data, so that the collection of "spans in $\cC$" will not
be [a set] (unless $\cC$ is [strict]) --- so we can not construct a
category where $\hom(a,b)$ is the collection of spans from $a$ to $b$.

[precategory]: Cat.Base.html
[a set]: 1Lab.HLevel.html#is-set
[strict]: Cat.Instances.StrictCat.html

However, we can make spans in $\cC$ the _objects_ of a category, and
the hom-sets are the maps in $\cC$ between the vertices which
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
private unquoteDecl eqv = declare-record-iso eqv (quote Span-hom)

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
[[faithful functor]] to $\cC$ (projecting the vertex and the "middle
map", respectively), so that equality of maps of spans can be compared
at the level of maps in $\cC$.

```agda
Spans : Ob → Ob → Precategory _ _
Spans x y .Precategory.Ob = Span x y
Spans x y .Precategory.Hom = Span-hom
Spans x y .Precategory.Hom-set _ _ = Iso→is-hlevel 2 eqv (hlevel 2)
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
  open Functor

  Span-∘ : ∀ {a b c} → Functor (Spans b c ×ᶜ Spans a b) (Spans a c)
  Span-∘ .F₀ (sp1 , sp2) =
    span pb.apex (sp2 .left ∘ pb.p₂) (sp1 .right ∘ pb.p₁)
    where module pb = Pullback (pb (sp1 .left) (sp2 .right))

  Span-∘ .F₁ {x1 , x2} {y1 , y2} (f , g) = res
    where
      module x = Pullback (pb (x1 .left) (x2 .right))
      module y = Pullback (pb (y1 .left) (y2 .right))

      x→y : Hom x.apex y.apex
      x→y = y.universal {p₁' = f .map ∘ x.p₁} {p₂' = g .map ∘ x.p₂} comm
        where abstract
          open Pullback
          comm : y1 .left ∘ f .map ∘ x.p₁ ≡ y2 .right ∘ g .map ∘ x.p₂
          comm = pulll (sym (f .left)) ∙ x.square ∙ pushl (g .right)

      res : Span-hom _ _
      res .map = x→y
      res .left = sym (pullr y.p₂∘universal ∙ pulll (sym (g .left)))
      res .right = sym (pullr y.p₁∘universal ∙ pulll (sym (f .right)))

  Span-∘ .F-id {x1 , x2} = Span-hom-path $ sym $ x.unique id-comm id-comm
    where module x = Pullback (pb (x1 .left) (x2 .right))

  Span-∘ .F-∘ {x1 , x2} {y1 , y2} {z1 , z2} f g =
    Span-hom-path $ sym $ z.unique
      (pulll z.p₁∘universal ∙ pullr y.p₁∘universal ∙ assoc _ _ _)
      (pulll z.p₂∘universal ∙ pullr y.p₂∘universal ∙ assoc _ _ _)
    where
      module x = Pullback (pb (x1 .left) (x2 .right))
      module y = Pullback (pb (y1 .left) (y2 .right))
      module z = Pullback (pb (z1 .left) (z2 .right))
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
    f ¤ g = Span-∘ .F₀ (f , g)

    sλ← : ∀ {A B} (x : Span A B) → Span-hom x (span _ C.id C.id ¤ x)
    sλ← x .map   = pb _ _ .universal id-comm-sym
    sλ← x .left  = sym $ pullr (pb _ _ .p₂∘universal) ∙ idr _
    sλ← x .right = sym $ pullr (pb _ _ .p₁∘universal) ∙ idl _

    sρ← : ∀ {A B} (x : Span A B) → Span-hom x (x ¤ span _ C.id C.id)
    sρ← x .map   = pb _ _ .universal id-comm
    sρ← x .left  = sym $ pullr (pb _ _ .p₂∘universal) ∙ idl _
    sρ← x .right = sym $ pullr (pb _ _ .p₁∘universal) ∙ idr _
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
        resp' = sym $ pullr (pb _ _ .p₁∘universal) ∙ extendl (sym (pb _ _ .square))

    sα← (f , g , h) .left = sym $ pullr (pb _ _ .p₂∘universal) ∙ pullr (pb _ _ .p₂∘universal)
    sα← (f , g , h) .right = sym $ pullr (pb _ _ .p₁∘universal) ∙ assoc _ _ _

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
        resp' = pullr (pb _ _ .p₂∘universal) ∙ extendl (pb _ _ .square)

    sα→ (f , g , h) .left = sym $ pullr (pb _ _ .p₂∘universal) ∙ assoc _ _ _
    sα→ (f , g , h) .right = sym $ pullr (pb _ _ .p₁∘universal) ∙ pullr (pb _ _ .p₁∘universal)

  open make-natural-iso
  {-# TERMINATING #-}
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
      (pulll (pb _ _ .p₁∘universal))
      (pulll (pb _ _ .p₂∘universal))
      (id-comm ∙ pb _ _ .square)
      id-comm)
    ni .inv∘eta x = Span-hom-path (pb _ _ .p₂∘universal)
    ni .natural x y f = Span-hom-path $
      Pullback.unique₂ (pb _ _) {p = idl _ ∙ f .right}
        (pulll (pb _ _ .p₁∘universal) ∙ pullr (pb _ _ .p₁∘universal) ∙ idl _)
        (pulll (pb _ _ .p₂∘universal) ∙ pullr (pb _ _ .p₂∘universal) ∙ idr _)
        (pulll (pb _ _ .p₁∘universal) ∙ sym (f .right))
        (pulll (pb _ _ .p₂∘universal) ∙ idl _)
  Spanᵇ .unitor-r = to-natural-iso ni where
    ni : make-natural-iso (Id {C = Spans _ _}) _
    ni .eta = sρ←
    ni .inv _ .map = pb _ _ .p₁
    ni .inv _ .left = sym (pb _ _ .square)
    ni .inv _ .right = refl
    ni .eta∘inv x = Span-hom-path (Pullback.unique₂ (pb _ _) {p = introl refl}
      (pulll (pb _ _ .p₁∘universal) ∙ idl _)
      (pulll (pb _ _ .p₂∘universal))
      (idr _)
      (id-comm ∙ sym (pb _ _ .square)))
    ni .inv∘eta x = Span-hom-path (pb _ _ .p₁∘universal)
    ni .natural x y f = Span-hom-path $
      Pullback.unique₂ (pb _ _) {p = sym (f .left) ∙ introl refl}
        (pulll (pb _ _ .p₁∘universal) ∙ pullr (pb _ _ .p₁∘universal) ∙ idr _)
        (pulll (pb _ _ .p₂∘universal) ∙ pullr (pb _ _ .p₂∘universal) ∙ idl _)
        (pulll (pb _ _ .p₁∘universal) ∙ idl _)
        (pulll (pb _ _ .p₂∘universal) ∙ sym (f .left))
  Spanᵇ .associator = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .eta = sα←
    ni .inv = sα→
    ni .eta∘inv x = Span-hom-path $
      Pullback.unique₂ (pb _ _) {p = pb _ _ .square}
      (pulll (pb _ _ .p₁∘universal) ∙ pullr (pb _ _ .p₁∘universal) ∙ pb _ _ .p₁∘universal)
      (pulll (pb _ _ .p₂∘universal) ∙ unique₂ (pb _ _) {p = extendl (pb _ _ .square)}
          (pulll (pb _ _ .p₁∘universal) ∙ pullr (pb _ _ .p₁∘universal) ∙ pb _ _ .p₂∘universal)
          (pulll (pb _ _ .p₂∘universal) ∙ pb _ _ .p₂∘universal)
          refl refl)
      (idr _)
      (idr _)
    ni .inv∘eta x = Span-hom-path $
      Pullback.unique₂ (pb _ _) {p = pb _ _ .square}
      (pulll (pb _ _ .p₁∘universal) ∙ unique₂ (pb _ _) {p = extendl (pb _ _ .square)}
        (pulll (pb _ _ .p₁∘universal) ∙ pb _ _ .p₁∘universal)
        (pulll (pb _ _ .p₂∘universal) ∙ pullr (pb _ _ .p₂∘universal) ∙ pb _ _ .p₁∘universal)
        refl refl)
      (pulll (pb _ _ .p₂∘universal) ∙ pullr (pb _ _ .p₂∘universal) ∙ pb _ _ .p₂∘universal)
      (idr _)
      (idr _)
    ni .natural x y f = Span-hom-path $ Pullback.unique₂ (pb _ _)
      {p₁' = f .fst .map C.∘ pb _ _ .p₁ C.∘ pb _ _ .p₁}
      {p₂' = pb _ _ .universal
        {p₁' = f .snd .fst .map C.∘ pb _ _ .p₂ C.∘ pb _ _ .p₁}
        {p₂' = f .snd .snd .map C.∘ pb _ _ .p₂}
        (pulll (sym (f .snd .fst .left)) ∙ assoc _ _ _ ∙ pb _ _ .square ∙ pushl (f .snd .snd .right))}
      {p = sym $ pullr (pb _ _ .p₁∘universal) ∙ pulll (sym (f .snd .fst .right)) ∙ extendl (sym (pb _ _ .square)) ∙ pushl (f .fst .left)}
      (pulll (pb _ _ .p₁∘universal) ∙ pullr (pb _ _ .p₁∘universal))
      (pulll (pb _ _ .p₂∘universal) ∙ pb _ _ .unique
        (pulll (extendl (pb _ _ .p₁∘universal)) ∙ pullr (pullr (pb _ _ .p₂∘universal)) ∙ ap₂ C._∘_ refl (pb _ _ .p₁∘universal))
        (pulll (extendl (pb _ _ .p₂∘universal)) ∙ pullr (pullr (pb _ _ .p₂∘universal)) ∙ ap₂ C._∘_ refl (pb _ _ .p₂∘universal)))
      (pulll (pb _ _ .p₁∘universal) ∙ pullr (pb _ _ .p₁∘universal) ∙ pulll (pb _ _ .p₁∘universal) ∙ sym (assoc _ _ _))
      (pulll (pb _ _ .p₂∘universal) ∙ pb _ _ .unique
        (pulll (pb _ _ .p₁∘universal) ∙ pullr (pb _ _ .p₁∘universal) ∙ extendl (pb _ _ .p₂∘universal))
        (pulll (pb _ _ .p₂∘universal) ∙ pb _ _ .p₂∘universal))
  Spanᵇ .triangle f g = Span-hom-path $
    pb _ _ .unique
      (pulll (pb _ _ .p₁∘universal) ∙ pullr (pb _ _ .p₁∘universal) ∙ pb _ _ .p₁∘universal ∙ introl refl)
      (pulll (pb _ _ .p₂∘universal) ∙ pullr (pb _ _ .p₂∘universal) ∙ eliml refl)
  Spanᵇ .pentagon f g h i = Span-hom-path $
    Pullback.unique₂ (pb _ _)
      {p = pullr (pulll (pb _ _ .p₂∘universal) ∙ pullr (pulll (pb _ _ .p₂∘universal) ∙ pullr (pb _ _ .p₂∘universal)) ∙ ap₂ C._∘_ refl (pulll (pb _ _ .p₁∘universal)))
         ∙ ap₂ C._∘_ refl (extendl (pb _ _ .p₂∘universal)) ∙ sym (ap₂ C._∘_ refl (idl _ ∙ extendl (pb _ _ .p₂∘universal)) ∙ extendl (sym (pb _ _ .square)))}
      (pulll (pb _ _ .p₁∘universal) ∙ pullr (pulll (pb _ _ .p₁∘universal)))
      (pulll (pb _ _ .p₂∘universal) ∙ pullr (pulll (pb _ _ .p₂∘universal) ∙ pullr (pb _ _ .p₂∘universal)))
      (pulll (pb _ _ .p₁∘universal)
      ∙ Pullback.unique₂ (pb _ _) {p = pullr (pb _ _ .p₂∘universal) ∙ extendl (pb _ _ .square) ∙ sym (assoc _ _ _)}
          (pulll (pb _ _ .p₁∘universal) ∙ pb _ _ .p₁∘universal)
          (pulll (pb _ _ .p₂∘universal) ∙ pullr (pb _ _ .p₂∘universal))
          (pulll (pb _ _ .p₁∘universal) ∙ pb _ _ .unique
            (pulll (pb _ _ .p₁∘universal) ∙ pulll (pb _ _ .p₁∘universal) ∙ pb _ _ .p₁∘universal ∙ idl _)
            (pulll (pb _ _ .p₂∘universal) ∙ pulll (pullr (pb _ _ .p₂∘universal)) ∙ pullr (pullr (pb _ _ .p₂∘universal) ∙ pulll (pb _ _ .p₁∘universal)) ∙ pulll (pb _ _ .p₁∘universal)))
          (pulll (pb _ _ .p₂∘universal) ∙ pullr (pulll (pb _ _ .p₂∘universal) ∙ pullr (pb _ _ .p₂∘universal))
          ∙ ap₂ C._∘_ refl (pulll (pb _ _ .p₁∘universal)) ∙ pulll (pb _ _ .p₂∘universal) ∙ sym (assoc _ _ _)))
      ( pulll (pb _ _ .p₂∘universal)
      ·· pullr (pb _ _ .p₂∘universal)
      ·· sym (idl _ ·· pulll (pb _ _ .p₂∘universal) ·· sym (assoc _ _ _)))
```
</details>
