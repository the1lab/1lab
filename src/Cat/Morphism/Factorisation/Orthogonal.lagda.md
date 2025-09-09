<!--
```agda
open import Cat.Morphism.Factorisation
open import Cat.Morphism.Orthogonal
open import Cat.Morphism.Class
open import Cat.Morphism.Lifts
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Morphism.Factorisation.Orthogonal where
```

# Orthogonal factorisation systems {defines="orthogonal-factorisation-system"}

<!--
```agda
module _
  {o ℓ ℓl ℓr}
  (C : Precategory o ℓ)
  (L : Arrows C ℓl)
  (R : Arrows C ℓr) where
  private module C = Cat.Reasoning C
  open Factorisation
```
-->

Suppose you have some category $\cC$ and you, inspired by the wisdom
of King Solomon, want to chop every morphism in half. An **orthogonal factorisation
system** $(L, R)$ on $\cC$ will provide a tool for doing so, in a
particularly coherent way. Here, $L$ and $R$ are predicates on the space
of morphisms of $C$. First, we package the data of an [[$(L, R)$-factorisation|factorisation]]
of a morphism $f : a \to b$.

```agda
  record is-ofs : Type (o ⊔ ℓ ⊔ ℓl ⊔ ℓr) where
    field
      factor : ∀ {a b} (f : C.Hom a b) → Factorisation C L R f
```

In addition to mandating that every map $f : a \to b$ factors as a map
$f : a \xto{l} m(f) \xto{r} b$ where $l \in L$ and $r \in R$, the classes
must satisfy the following properties:

- Every isomorphism is in both $L$ and in $R$^[We'll see, in a bit, that
the converse is true, too.].

- Both classes are stable under composition: if $f \in L$ and $g \in L$,
then $(g \circ f) \in L$, and likewise for $R$.

```agda
      is-iso→in-L : ∀ {a b} (f : C.Hom a b) → C.is-invertible f → f ∈ L
      L-is-stable
        : ∀ {a b c} (f : C.Hom b c) (g : C.Hom a b) → f ∈ L → g ∈ L
        → (f C.∘ g) ∈ L

      is-iso→in-R : ∀ {a b} (f : C.Hom a b) → C.is-invertible f → f ∈ R
      R-is-stable
        : ∀ {a b c} (f : C.Hom b c) (g : C.Hom a b) → f ∈ R → g ∈ R
        → (f C.∘ g) ∈ R
```

Most importantly, the class $L$ is [[orthogonal|orthogonality]] to $R$, i.e:
for every $l \in L$ and $r \in R$, we have $l \ortho r$.[^ortho]

[^ortho]: As we shall shortly see, $L$ is actually *exactly* the class of
morphisms that is left orthogonal to $R$ and vice-versa for $R$.

```agda
      L⊥R : Orthogonal C L R
```

The canonical example of an orthogonal factorisation system is the
([[surjective|surjections-between-sets]], [[injective|embedding]])
factorisation system on the [[category of sets]], which uniquely factors
a function $f : A \to B$ through the image of $f$.[^regular]

[^regular]: This factorisation system is a special case of the
([[strong epimorphism]], [[monomorphism]]) orthogonal factorisation
system on a [[regular category]].

<!--
```agda
module _
  {o ℓ ℓl ℓr}
  (C : Precategory o ℓ)
  (L : Arrows C ℓl)
  (R : Arrows C ℓr)
  (fs : is-ofs C L R)
  where

  private module C = Cat.Reasoning C
  open is-ofs fs
  open Factorisation
```
-->

The first thing we observe is that factorisations for a morphism are
unique. Working in precategorical generality, we weaken this to
essential uniqueness: Given two factorisations of $f$ we exhibit an
isomorphism between their replacements $m(f)$, $m'(f)$ which commutes
with both the `left`{.Agda} morphism and the `right`{.Agda}
morphism. We reproduce the proof from [@Borceux:vol1, §5.5].

```agda
  factorisation-essentially-unique
    : ∀ {a b} (f : C.Hom a b) (fa1 fa2 : Factorisation C L R f)
    → Σ[ f ∈ fa1 .mid C.≅ fa2 .mid ]
        ( (f .C.to C.∘ fa1 .left ≡ fa2 .left)
        × (fa1 .right C.∘ f .C.from ≡ fa2 .right))
  factorisation-essentially-unique f fa1 fa2 =
    C.make-iso (upq .fst) (vp'q' .fst) vu=id uv=id , upq .snd .fst , vp'q' .snd .snd
    where
```

Suppose that $f = r \circ l$ and $f = r' \circ l'$ are both
$(L,R)$-factorisations of $f$. We use the fact that $l \ortho r'$ and
$l' \ortho r$ to get maps $u, v$ satisfying $ur = r'$, $r'u = r$, $vl =
l'$, and $l'v = l$.

```agda
      upq =
        L⊥R _ (fa1 .left∈L) _ (fa2 .right∈R) _ _
          (sym (fa1 .factors) ∙ fa2 .factors) .centre

      vp'q' = L⊥R _ (fa2 .left∈L) _ (fa1 .right∈R) _ _
        (sym (fa2 .factors) ∙ fa1 .factors) .centre
```

To show that $u$ and $v$ are inverses, fit first $l$ and $r$ into a
lifting diagram like the one below. Since $l \ortho r$, we have that the
space of diagonals $m(f) \to m(f)$ is contractible, hence a proposition,
and since both $vu$ and the identity are in that diagonal, $uv =
\id$.

~~~{.quiver}
\begin{tikzcd}
  a && {m(f)} \\
  \\
  {m(f)} && b
  \arrow["l", from=1-1, to=1-3]
  \arrow["l"', from=1-1, to=3-1]
  \arrow["r", from=1-3, to=3-3]
  \arrow["\id", shift left=2, from=3-1, to=1-3]
  \arrow["vu"', shift right=2, from=3-1, to=1-3]
  \arrow["r"', from=3-1, to=3-3]
\end{tikzcd}
~~~

```agda
      vu=id : upq .fst C.∘ vp'q' .fst ≡ C.id
      vu=id = ap fst $ is-contr→is-prop
        (L⊥R _ (fa2 .left∈L) _ (fa2 .right∈R) _ _ refl)
        ( upq .fst C.∘ vp'q' .fst
        , C.pullr (vp'q' .snd .fst) ∙ upq .snd .fst
        , C.pulll (upq .snd .snd) ∙ vp'q' .snd .snd
        ) (C.id , C.idl _ , C.idr _)
```

A dual argument works by making a lifting square with $l'$ and $r'$ as
its faces. We omit it for brevity.  By the characterisation of path
spaces in categories, this implies that factorisations of a fixed
morphism are a proposition.

<!--
```agda
      uv=id : vp'q' .fst C.∘ upq .fst ≡ C.id
      uv=id = ap fst $ is-contr→is-prop
        (L⊥R _ (fa1 .left∈L) _ (fa1 .right∈R) _ _ refl)
        ( vp'q' .fst C.∘ upq .fst
        , C.pullr (upq .snd .fst) ∙ vp'q' .snd .fst
        , C.pulll (vp'q' .snd .snd) ∙ upq .snd .snd
        ) (C.id , C.idl _ , C.idr _)
```
-->

```agda
  factorisation-unique
    : ∀ {a b} (f : C.Hom a b) → is-category C → is-prop (Factorisation C L R f)
  factorisation-unique f c-cat x y = go where
    isop1p2 = factorisation-essentially-unique f x y

    p = Univalent.Hom-pathp-reflr-iso c-cat {q = isop1p2 .fst} (isop1p2 .snd .fst)
    q = Univalent.Hom-pathp-refll-iso c-cat {p = isop1p2 .fst} (isop1p2 .snd .snd)

    go : x ≡ y
    go i .mid   = c-cat .to-path (isop1p2 .fst) i
    go i .left  = p i
    go i .right = q i
```

<!--
```agda
    go i .left∈L  = is-prop→pathp (λ i → is-tr (L · (p i))) (x .left∈L) (y .left∈L) i
    go i .right∈R = is-prop→pathp (λ i → is-tr (R · (q i))) (x .right∈R) (y .right∈R) i
    go i .factors =
      is-prop→pathp (λ i → C.Hom-set _ _ f (q i C.∘ p i)) (x .factors) (y .factors) i
```
-->

As a passing observation, note that the intersection $L \cap R$ is
precisely the class of isomorphisms of $f$. Every isomorphism is in both
classes, by the definition, and if a morphism is in both classes, it is
orthogonal to itself, hence an isomorphism.

```agda
  in-intersection→is-iso
    : ∀ {a b} (f : C.Hom a b) → f ∈ L → f ∈ R → C.is-invertible f
  in-intersection→is-iso f f∈L f∈R = self-orthogonal→invertible C f $ L⊥R f f∈L f f∈R

  in-intersection≃is-iso
    : ∀ {a b} (f : C.Hom a b) → C.is-invertible f ≃ (f ∈ L × f ∈ R)
  in-intersection≃is-iso f = prop-ext!
    (λ fi → is-iso→in-L f fi , is-iso→in-R f fi)
    λ { (a , b) → in-intersection→is-iso f a b }
```

The final observation is that the class $L$ is precisely $^\bot R$, the
class of morphisms left-orthogonal to those in $R$. One direction is by
definition, and the other is rather technical. Let's focus on the
technical one.

```agda
  L-is-⊥R
    : ∀ {a b} (f : C.Hom a b)
    → (f ∈ L) ≃ (∀ {c d} (m : C.Hom c d) → m ∈ R → Orthogonal C f m)
  L-is-⊥R f = prop-ext! (λ m f∈L m∈R → to f∈L m m∈R) from where
    to : ∀ {c d} (m : C.Hom c d) → f ∈ L → m ∈ R → Orthogonal C f m
    to m f∈L m∈R u v square = L⊥R f f∈L m m∈R u v square

    from : (∀ {c d} (m : C.Hom c d) → m ∈ R → Orthogonal C f m) → f ∈ L
    from ortho = subst (_∈ L) (sym (fa .factors)) $ L-is-stable _ _ m∈L (fa .left∈L)
      where
```

Suppose that $f$ is left-orthogonal to every $r \in R$, and write out
the $(L,R)$-factorisation $f = r \circ l$. By a syntactic limitation in
Agda, we start with the conclusion: We'll show that $r$ is in $L$, and
since $L$ is closed under composition, so is $f$.  Since $f$ is
orthogonal to $r$, we can fit it into a lifting diagram

~~~{.quiver}
\[\begin{tikzcd}
  a && {m(f)} \\
  \\
  b && b
  \arrow["l", from=1-1, to=1-3]
  \arrow["f"', from=1-1, to=3-1]
  \arrow["r", from=1-3, to=3-3]
  \arrow["g", dashed, from=3-1, to=1-3]
  \arrow["\id"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

and make note of the diagonal filler $g : B \to r(f)$, and that it
satisfies $gf=e$ and $mg = \id$.

```agda
      fa = factor f
      gpq = ortho (fa .right) (fa .right∈R) (fa .left) C.id (C.idl _ ∙ (fa .factors))
```

We'll show $gr = \id$ by fitting it into a lifting diagram. But
since $l \ortho r$, the factorisation is unique, and $gr = \id$, as
needed.

~~~{.quiver}
\[\begin{tikzcd}
  a && {m(f)} \\
  \\
  {m(f)} && b
  \arrow["l", from=1-1, to=1-3]
  \arrow["l"', from=1-1, to=3-1]
  \arrow["r", from=1-3, to=3-3]
  \arrow["gr", shift left=2, from=3-1, to=1-3]
  \arrow["\id"', shift right=2, from=3-1, to=1-3]
  \arrow["r"', from=3-1, to=3-3]
\end{tikzcd} \]
~~~

```agda
      gm=id : gpq .centre .fst C.∘ (fa .right) ≡ C.id
      gm=id = ap fst $ is-contr→is-prop
        (L⊥R _ (fa .left∈L) _ (fa .right∈R) _ _ refl)
        ( _ , C.pullr (sym (fa .factors)) ∙ gpq .centre .snd .fst
        , C.cancell (gpq .centre .snd .snd)) (C.id , C.idl _ , C.idr _)
```

Think back to the conclusion we wanted to reach: $r$ is in $L$, so since
$f = r \circ l$ and $R$ is stable, so is $f$!

```agda
      m∈L : fa .right ∈ L
      m∈L = is-iso→in-L (fa .right) $
        C.make-invertible (gpq .centre .fst) (gpq .centre .snd .snd) gm=id
```
