<!--
```agda
{-# OPTIONS --lossy-unification -vtc.def.fun:10 #-}
open import Cat.Instances.Sets.Complete
open import Cat.Bi.Instances.Spans
open import Cat.Bi.Diagram.Monad
open import Cat.Instances.Sets
open import Cat.Bi.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Bi.Diagram.Monad.Spans {ℓ} where
```

<!--
```agda
open Precategory
open Span-hom
open Span
private module Sb = Prebicategory (Spanᵇ (Sets ℓ) Sets-pullbacks)
```
-->

# Monads in Spans(Sets)

Let $\cC$ be a [[strict category]]. Whatever your favourite strict
category might be --- it doesn't matter in this case. Let $\cC_0$
denote its set of objects, and write $\cC(x, y)$ for its Hom-family.
We know that families are equivalently [fibrations], so that we may define

[fibrations]: 1Lab.Univalence.html#object-classifiers

$$
\cC_1 = \sum_{x, y : \cC_0} \cC(x, y)\text{,}
$$

and, since the family is valued in $\Sets$ and indexed by a set, so is
$\cC_1$. We can picture $\cC_1$ together with the components of
its first projection as a _[span]_ in the category of sets

[span]: Cat.Bi.Instances.Spans.html

~~~{.quiver}
\[\begin{tikzcd}
  & {\mathcal{C}_1} \\
  {\mathcal{C}_0} && {\mathcal{C}_0\text{.}}
  \arrow["s", from=1-2, to=2-1]
  \arrow["t"', from=1-2, to=2-3]
\end{tikzcd}\]
~~~

Under this presentation, what does the composition operation correspond
to? Well, it takes something in the object of _composable morphisms_, a
certain subset of $\cC_1 \times \cC_1$, and yields a morphism,
i.e. something in $\cC_1$. Moreover, this commutes with taking
source/target: The source of the composition is the source of its first
argument, and the target is the target of its second argument. The key
observation, that will lead to a new representation of categories, is
that the object of composable morphisms is _precisely_ the composition
$\cC_1 \circ \cC_1$ in the bicategory $\bicat{Span}(\Sets)$!

~~~{.quiver}
\[\begin{tikzcd}
  && {\mathcal{C}_1 \times_{\mathcal{C}_0} \mathcal{C}_1} \\
  & {\mathcal{C}_1} && {\mathcal{C}_1} \\
  {\mathcal{C}_0} && {\mathcal{C}_0} && {\mathcal{C}_0}
  \arrow["s", from=2-2, to=3-1]
  \arrow["t"', from=2-2, to=3-3]
  \arrow["s", from=2-4, to=3-3]
  \arrow["t"', from=2-4, to=3-5]
  \arrow[from=1-3, to=2-2]
  \arrow[from=1-3, to=2-4]
  \arrow["\lrcorner"{anchor=center, pos=0.125, rotate=-45}, draw=none, from=1-3, to=3-3]
\end{tikzcd}\]
~~~

Phrased like this, we see that the composition map gives an associative
and unital procedure for mapping $(\cC_1\cC_1) \To \cC_1$ in a
certain bicategory --- a [monad] in that bicategory.

[monad]: Cat.Bi.Diagram.Monad.html

```agda
Spans[Sets] : Prebicategory _ _ _
Spans[Sets] = Spanᵇ (Sets ℓ) Sets-pullbacks

strict-category→span-monad
  : (C : Precategory ℓ ℓ) (cset : is-set (C .Ob))
  → Monad Spans[Sets] (el _ cset)
strict-category→span-monad C cset = m where
  open Monad
  open n-Type (el {n = 2} _ cset) using (H-Level-n-type)
  open Precategory.HLevel-instance C
  module C = Precategory C

  homs : Span (Sets ℓ) (el _ cset) (el _ cset)
  homs .apex = el (Σ[ x ∈ C .Ob ] Σ[ y ∈ C .Ob ] (C .Hom x y)) (hlevel 2)
  homs .left (x , _ , _) = x
  homs .right (_ , y , _) = y

  mult : _ Sb.⇒ _
  mult .map ((x , y , f) , (z , x' , g) , p) =
    z , y , subst (λ e → C.Hom e y) p f C.∘ g
  mult .left = refl
  mult .right = refl

  unit : _ Sb.⇒ _
  unit .map x = x , x , C .id
  unit .left = refl
  unit .right = refl

  m : Monad Spans[Sets] (el (C .Ob) cset)
  m .M = homs
  m .μ = mult
  m .η = unit
```

It is annoying, but entirely straightforward, to verify that the
operations `mult`{.Agda} and `unit`{.Agda} defined above _do_ constitute
a monad in $\bicat{Span}(\Sets)$. We omit the verification here and
instruct the curious reader to check the proof on GitHub.

<!--
```agda
  m .μ-assoc = Span-hom-path (Sets ℓ) $ funext λ where
    ((w , x , f) , ((y , z , g) , (a , b , h) , p) , q) →
      J' (λ w z q → ∀ (f : C.Hom w x) {y b} (p : y ≡ b) (g : C .Hom y z)
                      (h : C.Hom a b)
                  → (mult Sb.∘ (homs Sb.▶ mult)) .map ((w , x , f) , ((y , z , g) , (a , b , h) , p) , q)
                  ≡ (mult Sb.∘ (mult Sb.◀ homs) Sb.∘ Sb.α← homs homs homs) .map ((w , x , f) , ((y , z , g) , (a , b , h) , p) , q))
         (λ w f → J' (λ y b p → (g : C.Hom y w) (h : C.Hom a b) →
            (mult Sb.∘ (homs Sb.▶ mult)) .map ((w , x , f) , ((y , w , g) , (a , b , h) , p) , refl)
          ≡ (mult Sb.∘ (mult Sb.◀ homs) Sb.∘ Sb.α← homs homs homs) .map ((w , x , f) , ((y , w , g) , (a , b , h) , p) , refl))
          λ y g h → Σ-pathp refl (Σ-pathp refl (C.assoc _ _ _
            ∙ ap₂ C._∘_ (ap₂ C._∘_ (ap (λ p → subst (λ e → C.Hom e x) p f) (hlevel 2 w w _ refl) ∙ transport-refl _)
                                   (ap (λ p → subst (λ e → C.Hom e w) p g) (hlevel 2 y y _ refl) ∙ transport-refl _)
                        ∙ sym ((ap (subst (λ e → C.Hom e x) _)
                                  (ap₂ C._∘_ ((ap (λ p → subst (λ e → C.Hom e x) p f) (hlevel 2 w w _ refl) ∙ transport-refl _))
                                  refl) ∙ ap (λ p → subst (λ e → C.Hom e x) p (f C.∘ g)) (hlevel 2 y y _ refl) ∙ transport-refl _)))
                        refl)))
         q f p g h
  m .μ-unitr = Span-hom-path (Sets ℓ) $ funext λ where
    ((x , y , f) , z , p) →
      J' (λ x z p → (f : C .Hom x y) → (mult Sb.∘ (homs Sb.▶ unit)) .map ((x , y , f) , z , p)
                                     ≡ (x , y , f))
         (λ x f → Σ-pathp refl
            (Σ-pathp refl (ap₂ C._∘_ (ap (λ p → subst (λ e → C.Hom e y) p f) (hlevel 2 _ _ _ _) ∙ transport-refl _) refl
                          ∙ C.idr _)))
         p f
  m .μ-unitl = Span-hom-path (Sets ℓ) $ funext λ where
    (x , (y , z , f) , p) →
      J' (λ x z p → (f : C .Hom y z)
           → (mult Sb.∘ (unit Sb.◀ homs)) .map (x , (y , z , f) , p)
           ≡ (y , z , f))
         (λ x f → Σ-pathp refl
            (Σ-pathp refl (ap₂ C._∘_ (ap (λ p → subst (λ e → C.Hom e x) p C.id) (hlevel 2 _ _ _ _) ∙ transport-refl _) refl
                          ∙ C.idl _)))
         p f
```
-->

Conversely, if we _have_ an associative and unital method mapping
composable morphisms into morphisms, it stands to reason that we should
be able to recover a category. Indeed, we can! The verification is once
more annoying, but unsurprising. Since it's less of a nightmare this
time around, we include it in full below.

```agda
span-monad→strict-category : ∀ (C : Set ℓ) → Monad Spans[Sets] C → Precategory _ _
span-monad→strict-category C monad = precat where
  open Monad monad

  open n-Type C using (H-Level-n-type)
  open n-Type (M .apex) using (H-Level-n-type)

  precat : Precategory _ _
  precat .Ob = ∣ C ∣
  precat .Hom a b = Σ[ s ∈ ∣ M .apex ∣ ] ((M .left s ≡ a) × (M .right s ≡ b))
  precat .Hom-set x y = hlevel 2
  precat .id {x} = η .map x , sym (happly (η .left) x) , sym (happly (η .right) x)
  precat ._∘_ (f , fs , ft) (g , gs , gt) =
      μ .map (f , g , fs ∙ sym gt)
    , sym (happly (μ .left) _) ∙ gs
    , sym (happly (μ .right) _) ∙ ft
```

The family of morphisms $\hom(x,y)$ of our recovered category is
precisely the fibre of $(s,t) : \cC_1 \to \cC_0 \times \cC_0$ over the
pair $x, y$. The commutativity conditions for 2-cells in
$\bicat{Span}(\Sets)$ implies that source and target are preserved
through composition, and that the identity morphism --- that is, the
image of $x$ under the unit map --- lies in the fibre over $x, x$.

The verification follows from the monad laws, and it would be trivial in
extensional type theory, but the tradeoff for decidable type-checking is
having to munge paths sometimes. This is one of those times:

```agda
  precat .idr {x} {y} f = Σ-prop-path (λ _ → hlevel 1)
    ( ap (μ .map) (ap (f .fst ,_) (Σ-prop-path (λ _ → C .is-tr _ _) refl))
    ∙ happly (ap map μ-unitr) (f .fst , x , f .snd .fst))
  precat .idl {x} {y} f = Σ-prop-path (λ _ → hlevel 1)
    ( ap (μ .map) (ap (η .map y ,_) (Σ-prop-path (λ _ → C .is-tr _ _) refl))
    ∙ happly (ap map μ-unitl) (y , f .fst , sym (f .snd .snd)))
  precat .assoc f g h = Σ-prop-path (λ _ → hlevel 1)
    ( ap (μ .map) (ap (f .fst ,_) (Σ-prop-path (λ _ → hlevel 1)
        (ap (μ .map) (ap (g .fst ,_)
          (Σ-prop-path (λ _ → hlevel 1) (refl {x = h .fst}))))))
    ·· happly (ap map μ-assoc)
        ( f .fst , (g .fst , h .fst , g .snd .fst ∙ sym (h .snd .snd))
        , f .snd .fst ∙ sym (g .snd .snd)
        )
    ·· ap (μ .map) (Σ-pathp (ap (μ .map) (ap (f .fst ,_)
        (Σ-prop-path (λ _ → hlevel 1) refl)))
           (Σ-pathp refl (is-prop→pathp (λ _ → hlevel 1) _ _))))
```
