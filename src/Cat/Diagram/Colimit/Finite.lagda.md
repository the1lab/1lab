<!--
```agda
open import Cat.Diagram.Pushout.Properties
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Coequaliser
open import Cat.Diagram.Coproduct
open import Cat.Diagram.Initial
open import Cat.Diagram.Pushout
open import Cat.Prelude
open import Cat.Finite

import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Diagram.Colimit.Finite where
```

<!--
```agda
module _ {ℓ ℓ'} (C : Precategory ℓ ℓ') where
  open Cat C
```
-->

# Finitely cocomplete categories {defines="finite-colimit finitely-cocomplete finitely-cocomplete-category"}

Finitely **cocomplete** categories are dual to [[finitely complete
categories]] in that they admit colimits for all diagrams of
[[finite|finite category]] shape.

```agda
  is-finitely-cocomplete : Typeω
  is-finitely-cocomplete = ∀ {o ℓ} {D : Precategory o ℓ} → is-finite-precategory D
                         → (F : Functor D C) → Colimit F
```

Equivalently, a finitely cocomplete category has:

* An [[initial object]] (colimit over the empty diagram)
* All binary [[coproducts]] (colimits over any diagrams of shape $\bullet\quad\bullet$)
* All binary [[coequalisers]] (colimits over any diagrams of shape $\bullet\tto\bullet$)
* All binary [[pushouts]] (colimits over any diagrams of shape $\bullet\to\bullet\ot\bullet$)

```agda
  record Finitely-cocomplete : Type (ℓ ⊔ ℓ') where
    field
      initial      : Initial C
      coproducts   : Binary-coproducts C
      coequalisers : Coequalisers C
      pushouts     : Pushouts C

    open Initial initial public
    open Binary-coproducts coproducts public
    open Coequalisers coequalisers public
    open Pushouts pushouts public
```

As seen on the page for finitely complete categories, this definition
equivalently states that a finitely cocomplete category has either of
the following:

* An initial object, all binary coproducts, and all binary coequalisers
* An initial object and all binary pushouts

This follows from the fact that we can build coproducts and coequalisers
from pushouts, and that conversely, we can build pushouts from
coproducts and coequalisers. We begin by proving the latter.

## With coequalisers

We construct a pushout under a span $X \xot{f} Z \xto{g} Y$ as a
quotient object of a coproduct $X + Y$, i.e. the coequaliser
of $in_0f$ and $in_1g$ where $in_0$ and $in_1$ are injections into
the coproduct.

~~~{.quiver}
\[\begin{tikzcd}
	Z & {X + Y} & {X +_Z Y} \\
	&& {P'}
	\arrow["{in_0f}", shift left=1, from=1-1, to=1-2]
	\arrow["{in_1g}"', shift right=1, from=1-1, to=1-2]
	\arrow[from=1-2, to=1-3]
	\arrow[dashed, from=1-3, to=2-3]
	\arrow["{[i_1',i_2']}"', from=1-2, to=2-3]
\end{tikzcd}\]
~~~

Where $P'$ is some object which admits injections $i_1'$ and
$i_2'$ from X and Y respectively. This coequaliser
represents a pushout

~~~{.quiver}
\[\begin{tikzcd}
  Z && X \\
  \\
  Y && E
  \arrow["{g}", from=1-1, to=1-3]
  \arrow["{f}"', from=1-1, to=3-1]
  \arrow["in_1g"', from=1-3, to=3-3]
  \arrow["in_0f", from=3-1, to=3-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125, rotate=180}, draw=none, from=3-3, to=1-1]
\end{tikzcd}\]
~~~

where $E$ is the pushout's coapex, or equivalently, the coequaliser
of $in_0f$ and $in_1g$.

```agda
  coproduct+coequaliser→pushout
    : ∀ {E P X Y Z} {in1 : Hom X P} {in2 : Hom Y P} {f : Hom Z X}
        {g : Hom Z Y} {e : Hom P E}
    → is-coproduct C in1 in2
    → is-coequaliser C (in1 ∘ f) (in2 ∘ g) e
    → is-pushout C f (e ∘ in1) g (e ∘ in2)
  coproduct+coequaliser→pushout {in1 = in1} {in2} {f} {g} {e} cp cq = po where
    open is-pushout
    module cq = is-coequaliser cq
    module cp = is-coproduct cp

    po : is-pushout C _ _ _ _
    po .square = sym (assoc _ _ _) ∙ cq.coequal ∙ assoc _ _ _
    po .universal {i₁' = i₁'} {i₂'} p =
      cq.universal {e' = cp.[ i₁' , i₂' ]} (
        cp.[ i₁' , i₂' ] ∘ (in1 ∘ f) ≡⟨ pulll cp.[]∘ι₁ ⟩
        i₁' ∘ f                      ≡⟨ p ⟩
        i₂' ∘ g                      ≡˘⟨ pulll cp.[]∘ι₂ ⟩
        cp.[ i₁' , i₂' ] ∘ (in2 ∘ g) ∎
      )
    po .universal∘i₁ = pulll cq.factors ∙ cp.[]∘ι₁
    po .universal∘i₂ = pulll cq.factors ∙ cp.[]∘ι₂
    po .unique p q =
      cq.unique ((cp.unique (sym (assoc _ _ _) ∙ p) (sym (assoc _ _ _) ∙ q)))
```

Thus, if a category has an initial object, binary coproducts, and
binary coequalisers, it is finitely cocomplete.

```agda
  with-coequalisers
    : Initial C
    → Binary-coproducts C
    → Coequalisers C
    → Finitely-cocomplete
  with-coequalisers init copr coeq .Finitely-cocomplete.initial      = init
  with-coequalisers init copr coeq .Finitely-cocomplete.coproducts   = copr
  with-coequalisers init copr coeq .Finitely-cocomplete.coequalisers = coeq
  with-coequalisers init copr coeq .Finitely-cocomplete.pushouts     =
    has-pushouts→pushouts λ f g →
    coproduct+coequaliser→pushout has-is-coproduct has-is-coeq
    where
      open Binary-coproducts copr
      open Coequalisers coeq
```

## With pushouts

A coproduct is a pushout under a span whose vertex is the initial object.

```agda
  initial+pushout→coproduct
    : ∀ {P X Y I} {in1 : Hom X P} {in2 : Hom Y P} {f : Hom I X} {g : Hom I Y}
    → is-initial C I → is-pushout C f in1 g in2 → is-coproduct C in1 in2
  initial+pushout→coproduct {in1 = in1} {in2} {f} {g} init po = coprod where
      module Po = is-pushout po

      coprod : is-coproduct C in1 in2
      coprod .is-coproduct.[_,_] in1' in2' =
        Po.universal {i₁' = in1'} {i₂' = in2'} (is-contr→is-prop (init _) _ _)
      coprod .is-coproduct.[]∘ι₁ = Po.universal∘i₁
      coprod .is-coproduct.[]∘ι₂ = Po.universal∘i₂
      coprod .is-coproduct.unique p q = Po.unique p q
```


The construction of coequalisers from pushouts follows its [[dual|finite
limits]].

~~~{.quiver}
\[\begin{tikzcd}
	{A + A} && A \\
	\\
	B && {\rm{coequ}}
	\arrow[from=1-3, to=3-3]
	\arrow["{[\id, \id]}", from=1-1, to=1-3]
	\arrow["{[f,g]}"', from=1-1, to=3-1]
	\arrow["{\rm{coeq}}"', from=3-1, to=3-3]
	\arrow["\lrcorner"{anchor=center, pos=0.125, rotate=180}, draw=none, from=3-3, to=1-1]
\end{tikzcd}\]
~~~

```agda
  coproduct+pushout→coequaliser
    : ∀ {E X Y X+X}
    → {f g : Hom X Y} {e : Hom Y E} {ι₁ ι₂ : Hom X X+X} {i₁ : Hom X E}
    → (is-coprod : is-coproduct C ι₁ ι₂) (let open is-coproduct is-coprod)
    → (is-po : is-pushout C [ id , id ] i₁ [ f , g ] e)
    → is-coequaliser C f g e
```

<!--
```agda
  coproduct+pushout→coequaliser {f = f} {g} {e} {ι₁} {ι₂} {i₁} is-coprod is-po = is-coeq where
    open is-coproduct is-coprod renaming (unique₂ to []-unique₂)
    open is-pushout is-po renaming (unique to po-unique)

    is-coeq : is-coequaliser C f g e
    is-coeq .is-coequaliser.coequal =
      e ∘ f                   ≡˘⟨ pullr []∘ι₁ ⟩
      (e ∘ [ f , g ]) ∘ ι₁    ≡˘⟨ ap₂ _∘_ square refl ⟩
      (i₁ ∘ [ id , id ]) ∘ ι₁ ≡⟨ extendr ([]∘ι₁ ∙ sym []∘ι₂) ⟩
      (i₁ ∘ [ id , id ]) ∘ ι₂ ≡⟨ ap₂ _∘_ square refl ⟩
      (e ∘ [ f , g ]) ∘ ι₂    ≡⟨ pullr []∘ι₂ ⟩
      e ∘ g                   ∎
    is-coeq .is-coequaliser.universal {e' = e'} p =
      universal {i₁' = e' ∘ f} {i₂' = e'} comm
      where abstract
        comm : (e' ∘ f) ∘ [ id , id ] ≡ e' ∘ [ f , g ]
        comm =
          []-unique₂
            (cancelr []∘ι₁) (cancelr []∘ι₂)
            (pullr []∘ι₁) (pullr []∘ι₂ ∙ sym p)
    is-coeq .is-coequaliser.factors = universal∘i₂
    is-coeq .is-coequaliser.unique {e' = e'} {p = p} {other = other} other∘e=e' =
      po-unique
        other∘i₁=e'∘f
        other∘e=e'
      where
        other∘i₁=e'∘f : other ∘ i₁ ≡ e' ∘ f
        other∘i₁=e'∘f =
          other ∘ i₁ ≡⟨ insertr []∘ι₁ ⟩
          ((other ∘ i₁) ∘ [ id , id ]) ∘ ι₁ ≡⟨ ap₂ _∘_ (extendr square) refl ⟩
          ((other ∘ e) ∘ [ f , g ]) ∘ ι₁    ≡⟨ pullr []∘ι₁ ⟩
          (other ∘ e) ∘ f                   ≡⟨ ap₂ _∘_ other∘e=e' refl ⟩
          e' ∘ f                            ∎
```
-->


```agda
  with-pushouts
    : Initial C
    → Pushouts C
    → Finitely-cocomplete
  with-pushouts initial pushouts = fcc where
    open Initial initial
    open Pushouts pushouts

    coprods : Binary-coproducts C
    coprods = has-coproducts→binary-coproducts λ A B →
      initial+pushout→coproduct {f = ¡} {g = ¡} has⊥ has-is-po

    open Binary-coproducts coprods

    coeqs : Coequalisers C
    coeqs = has-coequalisers→coequalisers λ f g →
      coproduct+pushout→coequaliser has-is-coproduct has-is-po

    fcc : Finitely-cocomplete
    fcc .Finitely-cocomplete.initial      = initial
    fcc .Finitely-cocomplete.coproducts   = coprods
    fcc .Finitely-cocomplete.coequalisers = coeqs
    fcc .Finitely-cocomplete.pushouts     = pushouts
```

<!--
```agda
  coproduct→initial-pushout
    : ∀ {P X Y I} {in1 : Hom X P} {in2 : Hom Y P} {f : Hom I X} {g : Hom I Y}
    → is-initial C I → is-coproduct C in1 in2 → is-pushout C f in1 g in2
  coproduct→initial-pushout i r = po where
    open is-pushout
    po : is-pushout C _ _ _ _
    po .square = is-contr→is-prop (i _) _ _
    po .universal _ = r .is-coproduct.[_,_] _ _
    po .universal∘i₁ = r .is-coproduct.[]∘ι₁
    po .universal∘i₂ = r .is-coproduct.[]∘ι₂
    po .unique p q = r .is-coproduct.unique p q
```
-->

# Rex functors

A **right exact**, or **rex**, functor is a functor that preserves
finite colimits.

<!--
```agda
module _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'} where
  private module C = Cat C
  private module D = Cat D
```
-->

```agda
  record is-rex (F : Functor C D) : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
    private module F = Functor F

    field
      pres-⊥ : ∀ {I} → is-initial C I → is-initial D (F.₀ I)
      pres-pushout
        : ∀ {P X Y Z} {in1 : C.Hom X P} {in2 : C.Hom Y P}
            {f : C.Hom Z X} {g : C.Hom Z Y}
        → is-pushout C f in1 g in2
        → is-pushout D (F.₁ f) (F.₁ in1) (F.₁ g) (F.₁ in2)
    pres-coproduct
      : ∀ {P A B I} {in1 : C.Hom A P} {in2 : C.Hom B P}
      → is-initial C I
      → is-coproduct C in1 in2
      → is-coproduct D (F.₁ in1) (F.₁ in2)
    pres-coproduct  init copr = initial+pushout→coproduct D (pres-⊥ init)
      (pres-pushout {f = init _ .centre} {g = init _ .centre}
        (coproduct→initial-pushout C init copr))
    pres-epis : ∀ {A B} {f : C.Hom A B} → C.is-epic f → D.is-epic (F.₁ f)
    pres-epis {f = f} epi = is-pushout→is-epic
      (subst (λ x → is-pushout D _ x _ x) F.F-id
        (pres-pushout
          (is-epic→is-pushout epi)))
```
