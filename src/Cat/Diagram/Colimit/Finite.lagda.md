```agda
open import Cat.Diagram.Coproduct
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Coequaliser
open import Cat.Diagram.Pushout
open import Cat.Diagram.Initial
open import Cat.Prelude
open import Cat.Thin

import Cat.Reasoning as Cat

module Cat.Diagram.Colimit.Finite where
```

<!--
```agda
module _ {ℓ ℓ'} (C : Precategory ℓ ℓ') where
  open Cat C
```
-->

# Finitely Cocomplete Categories

Finitely **cocomplete** categories are dual to [finitely complete categories]
in that they admit colimits for all diagrams of finite shape. A finitely
cocomplete category has:

* An [initial object] (colimit over the empty diagram)
* All binary [coproducts] (colimits over any diagrams of shape $\bullet\quad\bullet$)
* All binary [coequalisers] (colimits over any diagrams of shape $\bullet\tto\bullet$)
* All binary [pushouts] (colimits over any diagrams of shape $\bullet\to\bullet\ot\bullet$)

[finitely complete categories]: Cat.Diagram.Limit.Finite.html
[initial object]: Cat.Diagram.Initial.html
[coproducts]: Cat.Diagram.Product.html
[coequalisers]: Cat.Diagram.Pullback.html
[pushouts]: Cat.Diagram.Equaliser.html

```agda
  record Finitely-cocomplete : Type (ℓ ⊔ ℓ') where
    field
      initial      : Initial C
      coproducts   : ∀ A B → Coproduct C A B
      coequalisers : ∀ {A B} (f g : Hom A B) → Coequaliser C f g
      pushouts     : ∀ {A B X} (f : Hom X A) (g : Hom X B) → Pushout C f g

    Coequ : ∀ {A B} (f g : Hom A B) → Ob
    Coequ f g = coequalisers f g .Coequaliser.coapex

    Po : ∀ {A B C} (f : Hom C A) (g : Hom C B) → Ob
    Po f g = pushouts f g .Pushout.coapex

  open Finitely-cocomplete
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
  coproduct-coequaliser→pushout
    : ∀ {E P X Y Z} {in1 : Hom X P} {in2 : Hom Y P} {f : Hom Z X}
        {g : Hom Z Y} {e : Hom P E}
    → is-coproduct C in1 in2
    → is-coequaliser C (in1 ∘ f) (in2 ∘ g) e
    → is-pushout C f (e ∘ in1) g (e ∘ in2)
  coproduct-coequaliser→pushout {in1 = in1} {in2} {f} {g} {e} cp cq = po where
    open is-pushout
    module cq = is-coequaliser cq
    module cp = is-coproduct cp

    po : is-pushout C _ _ _ _
    po .square = sym (assoc _ _ _) ∙ cq.coequal ∙ assoc _ _ _
    po .colimiting {i₁′ = i₁′} {i₂′} p =
      cq.coequalise {e′ = cp.[ i₁′ , i₂′ ]} (
        cp.[ i₁′ , i₂′ ] ∘ (in1 ∘ f) ≡⟨ pulll cp.in₀∘factor ⟩
        i₁′ ∘ f                      ≡⟨ p ⟩
        i₂′ ∘ g                      ≡˘⟨ pulll cp.in₁∘factor ⟩
        cp.[ i₁′ , i₂′ ] ∘ (in2 ∘ g) ∎
      )
    po .i₁∘colimiting = pulll cq.universal ∙ cp.in₀∘factor
    po .i₂∘colimiting = pulll cq.universal ∙ cp.in₁∘factor
    po .unique p q =
      cq.unique (sym (cp.unique _ (sym (assoc _ _ _) ∙ p) (sym (assoc _ _ _) ∙ q)))
```

Thus, if a category has an initial object, binary coproducts, and
binary coequalisers, it is finitely cocomplete.

```agda
  with-coequalisers
    : Initial C
    → (∀ A B → Coproduct C A B)
    → (∀ {A B} (f g : Hom A B) → Coequaliser C f g)
    → Finitely-cocomplete
  with-coequalisers init copr coeq .initial      = init
  with-coequalisers init copr coeq .coproducts   = copr
  with-coequalisers init copr coeq .coequalisers = coeq
  with-coequalisers init copr coeq .pushouts {A} {B} {X} f g =
    record { has-is-po = coproduct-coequaliser→pushout Copr.has-is-coproduct Coequ.has-is-coeq }
    where
      module Copr = Coproduct (copr A B)
      module Coequ = Coequaliser (coeq (Copr.in₀ ∘ f) (Copr.in₁ ∘ g))
```

## With pushouts

A coproduct is a pushout under a span whose vertex is the initial object.

```agda
  initial-pushout→coproduct
    : ∀ {P X Y I} {in1 : Hom X P} {in2 : Hom Y P} {f : Hom I X} {g : Hom I Y}
    → is-initial C I → is-pushout C f in1 g in2 → is-coproduct C in1 in2
  initial-pushout→coproduct {in1 = in1} {in2} {f} {g} init po = coprod where
      module Po = is-pushout po

      coprod : is-coproduct C in1 in2
      coprod .is-coproduct.[_,_] in1′ in2′ =
        Po.colimiting {i₁′ = in1′} {i₂′ = in2′} (is-contr→is-prop (init _) _ _)
      coprod .is-coproduct.in₀∘factor = Po.i₁∘colimiting
      coprod .is-coproduct.in₁∘factor = Po.i₂∘colimiting
      coprod .is-coproduct.unique other p q = Po.unique p q

  with-pushouts
    : Initial C
    → (∀ {A B X} (f : Hom X A) (g : Hom X B) → Pushout C f g)
    → Finitely-cocomplete
  with-pushouts bot po = fcc where
    module bot = Initial bot
    mkcoprod : ∀ A B → Coproduct C A B
    mkcoprod A B = record { has-is-coproduct = initial-pushout→coproduct bot.has⊥ po′ }
      where po′ = po (bot.has⊥ A .centre) (bot.has⊥ B .centre) .Pushout.has-is-po

    mkcoeq : ∀ {A B} (f g : Hom A B) → Coequaliser C f g
    mkcoeq {A = A} {B} f g = coequ where
```

The construction of coequalisers from pushouts follows its
[dual].

[dual]: Cat.Diagram.Limit.Finite#8325.html

~~~{.quiver}
\iu04[\begin{tikzcd}
	{A + A} && A \\
	\\
	B && {\id{coequ}}
	\arrow[from=1-3, to=3-3]
	\arrow["{[\id{id}, \id{id}]}", from=1-1, to=1-3]
	\arrow["{[f,g]}"', from=1-1, to=3-1]
	\arrow["{\id{coeq}}"', from=3-1, to=3-3]
	\arrow["\lrcorner"{anchor=center, pos=0.125, rotate=180}, draw=none, from=3-3, to=1-1]
\end{tikzcd}\]
~~~

<!--
```agda
      module A+A = Coproduct (mkcoprod A A)
      [id,id] : Hom A+A.coapex A
      [id,id] = A+A.[ id , id ]

      [f,g] : Hom A+A.coapex B
      [f,g] = A+A.[ f , g ]

      module Po = Pushout (po [f,g] [id,id])

      open is-coequaliser
      open Coequaliser
```
-->

```agda
      coequ : Coequaliser C f g
      coequ .coapex = Po.coapex
      coequ .coeq = Po.i₁
      coequ .has-is-coeq .coequal =
        Po.i₁ ∘ f                 ≡˘⟨ ap (Po.i₁ ∘_) A+A.in₀∘factor ⟩
        Po.i₁ ∘ [f,g] ∘ A+A.in₀   ≡⟨ assoc _ _ _ ∙ ap (_∘ A+A.in₀) Po.square ⟩
        (Po.i₂ ∘ [id,id]) ∘ A+A.in₀ ≡⟨ sym (assoc _ _ _) ∙ pushr (A+A.in₀∘factor ∙ sym A+A.in₁∘factor) ⟩
        (Po.i₂ ∘ [id,id]) ∘ A+A.in₁ ≡⟨ ap (_∘ A+A.in₁) (sym Po.square) ⟩
        (Po.i₁ ∘ [f,g]) ∘ A+A.in₁   ≡⟨ sym (assoc _ _ _) ∙ ap (Po.i₁ ∘_) A+A.in₁∘factor ⟩
        Po.i₁ ∘ g                 ∎
      coequ .has-is-coeq .coequalise {e′ = e′} p =
        Po.colimiting (A+A.unique₂ _ refl refl _ (in1) (in2))
        where
          in1 : ((e′ ∘ f) ∘ [id,id]) ∘ A+A.in₀ ≡ (e′ ∘ [f,g]) ∘ A+A.in₀
          in1 =
            ((e′ ∘ f) ∘ [id,id]) ∘ A+A.in₀ ≡⟨ cancelr A+A.in₀∘factor ⟩ -- ≡⟨ cancell A+A.in₀∘factor ⟩
            e′ ∘ f                     ≡˘⟨ pullr A+A.in₀∘factor ⟩ -- ≡˘⟨ pulll A+A.in₀∘factor ⟩
            (e′ ∘ [f,g]) ∘ A+A.in₀       ∎

          in2 : ((e′ ∘ f) ∘ [id,id]) ∘ A+A.in₁ ≡ (e′ ∘ [f,g]) ∘ A+A.in₁
          in2 =
            ((e′ ∘ f) ∘ [id,id]) ∘ A+A.in₁  ≡⟨ cancelr A+A.in₁∘factor ⟩
            e′ ∘ f                     ≡⟨ p ⟩
            e′ ∘ g                     ≡˘⟨ pullr A+A.in₁∘factor ⟩
            (e′ ∘ [f,g]) ∘ A+A.in₁        ∎

      coequ .has-is-coeq .universal = Po.i₁∘colimiting
      coequ .has-is-coeq .unique {F} {e′ = e′} {colim = colim} e′=col∘i₁ =
        Po.unique (sym e′=col∘i₁) path
        where
          path : colim ∘ Po.i₂ ≡ e′ ∘ f
          path =
            colim ∘ Po.i₂                         ≡⟨ insertr A+A.in₀∘factor ⟩
            ((colim ∘ Po.i₂) ∘ [id,id]) ∘ A+A.in₀ ≡⟨ ap (_∘ A+A.in₀) (extendr (sym Po.square)) ⟩
            ((colim ∘ Po.i₁) ∘ [f,g]) ∘ A+A.in₀   ≡⟨ ap (_∘ A+A.in₀) (ap (_∘ [f,g]) (sym e′=col∘i₁)) ⟩
            (e′ ∘ [f,g]) ∘ A+A.in₀                ≡⟨ pullr A+A.in₀∘factor ⟩
            e′ ∘ f           ∎

    fcc : Finitely-cocomplete
    fcc .initial      = bot
    fcc .coproducts   = mkcoprod
    fcc .coequalisers = mkcoeq
    fcc .pushouts     = po
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
    po .colimiting _ = r .is-coproduct.[_,_] _ _
    po .i₁∘colimiting = r .is-coproduct.in₀∘factor
    po .i₂∘colimiting = r .is-coproduct.in₁∘factor
    po .unique p q = r .is-coproduct.unique _ p q
```
-->

## Thinly

A finitely cocomplete thin category corresponds to a bounded
join-semilattice in that it is given by binary coproducts
and an initial object.

```agda
  with-bot-and-joins
      : is-thin C
      → Initial C
      → (∀ A B → Coproduct C A B)
      → Finitely-cocomplete
  with-bot-and-joins thin bot joins = fc where
    open Pushout
    module Thin = is-thin thin

    fc : Finitely-cocomplete
    fc .initial = bot
    fc .coproducts = joins
```

Coequalisers for parallel morphisms $f, g : A \to B$ are B and the
coequalising map is $\id{id}$.

```agda
    fc .coequalisers {A} {B} f g = thin-coequalise where
        open Coequaliser
        open is-coequaliser
        thin-coequalise : Coequaliser C _ _
        thin-coequalise .coapex = B
        thin-coequalise .coeq = id
        thin-coequalise .has-is-coeq .coequal = Thin.Hom-is-prop _ _ _ _
        thin-coequalise .has-is-coeq .coequalise {e′ = e′} p = e′
        thin-coequalise .has-is-coeq .universal = idr _
        thin-coequalise .has-is-coeq .unique p = Thin.Hom-is-prop _ _ _ _
  ```

Since pushouts may be constructed as quotient objects of coproducts
and coequalising maps are trivial, $(A +_C B) = (A + B)$.

  ```agda
    fc .pushouts {A} {B} f g = po where
        open Pushout
        open is-pushout
        module P = Coproduct (joins A B)
        po : Pushout C _ _
        po .coapex = P.coapex
        po .i₁ = P.in₀
        po .i₂ = P.in₁
        po .has-is-po .square = Thin.Hom-is-prop _ _ _ _
        po .has-is-po .colimiting {i₁′ = i₁′} {i₂′ = i₂′} p = P.[ i₁′ , i₂′ ]
        po .has-is-po .i₁∘colimiting = P.in₀∘factor
        po .has-is-po .i₂∘colimiting = P.in₁∘factor
        po .has-is-po .unique _ _ = Thin.Hom-is-prop _ _ _ _
```

# Rex functors

A **right exact**, or **rex**, functor is a functor that preserves
finite colimits.

<!--
```agda
module _ {o ℓ o′ ℓ′} {C : Precategory o ℓ} {D : Precategory o′ ℓ′} where
  private module C = Precategory C
```
-->

```agda
  record is-rex (F : Functor C D) : Type (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
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
    pres-coproduct  init copr = initial-pushout→coproduct D (pres-⊥ init)
      (pres-pushout {f = init _ .centre} {g = init _ .centre}
        (coproduct→initial-pushout C init copr))
```