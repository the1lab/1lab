---
description: |
  Epireflective subcategories.
---
<!--
```agda
open import Cat.Functor.Adjoint.Properties
open import Cat.Functor.Adjoint.Reflective
open import Cat.Morphism.Factorisation
open import Cat.Functor.Properties
open import Cat.Functor.Adjoint
open import Cat.Functor.Compose
open import Cat.Prelude

import Cat.Morphism.Strong.Mono
import Cat.Morphism.Strong.Epi
import Cat.Functor.Reasoning
import Cat.Natural.Reasoning
import Cat.Reasoning
```
-->
```agda
module Cat.Functor.Adjoint.Epireflective where
```

# Epireflective subcategories

:::{.definition #epireflective-subcategory}
A [[reflective subcategory]] is **epireflective** if the unit of
the adjunction is an [[epimorphism]].
:::

<!--
```agda
module _
  {oc ℓc od ℓd}
  {C : Precategory oc ℓc}
  {D : Precategory od ℓd}
  {L : Functor C D} {R : Functor D C}
  where
  private
    module C where
      open Cat.Reasoning C public
      open Cat.Morphism.Strong.Epi C public
    module D = Cat.Reasoning D
    module L = Cat.Functor.Reasoning L
    module R = Cat.Functor.Reasoning R
```
-->

```agda
  record is-epireflective (L⊣R : L ⊣ R) : Type (oc ⊔ od ⊔ ℓc ⊔ ℓd) where
    no-eta-equality
    open _⊣_ L⊣R
    field
      reflective : is-reflective L⊣R
      unit-epic : ∀ {x} → C.is-epic (η x)
```

:::{.definition #strong-epireflective-subcategory}
Likewise, a **strong epireflective category** is a reflective subcategory
where the unit is a [[strong epimorphism]].
:::

```agda
  record is-strong-epireflective (L⊣R : L ⊣ R) : Type (oc ⊔ od ⊔ ℓc ⊔ ℓd) where
    no-eta-equality
    open _⊣_ L⊣R
    field
      reflective : is-reflective L⊣R
      unit-strong-epi : ∀ {x} → C.is-strong-epi (η x)
```

<!--
```agda
module _
  {oc ℓc od ℓd}
  {C : Precategory oc ℓc}
  {D : Precategory od ℓd}
  {L : Functor C D} {R : Functor D C}
  (L⊣R : L ⊣ R)
  where
  private
    module C where
      open Cat.Reasoning C public
      open Cat.Morphism.Strong.Epi C public
      open Cat.Morphism.Strong.Mono C public
    module D = Cat.Reasoning D
    module L = Cat.Functor.Reasoning L
    module R = Cat.Functor.Reasoning R
  open _⊣_ L⊣R

  private
    Epi : ∀ {a b} → C.Hom a b → Ω
    Epi x = elΩ (C.is-epic x)

    Mono : ∀ {a b} → C.Hom a b → Ω
    Mono x = elΩ (C.is-monic x)

    StrongEpi : ∀ {a b} → C.Hom a b → Ω
    StrongEpi f = elΩ (C.is-strong-epi f)

    StrongMono : ∀ {a b} → C.Hom a b → Ω
    StrongMono f = elΩ (C.is-strong-mono f)
```
-->

## Epireflective subcategories and strong monos

If $L \dashv R$ is epireflective, and $f : \cC(X,R(A))$ is a
[[strong monomorphism]], then $\eta_{X}$ is invertible.

```agda
  epireflective+strong-mono→unit-invertible
    : is-epireflective L⊣R
    → ∀ {x a} {f : C.Hom x (R.₀ a)} → C.is-strong-mono f → C.is-invertible (η x)
```

It suffices to show that $\eta_{X}$ is a strong monomorphism, as strong
monos that are epic are isos. Luckily, this is rather straightforward:
strong monos can be left cancelled, so we can resort to showing that
$R(L(f)) \circ \eta_{X}$ is strong monic. However, $\eta$ is natural,
which gives us the following commutative square:

~~~{.quiver}
\begin{tikzcd}
  a && b \\
  \\
  c && d
  \arrow["f", tail, from=1-1, to=1-3]
  \arrow["{\eta_{X}}"', two heads, from=1-1, to=3-1]
  \arrow["{\eta_{R(L(X))}}", two heads, from=1-3, to=3-3]
  \arrow["{R(L(f))}"', tail, from=3-1, to=3-3]
\end{tikzcd}
~~~

Strong monos compose, so all that remains is to check that $\eta_{R(L(X))}$
is a strong mono. However, $\eta_{R(L(X))}$ is invertible, as the adjunction
is reflective!

```agda
  epireflective+strong-mono→unit-invertible epireflective {x} {a} {f} f-strong-mono =
    C.strong-mono+epi→invertible unit-strong-mono unit-epic where
      open is-epireflective epireflective

      unit-strong-mono : C.is-strong-mono (η x)
      unit-strong-mono = C.strong-mono-cancell (R.₁ (L.₁ f)) (η x)
        $ C.subst-is-strong-mono (unit.is-natural _ _ _)
        $ C.strong-mono-∘ (η (R.₀ a)) f
            (C.invertible→strong-mono
              (is-reflective→unit-right-is-iso L⊣R reflective))
            f-strong-mono
```

We also can prove a partial converse. $L \dashv R$ is epireflective if:

- $L \dashv R$ is reflective.
- $\eta_{X}$ is invertible if there is a strong mono $C(x, R(a))$.
- Every morphism $f : C(x,y)$ factors as an epi followed by a strong mono.

By our assumptions, $L \dashv R$ is reflective, so all we need to show is
that the unit is always epic.

```agda
  factor+strong-mono-unit-invertible→epireflective
    : is-reflective L⊣R
    → (∀ {x a} {f : C.Hom x (R.₀ a)} → C.is-strong-mono f → C.is-invertible (η x))
    → (∀ {x y} → (f : C.Hom x y) → Factorisation C Epi StrongMono f)
    → ∀ {x} → C.is-epic (η x)
```

The proof starts by factoring the unit $\eta_{X}$ as $m \circ e$. Moreover,
we can extend this factorisation along $\eta$, yielding the following
diagram:

~~~{.quiver}
\begin{tikzcd}
   X &&&& {R(L(X))} \\
   && I \\
   {R(L(X))} &&&& {R(L(R(L(X))))} \\
   && {R(L(I))}
   \arrow["{\eta_{X}}", no head, from=1-1, to=1-5]
   \arrow["e"', two heads, from=1-1, to=2-3]
   \arrow["{\eta_{X}}"', from=1-1, to=3-1]
   \arrow["{\eta_{R(L(X))}}", from=1-5, to=3-5]
   \arrow["m"', tail, from=2-3, to=1-5]
   \arrow["{\eta_I}"'{pos=0.2}, shift left, from=2-3, to=4-3]
   \arrow["{R(L(\eta_{X}))}"{pos=0.7}, from=3-1, to=3-5]
   \arrow["{R(L(e))}"', from=3-1, to=4-3]
  \arrow["{R(L(m))}"', from=4-3, to=3-5]
\end{tikzcd}
~~~

```agda
  factor+strong-mono-unit-invertible→epireflective reflective unit-inv factor {x} =
    unit-epic where
      open Factorisation (factor (η x)) renaming
        ( mediating to im
        ; forget to m
        ; mediate to e
        ; forget∈M to m-strong-mono
        ; mediate∈E to e-epi
        )
```

What follows is a massive diagram chase. First, note that $\eta_{I}$ must
be invertible, as $m : \cC(I, R(L(X)))$ is a strong mono.

```agda
      unit-im-invertible : C.is-invertible (η im)
      unit-im-invertible = unit-inv (□-out! m-strong-mono)
```

Next, observe that $R(L(m)) \circ R(L(e))$ must also be invertible:
their composite is $R(L(\eta_{X}))$, which is always invertible if
$L \dashv R$ is reflective.

```agda
      RL[m]∘RL[e]-invertible : C.is-invertible (R.₁ (L.₁ m) C.∘ R.₁ (L.₁ e))
      RL[m]∘RL[e]-invertible = C.subst-is-invertible (R.expand (L.expand factors))
        $ R.F-map-invertible
        $ is-reflective→left-unit-is-iso L⊣R reflective
```

This in turn means that $L(R(e))$ must be a strong mono, as
we can cancel strong monos.

```agda
      RL[e]-strong-mono : C.is-strong-mono (R.₁ (L.₁ e))
      RL[e]-strong-mono = C.strong-mono-cancell (R.₁ (L.₁ m)) (R.₁ (L.₁ e))
        $ C.invertible→strong-mono
        $ RL[m]∘RL[e]-invertible
```

Moreover, $R(L(e))$ is also epic. This follows from a somewhat convoluted chase:
$\eta_{I} \circ e$ has to be epic, as $\eta_{I}$ is invertible.
Moreover, $\eta_{I} \circ e = R(L(e)) \circ \eta{X}$, so we can use
right-cancellation of epis to deduce that $R(L(e))$ must be epic.

```agda
      RL[e]-epic : C.is-epic (R.₁ (L.₁ e))
      RL[e]-epic = C.epic-cancelr $ C.subst-is-epic (unit.is-natural _ _ _)
        $ C.∘-is-epic (C.invertible→epic unit-im-invertible) (□-out! e-epi)
```

We can put the previous two observations together to show that
$R(L(e))$ must be invertible. Additionally, $R(L(m))$ must also be
invertible by 2-out-of-3.

```agda
      RL[e]-invertible : C.is-invertible (R.₁ (L.₁ e))
      RL[e]-invertible = C.strong-mono+epi→invertible RL[e]-strong-mono RL[e]-epic

      RL[m]-invertible : C.is-invertible (R.₁ (L.₁ m))
      RL[m]-invertible = C.invertible-cancell RL[e]-invertible
        $ RL[m]∘RL[e]-invertible
```

We're on to the home stretch now! Our final penultimate step is to
show that $m$ must be invertible. This is another somewhat convoluted
chase: $R(L(m)) \circ \eta_{I}$ is invertible, so $\eta_{(R(L(X)))} \circ m$
must also be invertible by naturality. However, $\eta_{(R(L(X)))}$ must
itself be invertible, so $m$ is invertible via 2-out-of-3.

```agda
      m-invertible : C.is-invertible m
      m-invertible = C.invertible-cancelr
        (is-reflective→unit-right-is-iso L⊣R reflective)
        (C.subst-is-invertible (sym (unit.is-natural _ _ _))
          $ C.invertible-∘ RL[m]-invertible unit-im-invertible)
```

The prior step means that $\eta_{X}$ factors into a pair of epis,
so it must also be an epi.

```agda
      unit-epic : C.is-epic (η x)
      unit-epic = C.subst-is-epic (sym factors)
        $ C.∘-is-epic (C.invertible→epic m-invertible) (□-out! e-epi)
```

## Strong epireflective subcategories and monos

Our previous results relating epireflections and strong monos
relied on the (very useful) fact that morphisms that are both strong monos
and epis are isos. However, we can alternatively use monos and strong epis
to prove invertability: this suggests that we can weaken the preconditions
when $L \dashv R$ is a strong epireflective category.

```agda
  strong-epireflective+mono→unit-invertible
    : is-strong-epireflective L⊣R
    → ∀ {x a} {f : C.Hom x (R.₀ a)} → C.is-monic f → C.is-invertible (η x)

  factor+mono-unit-invertible→strong-epireflective
    : is-reflective L⊣R
    → (∀ {x a} {f : C.Hom x (R.₀ a)} → C.is-monic f → C.is-invertible (η x))
    → (∀ {x y} → (f : C.Hom x y) → Factorisation C StrongEpi Mono f)
    → ∀ {x} → C.is-strong-epi (η x)

```

<details>
<summary>Fortunately, the proofs are almost identical to their non-strong
counterparts. Unfortunately, this means that we need to replay the giant
diagram chase; we will spare the innocent reader the details.
</summary>
```agda
  strong-epireflective+mono→unit-invertible strong-epirefl {x} {a} {f} f-mono =
    C.strong-epi+mono→invertible unit-strong-epi unit-mono where
      open is-strong-epireflective strong-epirefl

      unit-mono : C.is-monic (η x)
      unit-mono = C.monic-cancell $ C.subst-is-monic (unit.is-natural _ _ _)
        $ C.∘-is-monic
            (C.invertible→monic (is-reflective→unit-right-is-iso L⊣R reflective))
            f-mono

  factor+mono-unit-invertible→strong-epireflective reflective unit-inv factor {x} =
    unit-strong-epi where
      open Factorisation (factor (η x)) renaming
        ( mediating to im
        ; forget to m
        ; mediate to e
        ; forget∈M to m-mono
        ; mediate∈E to e-strong-epi
        )

      unit-im-invertible : C.is-invertible (η im)
      unit-im-invertible = unit-inv (□-out! m-mono)

      RL[m]∘RL[e]-invertible
        : C.is-invertible (R.₁ (L.₁ m) C.∘ R.₁ (L.₁ e))
      RL[m]∘RL[e]-invertible = C.subst-is-invertible (R.expand (L.expand factors))
        $ R.F-map-invertible $ is-reflective→left-unit-is-iso L⊣R reflective

      RL[e]-mono : C.is-monic (R.₁ (L.₁ e))
      RL[e]-mono = C.monic-cancell $ C.invertible→monic $ RL[m]∘RL[e]-invertible

      RL[e]-strong-epi : C.is-strong-epi (R.₁ (L.₁ e))
      RL[e]-strong-epi = C.strong-epi-cancelr _ _
        $ C.subst-is-strong-epi (unit.is-natural _ _ _)
        $ C.strong-epi-∘ _ _
            (C.invertible→strong-epi unit-im-invertible)
            (□-out! e-strong-epi)

      RL[e]-invertible : C.is-invertible (R.₁ (L.₁ e))
      RL[e]-invertible = C.strong-epi+mono→invertible RL[e]-strong-epi RL[e]-mono

      RL[m]-invertible : C.is-invertible (R.₁ (L.₁ m))
      RL[m]-invertible = C.invertible-cancell RL[e]-invertible
        RL[m]∘RL[e]-invertible

      m-invertible : C.is-invertible m
      m-invertible = C.invertible-cancelr
        (is-reflective→unit-right-is-iso L⊣R reflective)
        (C.subst-is-invertible (sym (unit.is-natural _ _ _))
          $ C.invertible-∘ RL[m]-invertible unit-im-invertible)

      unit-strong-epi : C.is-strong-epi (η x)
      unit-strong-epi = C.subst-is-strong-epi (sym factors) $ C.strong-epi-∘ _ _
        (C.invertible→strong-epi m-invertible)
        (□-out! e-strong-epi)
```
</details>
