<!--
```agda
{-# OPTIONS --hidden-argument-puns #-}
open import 1Lab.Reflection.Induction
open import 1Lab.Prelude

open import Homotopy.Space.Suspension
```
-->

```agda
module Homotopy.Pushout where
```

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
  A B C X : Type ℓ
```
-->

# Pushouts {defines="pushout"}

Given the following span:

~~~{.quiver}
\[\begin{tikzcd}
  C && B \\
  \\
  A
  \arrow["g", from=1-1, to=1-3]
  \arrow["f"', from=1-1, to=3-1]
\end{tikzcd}\]
~~~

The **pushout** of this span is defined as the higher inductive type
presented by:

```agda
data Pushout (C : Type ℓ) (f : C → A) (g : C → B) : Type (level-of A ⊔ level-of B ⊔ ℓ) where
  inl  : A → Pushout C f g
  inr  : B → Pushout C f g
  glue : ∀ c → inl (f c) ≡ inr (g c)
```

<!--
```agda
unquoteDecl Pushout-elim = make-elim Pushout-elim (quote Pushout)
```
-->

These combine to give the following:

~~~{.quiver}
\[\begin{tikzcd}
	C && B \\
	\\
	A && {\rm{Pushout}}
	\arrow["g", from=1-1, to=1-3]
	\arrow["f"', from=1-1, to=3-1]
	\arrow["{\rm{inr}}", from=1-3, to=3-3]
	\arrow["{\rm{commutes}}"{description}, shorten <=6pt, shorten >=6pt, Rightarrow, from=3-1, to=1-3]
	\arrow["{\rm{inl}}"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

## Suspensions as pushouts

The [[suspension]] of a type $A$ can be expressed as the
`Pushout`{.Agda} of the span $\top \ot A \to \top$:

~~~{.quiver}
\[\begin{tikzcd}
	C && \top \\
	\\
	\top && {\rm{Pushout}}
	\arrow["{\rm{!}}", from=1-1, to=1-3]
	\arrow["{\rm{!}}"', from=1-1, to=3-1]
	\arrow["{\rm{inr}}", from=1-3, to=3-3]
	\arrow["{\rm{commutes}}"{description}, shorten <=6pt, shorten >=6pt, Rightarrow, from=3-1, to=1-3]
	\arrow["{\rm{inl}}"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

There is only one element of `⊤`{.Agda}, and hence only one choice for
the function projecting into `⊤`{.Agda} - `const tt`{.Agda}.

If one considers the structure we're creating, it becomes very obvious
that this is equivalent to suspension - because both of our non-path
constructors have input `⊤`{.Agda}, they're indistinguishable from
members of the pushout; therefore, we take the `inl`{.Agda} and
`inr`{.Agda} to `N`{.Agda} and `S`{.Agda} respectively. Likewise, we
take `glue`{.Agda} to `merid`{.Agda}.

```agda
Susp→Pushout-⊤←A→⊤ : Susp A → Pushout A (λ _ → tt) (λ _ → tt)
Susp→Pushout-⊤←A→⊤ north       = inl tt
Susp→Pushout-⊤←A→⊤ south       = inr tt
Susp→Pushout-⊤←A→⊤ (merid x i) = glue x i

Pushout-⊤←A→⊤-to-Susp : Pushout A (λ _ → tt) (λ _ → tt) → Susp A
Pushout-⊤←A→⊤-to-Susp (inl tt)   = north
Pushout-⊤←A→⊤-to-Susp (inr tt)   = south
Pushout-⊤←A→⊤-to-Susp (glue c i) = merid c i
```

So we then have:

```agda
Susp≃pushout : Susp A ≃ Pushout A (λ _ → tt) (λ _ → tt)
Susp≃pushout = (Susp→Pushout-⊤←A→⊤ , is-iso→is-equiv iso-pf) where
```

<details><summary> We then verify that our two functions above are in
fact inverse equivalences. This is entirely `refl`{.Agda}, due to the
noted similarities in structure.</summary>

```agda
  open is-iso

  iso-pf : is-iso Susp→Pushout-⊤←A→⊤
  iso-pf .from = Pushout-⊤←A→⊤-to-Susp
  iso-pf .rinv (inl x)    = refl
  iso-pf .rinv (inr x)    = refl
  iso-pf .rinv (glue c i) = refl

  iso-pf .linv north       = refl
  iso-pf .linv south       = refl
  iso-pf .linv (merid x i) = refl
```

</details>

## The universal property of pushouts

To formulate the universal property of a pushout, we first introduce
**cocones**.  A `Cocone`{.Agda}, given a type `D`{.Agda} and a span:

~~~{.quiver}
\[\begin{tikzcd}
	A & C & B
	\arrow["f"', from=1-2, to=1-1]
	\arrow["g", from=1-2, to=1-3]
\end{tikzcd}\]
~~~

consists of functions $i : A \to D$, $j : B \to D$, and a homotopy $h :
(c : C) \to i (f c) \is j (g c)$, forming:

~~~{.quiver}
\[\begin{tikzcd}
	C && B \\
	\\
	A && D
	\arrow["g", from=1-1, to=1-3]
	\arrow["f"', from=1-1, to=3-1]
	\arrow["j", from=1-3, to=3-3]
	\arrow["h"{description}, shorten <=6pt, shorten >=6pt, Rightarrow, from=3-1, to=1-3]
	\arrow["i"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~


One can then note the similarities between this definition, and our
previous `Pushout`{.Agda} definition. We define the type of
`Cocone`{.Agda}s as:

```agda
Cocone : {C A B : Type} → (f : C → A) → (g : C → B) → (D : Type) → Type
Cocone {C} {A} {B} f g D =
  Σ[ i ∈ (A → D) ]
  Σ[ j ∈ (B → D) ]
  ((c : C) → i (f c) ≡ j (g c))
```

We can then show that the canonical `Cocone`{.Agda} consisting of a
`Pushout`{.Agda} is the universal `Cocone`{.Agda}.

```agda
Pushout-is-universal-cocone
  : ∀ {f : C → A} {g : C → B} → (Pushout C f g → X) ≃ Cocone f g X
Pushout-is-universal-cocone {C} {X} {f} {g} = to , is-iso→is-equiv iso-pc where
```

<details><summary> Once again we show that the above is an equivalence;
this proof is essentially a transcription of Lemma 6.8.2 in the
[HoTT](HoTT.html) book, and again mostly reduces to `refl`{.Agda}.
</summary>

```agda
  open is-iso

  to : (Pushout C f g → X) → Cocone f g X
  to t = t ∘ inl , t ∘ inr , ap t ∘ glue

  iso-pc : is-iso to
  iso-pc .from (l , r , g) (inl x)    = l x
  iso-pc .from (l , r , g) (inr x)    = r x
  iso-pc .from (l , r , g) (glue c i) = g c i

  iso-pc .rinv _ = refl
  iso-pc .linv _ = funext λ where
    (inl y) → refl
    (inr y) → refl
    (glue c i) → refl
```

</details>
