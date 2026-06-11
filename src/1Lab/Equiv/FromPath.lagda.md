---
description: |
  We show how to turn a path into an equivalence, in a computationally
  efficient manner, using cubical methods.
---

<!--
```agda
open import 1Lab.Path.Cartesian
open import 1Lab.Path.Reasoning
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.Equiv.FromPath {ℓ} (P : (i : I) → Type ℓ) where
```

# Transport is an equivalence

Showing that [[transport]] is an [[equivalence]] could be done
essentially by [[path induction]], since the `transp`{.Agda} function
associated to a line of types $P$ is identical to the identity function
over $P$. This is a very straightforward argument:

```agda
private
  bad-transport-is-equiv : is-equiv (transp P i0)
  bad-transport-is-equiv = transp (λ i → is-equiv (coe0→i P i)) i0 id-equiv
```

Because `is-equiv`{.Agda} is a [[proposition]], the specific
construction does not matter in any mathematical context. However, in an
intensional proof assistant, we *do* still need to care about the
specific construction of the inverse, especially if we intend to perform
computations with that inverse. We would expect that the inverse of
transporting along $P$ is simply transporting along the path inverse of
$P$, but this is *not* the construction we obtain by the abstract
argument above. Instead, that construction introduces an extraneous
`transport`{.Agda} along `refl`{.Agda}:

```agda
  _ : equiv→inverse bad-transport-is-equiv
    ≡ transport refl ∘ transp (λ i → P (~ i)) i0
  _ = refl
```

We can instead construct a direct proof that `transp`{.Agda} along $P$
is an equivalence, giving us control over the unfolding of the inverse.
We start by naming all the relevant endpoints:

```agda
  A B : Type ℓ
  A = P i0
  B = P i1

  f : A → B
  f x = coe0→1 P x

  g : B → A
  g y = coe1→0 P y
```

We can then directly prove that $f$ and $g$ are inverses, fixing the
computation of the inverse. Since having a two-sided inverse is enough
to imply that a function is an equivalence, we would be done; however,
that general theorem relies on replacing the unit $\eta : gf \sim \id$
by something which satisfies the triangle identities, whereas in this
case we can show by a direct cubical argument that our $\eta$ *already*
satisfies the triangle identities.

```agda
  ε : (y : B) → f (g y) ≡ y
  ε y i = coe P i i1 (coe P i1 i y)

  η : (x : A) → g (f x) ≡ x
  η x i = coe P (~ i) i0 (coe P i0 (~ i) x)
```

It will suffice to give a square $\zeta_1$ with the boundary below,
since in that case (assuming we have $y : B$ and the data $x : A$,
$\alpha : f x \is y$ of a fibre $f^y$) we can construct $\beta : g y \is
x$ as the composite $$ g~ y \xto{\ap{g}{\alpha}} g~(f~ x) \xto{\eta~ x}
x $$, and glue $\zeta_1$ along `∙-filler'`{.Agda} to give us the
necessary square identifying $\ap{f}{\beta}$, $\eps$ and $\alpha$.

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  {f~(g~(f~x))} \&\& {f~x} \\
  \\
  {f~x} \&\& {f~x}
  \arrow["{\eps~(f~x)}", from=1-1, to=1-3]
  \arrow["{f~(\eta~x~i)}"', from=1-1, to=3-1]
  \arrow["{f~x}", from=1-3, to=3-3]
  \arrow["{f~x}"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

```agda
  module _ (y : B) (x : A) (α : f x ≡ y) where
    β : g y ≡ x
    β = ap g (sym α) ∙ η x
```

<details>
<summary>
Gluing `ζ₁`{.Agda} to obtain the necessary `ζ`{.Agda} is simple enough.

```agda
    ζ₁ : Square (ap f (η x)) (ε (f x)) refl refl
    ζ : Square (ap f β) (ε y) α refl
    ζ i j = hcomp (∂ i ∨ ∂ j) λ where
      k (k = i0) → ζ₁ i j

      k (i = i0) → ε (α k) j
      k (i = i1) → α (k ∧ j)
      k (j = i0) → f (∙-filler' (ap g (sym α)) (η x) k i)
      k (j = i1) → α k
```

However, since constructing `ζ₁`{.Agda} boils down to slapping together
an absurd number of `coe`{.Agda}s, we leave it in this
`<details>`{.html} tag for the curious reader.</summary>

```agda
    ζ₁ i j = comp P (∂ i ∨ ∂ j) λ where
      k (k = i0) → η x (i ∨ ~ j)

      k (i = i0) → coe P j k (coe-path P (λ j → coe0→i P j x) k j i)
      k (j = i0) → coe P j k (coe-path P (λ j → coe0→i P j x) k j i)

      k (i = i1) → coe P i0 k x
      k (j = i1) → hcomp (∂ i ∨ ∂ k) λ where
        j (j = i0) → coe-path P (λ j → coe P k j (coe0→i P k x)) i1 k i

        j (i = i1) → coei→i P k (coe0→i P k x) j
        j (i = i0) → coe P i1 k (coe P k i1 (coe0→i P k x))

        j (k = i0) → η x i
        j (k = i1) → f x
```

</details>

We can now simply package the components up.

```agda
transp-is-equiv : is-equiv (transp P i0)
transp-is-equiv .is-eqv y .centre = record { snd = ε y }
transp-is-equiv .is-eqv y .paths (x , α) i = record
  { snd = ζ y x α i }

line→equiv : A ≃ B
line→equiv .fst = transp P i0
line→equiv .snd = transp-is-equiv
```

At the level of points and paths, this construction computes very
nicely, with the only hitch being a stray reflexivity path added to the
unit. The witness for the triangle identity is our `ζ`{.Agda}, and so
made up of quite a few `hcomp`{.Agda}s, but still much better (by virtue
of the unit and counit being simpler) than is possible by simply
transporting the proof that the identity is an equivalence.

```agda
_ : equiv→inverse transp-is-equiv ≡ g
_ = refl

_ : equiv→counit transp-is-equiv ≡ transport⁻transport (λ i → P (~ i))
_ = refl

_ : ∀ {x}
  → equiv→unit transp-is-equiv x
  ≡ refl ∙ transport⁻transport (λ i → P i) x
_ = refl
```
