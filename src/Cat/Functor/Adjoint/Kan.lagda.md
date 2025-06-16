<!--
```agda
open import Cat.Functor.Kan.Duality
open import Cat.Functor.Coherence
open import Cat.Instances.Functor
open import Cat.Functor.Kan.Base
open import Cat.Functor.Adjoint
open import Cat.Prelude

import Cat.Functor.Reasoning as Fr
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Functor.Adjoint.Kan where
```

# Adjoints preserve Kan extensions {defines="adjoints-preserve-kan-extensions"}

Let $L \adj R$ be a pair of [[adjoint functors]]. It's well-known that
right adjoints preserve limits[^rapl], and dually that left adjoints
preserve colimits, but it turns out that this theorem can be made a bit
more general: If $G$ is a [[left|left Kan extension]] (resp.
[[right|right Kan extension]]) extension of $F$ along $p$, then $LG$ is
a left extension of $LF$ along $p$: left adjoints preserve left
extensions. This dualises to right adjoints preserving _right_
extensions.

[^rapl]: Here on the 1Lab, we derive the proof that right (resp. left)
adjoints preserve limits (resp. colimits) from _this proof_ that
adjoints preserve Kan extensions. For a more concrete approach to that
proof, we recommend [the nLab's]

[the nLab's]: https://ncatlab.org/nlab/show/adjoints+preserve+%28co-%29limits.

The proof could be given in bicategorical generality: If the triangle
below is a left extension diagram, then the overall pasted diagram is
also a left extension. This is essentially because the $L \dashv R$
adjunction provides a bunch of isomorphisms between natural
transformations, e.g. $(LF \to Mp) \cong (F \to RMp)$, which we can use
to "grow" the original extension diagram.

~~~{.quiver}
\[\begin{tikzcd}
  {\mathcal{C}} && D && A \\
  \\
  {\mathcal{C'}}
  \arrow["p"', from=1-1, to=3-1]
  \arrow["F", from=1-1, to=1-3]
  \arrow[""{name=0, anchor=center, inner sep=0}, "{\mathrm{Lan}_pF}"', from=3-1, to=1-3]
  \arrow[""{name=1, anchor=center, inner sep=0}, "L"', shift right=2, from=1-3, to=1-5]
  \arrow[""{name=2, anchor=center, inner sep=0}, "R"', shift right=3, color={rgb,255:red,137;green,133;blue,142}, from=1-5, to=1-3]
  \arrow["{L\mathrm{Lan}_pF}"', curve={height=18pt}, from=3-1, to=1-5]
  \arrow["\dashv"{anchor=center, rotate=90}, draw=none, from=1, to=2]
  \arrow["\eta"', shorten <=6pt, Rightarrow, from=0, to=1-1]
\end{tikzcd}\]
~~~

<!--
```agda
module
  _ {oc ℓc oc' ℓc' od ℓd oa ℓa}
    {C : Precategory oc ℓc} {C' : Precategory oc' ℓc'} {D : Precategory od ℓd}
    {A : Precategory oa ℓa}
    {p : Functor C C'}
    {F : Functor C D}
    {L : Functor D A} {R : Functor A D}
    (adj : L ⊣ R)
  where
  private
    open _⊣_ adj
    open is-lan
    open _=>_
    module A = Cr A
    module D = Cr D
    module L = Fr L
    module R = Fr R
    module F = Functor F
    module p = Functor p

    LF = L F∘ F
    RL = R F∘ L
    module RL = Functor RL
    module LF = Functor LF
```
-->

```agda
  left-adjoint→preserves-lan : preserves-lan p F L
  left-adjoint→preserves-lan {G} {eta} lan = pres where
```

<!--
```agda
    module l = is-lan lan
    module G = Functor G
    LG = L F∘ G
    module LG = Functor LG

    fixup : ∀ {M : Functor C' A} → (LF => M F∘ p) → F => (R F∘ M) F∘ p
    fixup α .η x = L-adjunct adj (α .η x)
    fixup {M = M} α .is-natural x y f =
      (R.₁ (α .η y) D.∘ unit.η _) D.∘ F.₁ f            ≡⟨ D.pullr (unit.is-natural _ _ _) ⟩
      (R.₁ (α .η y) D.∘ (RL.₁ (F.₁ f)) D.∘ unit.η _)   ≡⟨ D.extendl (R.weave (α .is-natural _ _ _)) ⟩
      R.₁ (M.₁ (p.₁ f)) D.∘ R.₁ (α .η x) D.∘ unit.η _  ∎
      where module M = Functor M
```
-->

It wouldn't fit in the diagram above, but the 2-cell of the larger
diagram is simply the whiskering $L\eta$. Unfortunately, proof
assistants; Our existing definition of whiskering lands in $L(Gp)$, but
we need a natural transformation onto $(LG)p$.

```agda
    pres : is-lan p (L F∘ F) (L F∘ G) (nat-assoc-to (L ▸ eta))
```

Given a 2-cell $\alpha : LF \to Mp$, how do we factor it through $\eta$
as a 2-cell $\sigma : LG \to M$? Well, since the original diagram was an
extension, if we can get our hands on a 2-cell $F \to M'p$, that'll give
us a cell $G \to M'$. Hm: choose $M' = RM$, let $\alpha' : F \to (RM)p$
be the adjunct of $\alpha$, factor it through the original $\eta$ into a
cell $\sigma' : G \to RM$, and let $\sigma : LG \to M$ be its adjunct.

```agda
    pres .σ α .η x = R-adjunct adj (l.σ (fixup α) .η x)
    pres .σ {M = M} α .is-natural x y f =
      (ε _ A.∘ L.₁ (l.σ (fixup α) .η y)) A.∘ LG.₁ f        ≡⟨ A.pullr (L.weave (l.σ (fixup α) .is-natural x y f)) ⟩
      ε _ A.∘ (L.₁ (RM.₁ f) A.∘ L.₁ (l.σ (fixup α) .η x))  ≡⟨ A.extendl (counit.is-natural _ _ _) ⟩
      M.₁ f A.∘ pres .σ α .η x                             ∎
      where module M = Functor M
            module RM = Functor (R F∘ M)
```

And since every part of the process in the preceding paragraph is an
isomorphism, this is indeed a factorisation, and it's unique to boot:
we've shown that $LG$ is the extension of $LF$ along $p$!

<details>
<summary>The details of the calculation is just some more calculation
with natural transformations. We'll leave them here for the intrepid
reader but they will not be elaborated on.
</summary>

```agda
    pres .σ-comm {α = α} = ext λ x →
      (R-adjunct adj (l.σ (fixup α) .η _)) A.∘ L.₁ (eta .η _) ≡⟨ L.pullr (l.σ-comm {α = fixup α} ηₚ _) ⟩
      R-adjunct adj (L-adjunct adj (α .η x))                  ≡⟨ equiv→unit (L-adjunct-is-equiv adj) (α .η x) ⟩
      α .η x                                                  ∎

    pres .σ-uniq {M = M} {α = α} {σ' = σ'} wit = ext λ x →
      R-adjunct adj (l.σ (fixup α) .η x)      ≡⟨ A.refl⟩∘⟨ ap L.₁ (l.σ-uniq lemma ηₚ x) ⟩
      R-adjunct adj (L-adjunct adj (σ' .η x)) ≡⟨ equiv→unit (L-adjunct-is-equiv adj) (σ' .η x) ⟩
      σ' .η x                                 ∎
      where
        module M = Functor M

        σ'' : G => R F∘ M
        σ'' .η x = L-adjunct adj (σ' .η x)
        σ'' .is-natural x y f =
          (R.₁ (σ' .η _) D.∘ unit.η _) D.∘ G.₁ f          ≡⟨ D.pullr (unit.is-natural _ _ _) ⟩
          (R.₁ (σ' .η _) D.∘ (RL.₁ (G.₁ f)) D.∘ unit.η _) ≡⟨ D.extendl (R.weave (σ' .is-natural _ _ _)) ⟩
          R.₁ (M.₁ f) D.∘ R.₁ (σ' .η x) D.∘ unit.η _      ∎

        lemma : fixup α ≡ ((σ'' ◂ p) ∘nt eta)
        lemma = ext λ x →
          R.₁ (α .η x) D.∘ unit.η _                     ≡⟨ ap R.₁ (wit ηₚ _) D.⟩∘⟨refl ⟩
          R.₁ (σ' .η _ A.∘ L.₁ (eta .η _)) D.∘ unit.η _ ≡⟨ ap (D._∘ unit.η _) (R.F-∘ _ _) ∙ D.extendr (sym (unit.is-natural _ _ _)) ⟩
          (R.₁ (σ' .η _) D.∘ unit.η _) D.∘ eta .η x     ∎
```

</details>

## Dually

By duality, right adjoints preserve right extensions.

<!--
```agda
module
  _ {oc ℓc oc' ℓc' od ℓd oa ℓa}
    {C : Precategory oc ℓc} {C' : Precategory oc' ℓc'} {D : Precategory od ℓd}
    {A : Precategory oa ℓa} {p : Functor C C'} {F : Functor C D}
    {L : Functor A D} {R : Functor D A} (adj : L ⊣ R)
  where
```
-->

```agda
  right-adjoint→preserves-ran : preserves-ran p F R
  right-adjoint→preserves-ran {G} {eps} ran = fixed where
    pres-lan = left-adjoint→preserves-lan
      (opposite-adjunction adj)
      (is-ran→is-co-lan _ _ ran)

    module p = is-lan pres-lan
    open is-ran
    open _=>_

    fixed : is-ran p (R F∘ F) (R F∘ G) (nat-assoc-from (R ▸ eps))
    fixed .is-ran.σ {M = M} α = σ' where
      unquoteDecl α' = dualise-into α'
        (Functor.op R F∘ Functor.op F => Functor.op M F∘ Functor.op p)
        α
      unquoteDecl σ' = dualise-into σ' (M => R F∘ G) (p.σ α')

    fixed .is-ran.σ-comm = ext λ x → p.σ-comm ηₚ _
    fixed .is-ran.σ-uniq {M = M} {σ' = σ'} p =
      ext λ x → p.σ-uniq {σ' = dualise! σ'} (reext! p) ηₚ x
```
