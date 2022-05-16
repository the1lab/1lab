```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Colimit.Base
open import Cat.Instances.Functor
open import Cat.Diagram.Initial
open import Cat.Functor.Adjoint
open import Cat.Instances.Comma
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning as Cat

module Cat.Functor.Kan where
```

<!--
```agda
private
  variable
    o ℓ : Level
    C C′ D : Precategory o ℓ
  kan-lvl : ∀ {o ℓ o′ ℓ′ o′′ ℓ′′} {C : Precategory o ℓ} {C′ : Precategory o′ ℓ′} {D : Precategory o′′ ℓ′′}
          → Functor C D → Functor C C′ → Level
  kan-lvl {a} {b} {c} {d} {e} {f} _ _ = a ⊔ b ⊔ c ⊔ d ⊔ e ⊔ f
```
-->

# Kan extensions

Suppose we have a functor $F : \ca{C} \to \ca{D}$, and a functor $p :
\ca{C} \to \ca{C}'$ --- perhaps to be thought of as a [full subcategory]
inclusion, where $\ca{C}'$ is a completion of $\ca{C}$, but the
situation applies just as well to any pair of functors --- which
naturally fit into a commutative diagram

[full subcategory]: Cat.Functor.FullSubcategory.html

~~~{.quiver}
\[\begin{tikzcd}
  \mathcal{C} && \mathcal{D} \\
  \\
  {\mathcal{C}'}
  \arrow["F", from=1-1, to=1-3]
  \arrow["p"', from=1-1, to=3-1]
\end{tikzcd}\]
~~~

but as we can see this is a particularly sad commutative diagram; it's
crying out for a third edge $\ca{C}' \to \ca{D}$

~~~{.quiver}
\[\begin{tikzcd}
  \mathcal{C} && \mathcal{D} \\
  \\
  {\mathcal{C}'}
  \arrow["F", from=1-1, to=1-3]
  \arrow["p"', from=1-1, to=3-1]
  \arrow[dashed, from=3-1, to=1-3]
\end{tikzcd}\]
~~~

extending $F$ to a functor $\ca{C}' \to \ca{D}$. If there exists an
_universal_ such extension (we'll define what "universal" means in just
a second), we call it the **left Kan extension** of $F$ along $p$, and
denote it $\Lan_p F$. Such extensions do not come for free (in a sense
they're pretty hard to come by), but concept of Kan extension can be
used to rephrase the definition of both [limit] and [adjoint functor].

[limit]: Cat.Diagram.Limit.Base.html
[adjoint functor]: Cat.Functor.Adjoint.html

A left Kan extension $\Lan_p F$ is equipped with a natural
transformation $\eta : F \To \Lan_p F \circ p$ witnessing the
("directed") commutativity of the triangle (so that it need not commute
on-the-nose) which is universal among such transformations; Meaning that
if $M : \ca{C'} \to \ca{D}$ is another functor with a transformation
$\alpha : M \To M \circ p$, there is a unique natural transformation
$\sigma : \Lan_p F \To M$ which commutes with $\alpha$.

Note that in general the triangle commutes "weakly", but when $p$ is
[fully faithful] and $\ca{D}$ is [cocomplete], $\Lan_p F$ genuinely extends
$p$, in that $\eta$ is a natural isomorphism.

[fully faithful]: Cat.Functor.Base.html#ff-functors
[cocomplete]: Cat.Diagram.Colimit.Base.html#cocompleteness

```agda
record Lan (p : Functor C C′) (F : Functor C D) : Type (kan-lvl p F) where
  field
    Ext : Functor C′ D
    eta : F => Ext F∘ p
```

Universality of `eta`{.Agda} is witnessed by the following fields, which
essentially say that, in the diagram below (assuming $M$ has a natural
transformation $\alpha$ witnessing the same "directed commutativity"
that $\eta$ does for $\Lan_p F$), the 2-cell exists and is unique.

~~~{.quiver}
\[\begin{tikzcd}
  C && D \\
  \\
  {C'}
  \arrow["F", from=1-1, to=1-3]
  \arrow["p"', from=1-1, to=3-1]
  \arrow[""{name=0, anchor=center, inner sep=0}, "{\mathrm{Lan}_pF}"{description}, curve={height=-12pt}, from=3-1, to=1-3]
  \arrow[""{name=1, anchor=center, inner sep=0}, "M"{description}, curve={height=12pt}, from=3-1, to=1-3]
  \arrow[shorten <=6pt, shorten >=4pt, Rightarrow, from=0, to=1]
\end{tikzcd}\]
~~~

```agda
    σ : {M : Functor C′ D} (α : F => M F∘ p) → Ext => M
    σ-comm : {M : Functor C′ D} {α : F => M F∘ p} → whiskerl (σ α) ∘nt eta ≡ α
    σ-uniq : {M : Functor C′ D} {α : F => M F∘ p} {σ′ : Ext => M}
           → α ≡ whiskerl σ′ ∘nt eta
           → σ α ≡ σ′
```

## Ubiquity

The elevator pitch for Kan extensions is that "all concepts are Kan
extensions". The example we will give here is that, if $F \dashv G$ is
an adjunction, then $(G, \eta)$ gives $\Lan_F(\id{Id})$. This isn't
exactly enlightening: adjunctions and Kan extensions have very different
vibes, but the latter concept _is_ a legitimate generalisation.

<!--
```agda
module _ {F : Functor C D} {G : Functor D C} (adj : F ⊣ G) where
  open Lan
  private
    module F = Functor F
    module G = Functor G
    module C = Cat C
    module D = Cat D
  open _⊣_ adj
  open _=>_
```
-->

```agda
  adjoint→lan : Lan F Id
  adjoint→lan .Ext = G
  adjoint→lan .eta = unit
```

The proof is mostly pushing symbols around, and the calculation is
available below unabridged. In components, $\sigma_x$ must give,
assuming a map $\alpha : \id{Id} \To MFx$, a map $Gx \to Mx$. The
transformation we're looking for arises as the composite

$$
Gx \xto{\alpha} MFGx \xto{M\epsilon} Mx\text{,}
$$

where uniqueness and commutativity follows from the triangle identities
`zig`{.Agda} and `zag`{.Agda}.

```agda
  adjoint→lan .σ {M} α .η x = M .Functor.F₁ (counit.ε _) C.∘ α .η (G.₀ x)
  adjoint→lan .σ {M} nt .is-natural x y f =
    (M.₁ (counit.ε _) C.∘ nt .η _) C.∘ G.₁ f            ≡⟨ C.pullr (nt .is-natural _ _ _) ⟩
    M.₁ (counit.ε _) C.∘ M.₁ (F.₁ (G.₁ f)) C.∘ nt .η _  ≡⟨ M.extendl (counit.is-natural _ _ _) ⟩
    M.₁ f C.∘ M.₁ (counit.ε _) C.∘ nt .η _              ∎
    where module M = Func M

  adjoint→lan .σ-comm {M} {α} = Nat-path λ _ →
    (M.₁ (counit.ε _) C.∘ α.η _) C.∘ unit.η _              ≡⟨ C.pullr (α.is-natural _ _ _) ⟩
    M.₁ (counit.ε _) C.∘ M.₁ (F.F₁ (unit .η _)) C.∘ α.η _  ≡⟨ M.cancell zig ⟩
    α.η _                                                  ∎
    where module α = _=>_ α
          module M = Func M

  adjoint→lan .σ-uniq {M} {α} {σ'} p = Nat-path λ x →
    M.₁ (counit.ε _) C.∘ α.η _                ≡⟨ ap (_ C.∘_) (ap (λ e → e .η _) p) ⟩
    M.₁ (counit.ε _) C.∘ σ' .η _ C.∘ unit.η _ ≡⟨ C.extendl (sym (σ' .is-natural _ _ _)) ⟩
    σ' .η _ C.∘ G.₁ (counit.ε _) C.∘ unit.η _ ≡⟨ C.elimr zag ⟩
    σ' .η x                                   ∎
    where module α = _=>_ α
          module M = Func M
```

# A formula

In the cases where $\ca{C}, \ca{D}$ are "small enough" and $\ca{E}$ is
"cocomplete enough", the left Kan extension of _any_ functor $F : \ca{C}
\to \ca{E}$ along _any_ functor $K : \ca{C} \to \ca{D}$ exists, and is
computed as a colimit in $\ca{E}$. The size concerns here are
unavoidable, so let's be explicit about them: Suppose that $\ca{E}$
admits colimits of [$\kappa$-small diagrams], e.g. because it is
$\sets_\kappa$. Then the category $\ca{C}$ must be $\kappa$-small, and
$\ca{D}$ must be locally $\kappa$-small, i.e. its Hom-sets must live in
the $\kappa$th universe.

[$\kappa$-small diagrams]: 1Lab.intro.html#universes-and-size-issues

<!--
```agda
module _
  {o o′ ℓ κ} {C : Precategory κ κ} {D : Precategory o′ κ} {E : Precategory o ℓ}
  (colim : is-cocomplete κ κ E)
  (F : Functor C E)
  (K : Functor C D)
  where
  private
    module C = Cat C
    module D = Cat D
    module E = Cat E
    module F = Func F
    module K = Func K
    open Cocone-hom
    open Initial
    open Functor
    open Cocone
    open Lan
    open ↓Obj
    open ↓Hom
```
-->

The size restrictions on $\ca{C}$ and $\ca{D}$ ensure that the [comma
category] $K \searrow d$ is $\kappa$-small, so that $\ca{E}$ has a
colimit for it. The objects of this category can be considered
"approximations of $d$ coming from $\ca{C}$", so the colimit over this
category is a "best approximation of $d$"! The rest of the computation
is "straightforward" in the way that most category-theoretic
computations are: it looks mighty complicated from the outside, but when
you're actually working them out, there's only one step you can take at
each point. Agda's goal-and-context display guides you the whole way.

[comma category]: Cat.Instances.Comma.html

```agda
  lan-approximate : ∀ {d e} (f : D.Hom d e) → Cocone (F F∘ Dom K (const! d))
  lan-approximate {e = e} f .coapex = colim (F F∘ Dom K (const! e)) .bot .coapex
  lan-approximate {e = e} f .ψ x =
    colim (F F∘ Dom K (const! e)) .bot .ψ (record { map = f D.∘ x .map })
  lan-approximate {e = e} f .commutes {x} {y} h =
    colim (F F∘ Dom K (const! e)) .bot .commutes (record { sq = path })
    where abstract
      path : (f D.∘ y .map) D.∘ K.₁ (h .α) ≡ D.id D.∘ (f D.∘ x .map)
      path =
        (f D.∘ y .map) D.∘ K.₁ (h .α) ≡⟨ D.pullr (h .sq) ⟩
        f D.∘ D.id D.∘ x .map         ≡⟨ solve D ⟩
        D.id D.∘ (f D.∘ x .map)       ∎

  cocomplete→lan : Lan K F
  cocomplete→lan = lan where
    diagram : ∀ d → Functor (K ↘ d) E
    diagram d = F F∘ Dom K (const! d)

    approx = lan-approximate
```

Our extension will associate to each object $d$ the colimit of

$$
(K \searrow d) \xto{\id{Dom}} C \xto{F} E\text{,}
$$

where $\id{Dom}$ is the functor which projects out the *dom*ain of each
object of $K \searrow d$. Now, we must also associate _arrows_ $f : d
\to e \in \ca{D}$ to arrows between the respective colimits of $d$ and
$e$. What we note is that any arrow $f : d \to e$ displays (the colimit
associated with) $e$ as a cocone under $d$, as can be seen in the
computation of `approx`{.Agda} above.

Our functor can then take an arrow $f : d \to e$ to the uniqueness arrow
from $\colim(d) \to \colim(e)$ (punning $d$ and $e$ for their respective
diagrams), which exists because $\colim(d)$ is initial. Uniqueness of
this arrow ensures that this assignment is functorial --- but as the
functoriality proof is (to use a technical term) goddamn nasty, we leave
it hidden from the page.

```agda
    func : Functor D E
    func .F₀ d = colim (diagram d) .bot .coapex
    func .F₁ {d} {e} f = colim (diagram d) .has⊥ (approx f) .centre .hom
```

<!--
```agda
    func .F-id {d} = path where abstract
      path : func .F₁ (D.id {x = d}) ≡ E.id
      path = ap hom $ colim (diagram d) .has⊥ (approx D.id) .paths
        (cocone-hom E.id (λ o → E.idl _
                         ∙ ap (colim (diagram d) .bot .ψ)
                              (↓Obj-path _ _ refl refl (sym (D.idl _)))))
    func .F-∘ {d} {e} {f} g h = path where abstract
      path : func .F₁ (g D.∘ h) ≡ func .F₁ g E.∘ func .F₁ h
      path = ap hom $ colim (diagram d) .has⊥ (approx _) .paths
        (cocone-hom _ λ o →
            E.pullr (colim (diagram d) .has⊥ (approx h) .centre .commutes _)
          ∙ colim (diagram e) .has⊥ (approx g) .centre .commutes _
          ∙ ap (colim (diagram f) .bot .ψ)
               (↓Obj-path _ _ refl refl (D.assoc _ _ _)))

    open _=>_
```
-->

It remains to show that our extension functor admits a natural
transformation (with components) $Fx \to \colim(Fx)$, but we can take
these arrows to be the colimit coprojections `ψ`{.Agda}; The factoring
natural transformation `σ`{.Agda} is given by eliminating the colimit,
which ensures commutativity and uniqueness. We leave the rest of the
computation in this `<details>`{.html} tag, for the interested reader.

<details>
<summary>
Fair advance warning that the computation here doesn't have any further comments.
</summary>

```agda
    lan : Lan K F
    lan .Ext = func
    lan .eta .η x = colim (diagram (K.₀ x)) .bot .ψ (record { map = D.id })

    lan .σ {M} α .η x = colim (diagram x) .has⊥ cocone′ .centre .hom
      where
        module M = Func M

        cocone′ : Cocone _
        cocone′ .coapex = M.₀ x
        cocone′ .ψ ob = M.₁ (ob .map) E.∘ α .η _
        cocone′ .commutes {x} {y} f =
          (M.₁ (y .map) E.∘ α .η _) E.∘ F.₁ (f .↓Hom.α)      ≡⟨ E.pullr (α .is-natural _ _ _) ⟩
          M.₁ (y .map) E.∘ M.₁ (K.₁ (f .↓Hom.α)) E.∘ α .η _  ≡⟨ M.pulll (f .↓Hom.sq ∙ D.idl _) ⟩
          M.₁ (x .map) E.∘ α .η _                            ∎

    lan .eta .is-natural x y f = sym $
        colim (diagram (K.₀ x)) .has⊥ (approx (K.₁ f)) .centre .commutes _
      ∙ sym (colim (diagram (K.₀ y)) .bot .commutes
            (record { sq = D.introl refl ∙ ap₂ D._∘_ refl (sym D.id-comm) }))

    lan .σ {M} α .is-natural x y f =
      ap hom $ is-contr→is-prop (colim (diagram x) .has⊥ cocone′)
        (cocone-hom _ λ o → E.pullr (colim (diagram x) .has⊥ (approx f) .centre .commutes _)
                          ∙ colim (diagram y) .has⊥ _ .centre .commutes _)
        (cocone-hom _ λ o → E.pullr (colim (diagram x) .has⊥ _ .centre .commutes _)
                          ∙ M.pulll refl)
      where
        module M = Func M

        cocone′ : Cocone _
        cocone′ .coapex = M.₀ y
        cocone′ .ψ x = _
        cocone′ .commutes {x} {y} f =
            E.pullr (α .is-natural _ _ _)
          ∙ M.pulll (D.pullr (f .↓Hom.sq ∙ D.idl _))

    lan .σ-comm {M = M} =
      Nat-path λ x → colim (diagram (K.₀ x)) .has⊥ _  .centre .commutes _ ∙ M.eliml refl
      where module M = Func M

    lan .σ-uniq {M = M} {α} {σ'} path = Nat-path λ x →
      ap hom $ colim (diagram _) .has⊥ _ .paths
        (cocone-hom _ λ o → sym $
            ap₂ E._∘_ refl (ap (λ e → e .η _) path)
          ∙ E.pulll (sym (σ' .is-natural _ _ _))
          ∙ E.pullr ( colim _ .has⊥ _ .centre .commutes _
                    ∙ ap (colim (diagram x) .bot .ψ)
                         (↓Obj-path _ _ refl refl (D.idr _))))
```
</details>

A useful result about this calculation of $\Lan_F(G)$ is that, if $F$ is
fully faithful, then $\Lan_F(G) \circ F \cong G$ --- the left Kan
extension along a fully-faithful functor does actually _extend_.

```agda
  private module Fn = Cat Cat[ C , E ]
  open _=>_

  ff-lan-ext : is-fully-faithful K → cocomplete→lan .Ext F∘ K Fn.≅ F

  ff-lan-ext ff = Fn._Iso⁻¹ (Fn.invertible→iso (cocomplete→lan .eta) inv) where
    inv′ : ∀ x → E.is-invertible (cocomplete→lan .eta .η x)
    inv′ x = E.make-invertible to invl invr where
      cocone′ : Cocone _
      cocone′ .coapex = F.₀ x
      cocone′ .ψ ob = F.₁ (equiv→inverse ff (ob .map))
      cocone′ .commutes {x = y} {z} f =
        F.collapse (fully-faithful→faithful {F = K} ff
          ( K .Functor.F-∘  _ _
          ∙ ap₂ D._∘_ (equiv→section ff _) refl
          ∙ f .sq
          ∙ D.idl _
          ∙ sym (equiv→section ff _)))

      to : E.Hom _ (F.₀ x)
      to = colim _ .has⊥ cocone′ .centre .hom

      invl : cocomplete→lan .eta .η x E.∘ to ≡ E.id
      invl = ap hom $ is-contr→is-prop
        (colim _ .has⊥ (colim (F F∘ Dom K (const! _)) .bot))
        (cocone-hom _ λ o →
            E.pullr (colim _ .has⊥ cocone′ .centre .commutes _)
          ∙ colim _ .bot .commutes
              (record { sq = ap (D.id D.∘_) (equiv→section ff _) }))
        (cocone-hom _ λ o → E.idl _)

      invr : to E.∘ cocomplete→lan .eta .η x ≡ E.id
      invr = colim _ .has⊥ cocone′ .centre .commutes _
           ∙ F.elim (fully-faithful→faithful {F = K} ff
                      (equiv→section ff _ ∙ sym K.F-id))

    inv : Fn.is-invertible (cocomplete→lan .eta)
    inv = componentwise-invertible→invertible (cocomplete→lan .eta) inv′
```
