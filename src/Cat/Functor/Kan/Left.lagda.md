```agda
open import Cat.Instances.Functor.Compose
open import Cat.Instances.Shape.Terminal
open import Cat.Instances.Functor
open import Cat.Functor.Adjoint
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning as Cat

module Cat.Functor.Kan.Left where
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

# Left Kan extensions

Suppose we have a functor $F : \cC \to \cD$, and a functor $p :
\cC \to \cC'$ --- perhaps to be thought of as a [full subcategory]
inclusion, where $\cC'$ is a completion of $\cC$, but the
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
crying out for a third edge $\cC' \to \cD$

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

extending $F$ to a functor $\cC' \to \cD$. If there exists an
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
if $M : \ca{C'} \to \cD$ is another functor with a transformation
$\alpha : M \To M \circ p$, there is a unique natural transformation
$\sigma : \Lan_p F \To M$ which commutes with $\alpha$.

Note that in general the triangle commutes "weakly", but when $p$ is
[fully faithful] and $\cD$ is [cocomplete], $\Lan_p F$ genuinely extends
$p$, in that $\eta$ is a natural isomorphism.

[fully faithful]: Cat.Functor.Base.html#ff-functors
[cocomplete]: Cat.Diagram.Colimit.Base.html#cocompleteness

```agda
record is-left-kan-extension
  (p : Functor C C′) (F : Functor C D) (Ext : Functor C′ D) : Type (kan-lvl p F) where
  field
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
    σ-comm : {M : Functor C′ D} {α : F => M F∘ p} → (σ α ◂ p) ∘nt eta ≡ α
    σ-uniq : {M : Functor C′ D} {α : F => M F∘ p} {σ′ : Ext => M}
           → α ≡ (σ′ ◂ p) ∘nt eta
           → σ α ≡ σ′
```

We also provide a bundled form of this data.

```agda
record Lan (p : Functor C C′) (F : Functor C D) : Type (kan-lvl p F) where
  field
    Ext : Functor C′ D
    has-left-kan-extension : is-left-kan-extension p F Ext

  open is-left-kan-extension has-left-kan-extension public
```

## Ubiquity

The elevator pitch for Kan extensions is that "all concepts are Kan
extensions". The example we will give here is that, if $F \dashv G$ is
an adjunction, then $(G, \eta)$ gives $\Lan_F(\rm{Id})$. This isn't
exactly enlightening: adjunctions and Kan extensions have very different
vibes, but the latter concept _is_ a legitimate generalisation.

<!--
```agda
module _ {F : Functor C D} {G : Functor D C} (adj : F ⊣ G) where
  open Lan
  open is-left-kan-extension
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
  adjoint→is-lan : is-left-kan-extension F Id G
  adjoint→is-lan .eta = unit
```

The proof is mostly pushing symbols around, and the calculation is
available below unabridged. In components, $\sigma_x$ must give,
assuming a map $\alpha : \rm{Id} \To MFx$, a map $Gx \to Mx$. The
transformation we're looking for arises as the composite

$$
Gx \xto{\alpha} MFGx \xto{M\epsilon} Mx\text{,}
$$

where uniqueness and commutativity follows from the triangle identities
`zig`{.Agda} and `zag`{.Agda}.

```agda
  adjoint→is-lan .σ {M} α .η x = M .Functor.F₁ (counit.ε _) C.∘ α .η (G.₀ x)
  adjoint→is-lan .σ {M} nt .is-natural x y f =
    (M.₁ (counit.ε _) C.∘ nt .η _) C.∘ G.₁ f            ≡⟨ C.pullr (nt .is-natural _ _ _) ⟩
    M.₁ (counit.ε _) C.∘ M.₁ (F.₁ (G.₁ f)) C.∘ nt .η _  ≡⟨ M.extendl (counit.is-natural _ _ _) ⟩
    M.₁ f C.∘ M.₁ (counit.ε _) C.∘ nt .η _              ∎
    where module M = Func M

  adjoint→is-lan .σ-comm {M} {α} = Nat-path λ _ →
    (M.₁ (counit.ε _) C.∘ α.η _) C.∘ unit.η _              ≡⟨ C.pullr (α.is-natural _ _ _) ⟩
    M.₁ (counit.ε _) C.∘ M.₁ (F.F₁ (unit .η _)) C.∘ α.η _  ≡⟨ M.cancell zig ⟩
    α.η _                                                  ∎
    where module α = _=>_ α
          module M = Func M

  adjoint→is-lan .σ-uniq {M} {α} {σ'} p = Nat-path λ x →
    M.₁ (counit.ε _) C.∘ α.η _                ≡⟨ ap (_ C.∘_) (p ηₚ _) ⟩
    M.₁ (counit.ε _) C.∘ σ' .η _ C.∘ unit.η _ ≡⟨ C.extendl (sym (σ' .is-natural _ _ _)) ⟩
    σ' .η _ C.∘ G.₁ (counit.ε _) C.∘ unit.η _ ≡⟨ C.elimr zag ⟩
    σ' .η x                                   ∎
    where module α = _=>_ α
          module M = Func M
```
