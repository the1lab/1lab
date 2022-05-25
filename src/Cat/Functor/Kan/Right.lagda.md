```agda
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Functor
open import Cat.Diagram.Duals
open import Cat.Functor.Kan
open import Cat.Prelude

module Cat.Functor.Kan.Right where
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

# Right Kan extensions

Dually to our setup for a [left Kan extension], we have **right Kan
extensions**: The (suitably weakly) [terminal] solution to the problem of
lifting a functor $F : \ca{C} \to \ca{D}$ along a functor $p : \ca{C}'
\to \ca{C}$. We picture the situation as in the following commutative
diagram:

[left Kan extension]: Cat.Functor.Kan.html
[terminal]: Cat.Diagram.Terminal.html

~~~{.quiver}
\[\begin{tikzcd}
  {\mathcal{C}} && {\mathcal{D}} \\
  \\
  {\mathcal{C}'}
  \arrow["F", from=1-1, to=1-3]
  \arrow["p"', from=1-1, to=3-1]
  \arrow[""{name=0, anchor=center, inner sep=0}, "{\mathrm{Ran}_pF}"{description}, curve={height=-12pt}, from=3-1, to=1-3]
  \arrow[""{name=1, anchor=center, inner sep=0}, "M"{description}, curve={height=12pt}, from=3-1, to=1-3]
  \arrow[shorten <=4pt, shorten >=4pt, Rightarrow, from=1, to=0]
\end{tikzcd}\]
~~~

Note the same warnings about "weak, directed" commutativity as for [left
Kan extensions] apply here, too. Rather than either of the triangles
commuting on the nose, we have natural transformations $\eps$ witnessing
their commutativity.

```agda
record Ran (p : Functor C C′) (F : Functor C D) : Type (kan-lvl p F) where
  field
    Ext : Functor C′ D
    eps : Ext F∘ p => F

    σ : {M : Functor C′ D} (α : M F∘ p => F) → M => Ext
    σ-comm : {M : Functor C′ D} {β : M F∘ p => F} → eps ∘nt whiskerl (σ β) ≡ β
    σ-uniq : {M : Functor C′ D} {β : M F∘ p => F} {σ′ : M => Ext}
           → β ≡ eps ∘nt whiskerl σ′
           → σ β ≡ σ′
```

The first thing we'll verify is that this construction is indeed dual to
the left Kan extension. This is straightforward enough to do, but we
have some administrative noise from all the opposite categories getting
in the way.

```agda
module _ (p : Functor C C′) (F : Functor C D) where
  open Ran
  open _=>_

  Co-lan→Ran : Lan (Functor.op p) (Functor.op F) -> Ran p F
  Co-lan→Ran lan = ran where
    module lan = Lan lan
    ran : Ran p F
    ran .Ext = Functor.op lan.Ext
    ran .eps .η x = lan.eta .η x
    ran .eps .is-natural x y f = sym (lan.eta .is-natural y x f)

    ran .σ {M = M} α = op (lan.σ α′) where
      α′ : Functor.op F => Functor.op M F∘ Functor.op p
      α′ .η x = α .η x
      α′ .is-natural x y f = sym (α .is-natural y x f)

    ran .σ-comm = Nat-path λ x → ap (λ e → e .η _) lan.σ-comm
    ran .σ-uniq {M = M} {σ′ = σ′} p =
      Nat-path λ x → ap (λ e → e .η x) $ lan.σ-uniq {σ′ = σ′op} $ Nat-path λ x →
        ap (λ e → e .η x) p
      where
        σ′op : lan.Ext => Functor.op M
        σ′op .η x = σ′ .η x
        σ′op .is-natural x y f = sym (σ′ .is-natural y x f)
```

## Computation

Using the helper `Co-lan→Ran`{.Agda} defined above and the formula for
computing _left_ Kan extensions, we can formulate a condition for the
existence of right Kan extensions based on the size and completeness of
the categories involved. If $\ca{E}$ admits limits of [$\kappa$-small
diagrams], $\ca{C}$ is $\kappa$-small, and $\ca{D}$ is locally
$\kappa$-small, then for any $p : \ca{C} \to \ca{D}$ and $F : \ca{D} \to
\ca{E}$, the right Kan extension $\Ran_p F$ exists.

[$\kappa$-small diagrams]: 1Lab.intro.html#universes-and-size-issues

```agda
module _
  {o o′ ℓ κ} {C : Precategory κ κ} {D : Precategory o′ κ} {E : Precategory o ℓ}
  (lims : is-complete κ κ E) (p : Functor C D) (F : Functor C E)
  where

  complete→ran : Ran p F
  complete→ran =
    Co-lan→Ran p F $
      cocomplete→lan
        (λ F → Co-limit→Colimit (E ^op) (lims (Functor.op F)))
        (Functor.op p) (Functor.op F)
```

As before, it's impossible to cheat the size limitations for computing
Kan extensions as (co)limits, but this does not preclude the existence
of extensions in other situations.
