```agda
open import Cat.Instances.Functor.Compose
open import Cat.Instances.Functor
open import Cat.Functor.Kan.Left
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
lifting a functor $F : \cC \to \cD$ along a functor $p : \cC'
\to \cC$. We picture the situation as in the following commutative
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
record is-right-kan-extension
  (p : Functor C C′) (F : Functor C D) (Ext : Functor C′ D) : Type (kan-lvl p F) where
  no-eta-equality
  field
    eps : Ext F∘ p => F

    σ : {M : Functor C′ D} (α : M F∘ p => F) → M => Ext
    σ-comm : {M : Functor C′ D} {β : M F∘ p => F} → eps ∘nt (σ β ◂ p) ≡ β
    σ-uniq : {M : Functor C′ D} {β : M F∘ p => F} {σ′ : M => Ext}
           → β ≡ eps ∘nt (σ′ ◂ p)
           → σ β ≡ σ′

  σ-uniq₂
    : {M : Functor C′ D} (β : M F∘ p => F) {σ₁′ σ₂′ : M => Ext}
    → β ≡ eps ∘nt (σ₁′ ◂ p)
    → β ≡ eps ∘nt (σ₂′ ◂ p)
    → σ₁′ ≡ σ₂′
  σ-uniq₂ β p q = sym (σ-uniq p) ∙ σ-uniq q

record Ran (p : Functor C C′) (F : Functor C D) : Type (kan-lvl p F) where
  no-eta-equality
  field
    Ext : Functor C′ D
    has-right-kan-extension : is-right-kan-extension p F Ext

  open is-right-kan-extension has-right-kan-extension public
```

The first thing we'll verify is that this construction is indeed dual to
the left Kan extension. This is straightforward enough to do, but we
have some administrative noise from all the opposite categories getting
in the way.

```agda
module _ (p : Functor C C′) (F : Functor C D) where
  open Ran
  open Lan
  open is-right-kan-extension
  open _=>_

  is-co-lan→is-ran
    : ∀ {Ext : Functor (C′ ^op) (D ^op)}
    → is-left-kan-extension (Functor.op p) (Functor.op F) Ext
    → is-right-kan-extension p F (Functor.op Ext)
  is-co-lan→is-ran {Ext = Ext} is-lan = is-ran where
    module is-lan = is-left-kan-extension is-lan

    is-ran : is-right-kan-extension p F (Functor.op Ext)
    is-ran .eps .η x = is-lan.eta .η x
    is-ran .eps .is-natural x y f = sym (is-lan.eta .is-natural y x f)

    is-ran .σ {M = M} α = op (is-lan.σ α′) where
      α′ : Functor.op F => Functor.op M F∘ Functor.op p
      α′ .η x = α .η x
      α′ .is-natural x y f = sym (α .is-natural y x f)

    is-ran .σ-comm = Nat-path λ x → is-lan.σ-comm ηₚ x
    is-ran .σ-uniq {M = M} {σ′ = σ′} p =
      Nat-path λ x → is-lan.σ-uniq {σ′ = σ′op} (Nat-path λ x → p ηₚ x) ηₚ x
      where
        σ′op : Ext => Functor.op M
        σ′op .η x = σ′ .η x
        σ′op .is-natural x y f = sym (σ′ .is-natural y x f)

  Co-lan→Ran : Lan (Functor.op p) (Functor.op F) -> Ran p F
  Co-lan→Ran lan .Ext =
    Functor.op (lan .Ext)
  Co-lan→Ran lan .has-right-kan-extension =
    is-co-lan→is-ran (lan .has-left-kan-extension)
```
