```agda
{-# OPTIONS -vtactic.dualise:30 -vtc.unquote.def:10 #-}
open import Cat.Functor.Coherence
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
record is-ran
  (p : Functor C C′) (F : Functor C D) (Ext : Functor C′ D)
  (eps : Ext F∘ p => F)
  : Type (kan-lvl p F) where
  no-eta-equality

  field
    σ : {M : Functor C′ D} (α : M F∘ p => F) → M => Ext
    σ-comm : {M : Functor C′ D} {β : M F∘ p => F} → eps ∘nt (σ β ◂ p) ≡ β
    σ-uniq : {M : Functor C′ D} {β : M F∘ p => F} {σ′ : M => Ext}
           → β ≡ eps ∘nt (σ′ ◂ p)
           → σ β ≡ σ′

  open _=>_ eps renaming (η to ε)

  σ-uniq₂
    : {M : Functor C′ D} (β : M F∘ p => F) {σ₁′ σ₂′ : M => Ext}
    → β ≡ eps ∘nt (σ₁′ ◂ p)
    → β ≡ eps ∘nt (σ₂′ ◂ p)
    → σ₁′ ≡ σ₂′
  σ-uniq₂ β p q = sym (σ-uniq p) ∙ σ-uniq q

record Ran (p : Functor C C′) (F : Functor C D) : Type (kan-lvl p F) where
  no-eta-equality
  field
    Ext     : Functor C′ D
    eps     : Ext F∘ p => F
    has-ran : is-ran p F Ext eps

  module Ext = Functor Ext
  open is-ran has-ran public
```

The first thing we'll verify is that this construction is indeed dual to
the left Kan extension. This is straightforward enough to do, but we
have some administrative noise from all the opposite categories getting
in the way.

<!--
```agda
module _ (p : Functor C C′) (F : Functor C D) where
  open Ran
  open Lan
  open is-ran
  open is-lan
  open _=>_

  co-unit→counit
    : ∀ {G : Functor (C′ ^op) (D ^op)}
    → Functor.op F => G F∘ Functor.op p → Functor.op G F∘ p => F
  counit→co-unit
    : ∀ {G : Functor C′ D}
    → G F∘ p => F
    → Functor.op F => Functor.op G F∘ Functor.op p

  unquoteDef co-unit→counit = define-dualiser co-unit→counit
  unquoteDef counit→co-unit = define-dualiser counit→co-unit
```
-->

```agda
  is-co-lan→is-ran
    : ∀ {G : Functor (C′ ^op) (D ^op)} {eta : Functor.op F => G F∘ Functor.op p}
    → is-lan (Functor.op p) (Functor.op F) G eta
    → is-ran p F (Functor.op G) (co-unit→counit eta)
  is-co-lan→is-ran {G = G} {eta = eta} is-lan = ran where
    module lan = is-lan is-lan

    ran : is-ran p F (Functor.op G) (co-unit→counit eta)
    ran .σ {M = M} α = op (lan.σ α′) where
      unquoteDecl α′ = dualise-into α′
        (Functor.op F => Functor.op M F∘ Functor.op p)
        α

    ran .σ-comm = Nat-path λ x → lan.σ-comm ηₚ x
    ran .σ-uniq {M = M} {σ′ = σ′} p =
      Nat-path λ x → lan.σ-uniq {σ′ = σ′op} (Nat-path λ x → p ηₚ x) ηₚ x
      where unquoteDecl σ′op = dualise-into σ′op _ σ′
```

<!--
```agda
  is-ran→is-co-lan
    : ∀ {Ext : Functor C′ D} {eta : Ext F∘ p => F}
    → is-ran p F Ext eta
    → is-lan (Functor.op p) (Functor.op F) (Functor.op Ext) (counit→co-unit eta)
  is-ran→is-co-lan {Ext = Ext} is-ran = lan where
    module ran = is-ran is-ran

    lan : is-lan (Functor.op p) (Functor.op F) (Functor.op Ext) _
    lan .σ {M = M} α = σ′ where
      unquoteDecl α′ = dualise-into α′ (Functor.op M F∘ p => F) α
      unquoteDecl σ′ = dualise-into σ′ (Functor.op Ext => M) (ran.σ α′)

    lan .σ-comm = Nat-path λ x → ran.σ-comm ηₚ x
    lan .σ-uniq {M = M} {σ′ = σ′} p =
      Nat-path λ x → ran.σ-uniq {σ′ = σ′op} (Nat-path λ x → p ηₚ x) ηₚ x
      where unquoteDecl σ′op = dualise-into σ′op _ σ′
```
-->

```agda
  Co-lan→Ran : Lan (Functor.op p) (Functor.op F) → Ran p F
  Co-lan→Ran lan .Ext     = Functor.op (lan .Ext)
  Co-lan→Ran lan .eps     = co-unit→counit (lan .eta)
  Co-lan→Ran lan .has-ran = is-co-lan→is-ran (lan .has-lan)
```

<!--
```agda
is-ran-is-prop
  : {p : Functor C C′} {F : Functor C D} {G : Functor C′ D} {eps : G F∘ p => F}
  → is-prop (is-ran p F G eps)
is-ran-is-prop {p = p} {F} {G} {eps} a b = path where
  private
    module a = is-ran a
    module b = is-ran b

  σ≡ : {M : Functor _ _} (α : M F∘ p => F) → a.σ α ≡ b.σ α
  σ≡ α = Nat-path λ x → a.σ-uniq (sym b.σ-comm) ηₚ x

  open is-ran
  path : a ≡ b
  path i .σ α = σ≡ α i
  path i .σ-comm {β = α} =
    is-prop→pathp (λ i → Nat-is-set (eps ∘nt (σ≡ α i ◂ p)) α)
      (a.σ-comm {β = α}) (b.σ-comm {β = α})
      i
  path i .σ-uniq {β = α} γ =
    is-prop→pathp (λ i → Nat-is-set (σ≡ α i) _)
      (a.σ-uniq γ) (b.σ-uniq γ)
      i
```
-->
