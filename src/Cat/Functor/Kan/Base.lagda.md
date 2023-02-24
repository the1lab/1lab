```agda
open import Cat.Functor.Coherence
open import Cat.Instances.Functor.Compose
open import Cat.Instances.Shape.Terminal
open import Cat.Instances.Functor
open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning as Cat

module Cat.Functor.Kan.Base where
```

<!--
```agda
private
  variable
    o ℓ : Level
    C C′ D E : Precategory o ℓ
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
record
  is-lan (p : Functor C C′) (F : Functor C D) (L : Functor C′ D) (eta : F => L F∘ p)
    : Type (kan-lvl p F) where
  field
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
    σ : {M : Functor C′ D} (α : F => M F∘ p) → L => M
    σ-comm : {M : Functor C′ D} {α : F => M F∘ p} → (σ α ◂ p) ∘nt eta ≡ α
    σ-uniq : {M : Functor C′ D} {α : F => M F∘ p} {σ′ : L => M}
           → α ≡ (σ′ ◂ p) ∘nt eta
           → σ α ≡ σ′

  σ-uniq₂
    : {M : Functor C′ D} (α : F => M F∘ p) {σ₁′ σ₂′ : L => M}
    → α ≡ (σ₁′ ◂ p) ∘nt eta
    → α ≡ (σ₂′ ◂ p) ∘nt eta
    → σ₁′ ≡ σ₂′
  σ-uniq₂ β p q = sym (σ-uniq p) ∙ σ-uniq q

  open _=>_ eta
```

We also provide a bundled form of this data.

```agda
record Lan (p : Functor C C′) (F : Functor C D) : Type (kan-lvl p F) where
  field
    Ext     : Functor C′ D
    eta     : F => Ext F∘ p
    has-lan : is-lan p F Ext eta

  module Ext = Func Ext
  open is-lan has-lan public
```

# Right Kan extensions

Our choice of universal property in the section above isn't the only
choice; we could instead require a [terminal] solution to the lifting
problem, instead of an [initial] one. We can picture the terminal
situation using the following diagram.

[terminal]: Cat.Diagram.Terminal.html
[initial]: Cat.Diagram.Initial.html

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

Note the same warnings about "weak, directed" commutativity as for left
Kan extensions apply here, too. Rather than either of the triangles
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

  module Ext = Func Ext
  open is-ran has-ran public
```

<!--
```agda
is-lan-is-prop
  : {p : Functor C C′} {F : Functor C D} {G : Functor C′ D} {eta : F => G F∘ p}
  → is-prop (is-lan p F G eta)
is-lan-is-prop {p = p} {F} {G} {eta} a b = path where
  private
    module a = is-lan a
    module b = is-lan b

  σ≡ : {M : Functor _ _} (α : F => M F∘ p) → a.σ α ≡ b.σ α
  σ≡ α = Nat-path λ x → a.σ-uniq (sym b.σ-comm) ηₚ x

  open is-lan
  path : a ≡ b
  path i .σ α = σ≡ α i
  path i .σ-comm {α = α} =
    is-prop→pathp (λ i → Nat-is-set ((σ≡ α i ◂ p) ∘nt eta) α)
      (a.σ-comm {α = α}) (b.σ-comm {α = α})
      i
  path i .σ-uniq {α = α} β =
    is-prop→pathp (λ i → Nat-is-set (σ≡ α i) _)
      (a.σ-uniq β) (b.σ-uniq β)
      i

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

# Preservation and reflection of Kan extensions

Let $(G : C' \to D, \eta : F \to G \circ p)$ be the left kan extension
of $F : C \to D$ along $p : C \to C'$, and suppose that $H : D \to E$ is
a functor. Note that we can $H$ with all of the data of the kan extension
to obtain the following diagram.

~~~{.quiver}
\begin{tikzcd}
  C &&&& E \\
  \\
  && {C'}
  \arrow["p"', from=1-1, to=3-3]
  \arrow[""{name=0, anchor=center, inner sep=0}, "HF", from=1-1, to=1-5]
  \arrow["HG"', from=3-3, to=1-5]
  \arrow["H\eta", shorten <=4pt, shorten >=4pt, Rightarrow, from=0, to=3-3]
\end{tikzcd}
~~~

This looks like yet another kan extension, but it may not be universal!
If this diagram is a left kan extension, we say that $H$ **preserves**
$(G, \eta)$.

<!--
```agda
module _
  {p : Functor C C′} {F : Functor C D} {G : Functor C′ D} {eta : F => G F∘ p} where
```
-->

```agda
  preserves-lan : (H : Functor D E) → is-lan p F G eta → Type _
  preserves-lan H _ =
    is-lan p (H F∘ F) (H F∘ G) (nat-assoc-to (H ▸ eta))
```

In the diagram above, the 2-cell is simply the whiskering $H\eta$.
Unfortunately, proof assistants; our definition of whiskering lands in
$H(Gp)$, but we requires a natural transformation to $(HG)p$.

It may also be the case that $(HG, H\eta)$ is already a left kan
extension of $HF$ along $p$. We say that $H$ reflects this kan extension
if $G, \eta$ is a kan extension of $F$ along $p$.

```agda
  reflects-lan
    : (H : Functor D E)
    → is-lan p (H F∘ F) (H F∘ G) (nat-assoc-to (H ▸ eta))
    → Type _
  reflects-lan _ _ =
    is-lan p F G eta
```

<!--
```agda
module _
  {p : Functor C C′} {F : Functor C D} {G : Functor C′ D} {eps : G F∘ p => F} where
```
-->

We can define dual notions for right kan extensions as well.

```agda
  preserves-ran : (H : Functor D E) → is-ran p F G eps → Type _
  preserves-ran H _ =
    is-ran p (H F∘ F) (H F∘ G) (nat-assoc-from (H ▸ eps))

  reflects-ran
    : (H : Functor D E)
    → is-ran p (H F∘ F) (H F∘ G) (nat-assoc-from (H ▸ eps))
    → Type _
  reflects-ran _ _ =
    is-ran p F G eps
```