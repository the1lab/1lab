<!--
```agda
open import Cat.Displayed.Instances.Subobjects using (Subobject)
open import Cat.Instances.Sheaf.Limits.Finite
open import Cat.Functor.Adjoint.Continuous
open import Cat.Instances.Presheaf.Limits
open import Cat.Diagram.Pullback.Along
open import Cat.Site.Sheafification
open import Cat.Instances.Functor
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Functor.Morphism
open import Cat.Functor.Adjoint
open import Cat.Diagram.Omega
open import Cat.Diagram.Sieve
open import Cat.Site.Closure
open import Cat.Site.Base
open import Cat.Prelude

import Cat.Instances.Presheaf.Omega as Soc
import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Instances.Sheaf.Omega {ℓ} {C : Precategory ℓ ℓ} (J : Coverage C ℓ) where
```

# Closed sieves and the subobject classifier {defines="subobject-classifier-sheaf"}

<!--
```agda
open is-generic-subobject
open is-pullback-along
open is-pullback
open Subobject
open Functor
open Soc C
open Cat C

private
  module ΩPSh = Subobject-classifier ΩPSh
  module PSh = Cat (PSh ℓ C)

open Coverage J using (Membership-covers ; Sem-covers)
```
-->

The category of [[sheaves]] $\Sh(\cC, J)$ on a small [[site]] $\cC$ is a
*topos*, which means that --- in addition to finite limits and
exponential objects --- it has a *subobject classifier*, a sheaf which
plays the role of the "universe of propositions". We can construct the
sheaf $\Omega_J$ explicitly, as the sheaf of **$J$-closed sieves**.

A sieve is $J$-closed if it contains every morphism it covers. This
notion is evidently closed under pullback, so the closed sieves form a
presheaf on $\cC$.

```agda
is-closed : ∀ {U} → Sieve C U → Type ℓ
is-closed {U} S = ∀ {V} (h : Hom V U) → J ∋ pullback h S → h ∈ S

abstract
  is-closed-pullback
    : ∀ {U V} (f : Hom V U) (S : Sieve C U)
    → is-closed S → is-closed (pullback f S)
  is-closed-pullback f S c h p = c (f ∘ h) (subst (J ∋_) (sym pullback-∘) p)
```

<!--
```agda
instance
  Extensional-closed-sieve : ∀ {ℓr U} ⦃ _ : Extensional (Sieve C U) ℓr ⦄ → Extensional (Σ[ R ∈ Sieve C U ] is-closed R) ℓr
  Extensional-closed-sieve ⦃ e ⦄ = injection→extensional! Σ-prop-path! e
```
-->

```agda
ΩJ : Sheaf J ℓ
ΩJ .fst = pre where
  pre : Functor (C ^op) (Sets ℓ)
  pre .F₀ U = el! (Σ[ R ∈ Sieve C U ] is-closed R)
  pre .F₁ f (R , c) = pullback f R , is-closed-pullback f R c
  pre .F-id    = funext λ _ → Σ-prop-path! pullback-id
  pre .F-∘ f g = funext λ _ → Σ-prop-path! pullback-∘
```

It remains to show that this is a sheaf. We start by showing that it is
[[separated|separated presheaf]]. Suppose we have two closed sieves $S$,
$T$ which agree everywhere on some $R \in J(U)$. We want to show $S =
T$, so fix some $h : V \to U$; we'll show $h \in S$ iff $h \in T$.

```agda
ΩJ .snd = from-is-separated sep mk where
```

It appears that we don't know much about how $S$ and $T$ behave outside
of their agreement on $R$, but knowing that they're closed will be
enough to show that they agree everywhere. First, let's codify that they
actually agree on their intersection with $R$:

```agda
  sep : is-separated J (ΩJ .fst)
  sep {U} R {S , cS} {T , cT} α = ext λ {V} h →
    let
      rem₁ : S ∩S ⟦ R ⟧ ≡ T ∩S ⟦ R ⟧
      rem₁ = ext λ {V} h → Ω-ua
        (λ (h∈S , h∈R) → cT h (subst (J ∋_) (ap fst (α h h∈R)) (max (S .closed h∈S id))) , h∈R)
        (λ (h∈T , h∈R) → cS h (subst (J ∋_) (ap fst (sym (α h h∈R))) (max (T .closed h∈T id))) , h∈R)
```

Then, assuming w.l.o.g. that $h \in S$, we know that the pullback $h^*(S
\cap R)$ is a covering sieve. And since $h^*(T)$ is a subsieve of
$h^*(S \cap R) = h^*(T \cap R)$, we conclude that if $h \in S$, then
$h^*(T)$ is $J$-covering; and since $T$ is closed, this implies also
that $h \in T$.

```agda
      rem₂ : h ∈ S → J ∋ pullback h (S ∩S ⟦ R ⟧)
      rem₂ h∈S = local (pull h (inc R)) λ f hf∈R → max
        ( S .closed h∈S (f ∘ id)
        , subst (_∈ R) (ap (h ∘_) (intror refl)) hf∈R
        )

      rem₂' : h ∈ S → J ∋ pullback h T
      rem₂' h∈S = incl (λ _ → fst) (subst (J ∋_) (ap (pullback h) rem₁) (rem₂ h∈S))
```

We omit the symmetric converse for brevity.

<!--
```agda
      rem₃ : h ∈ T → J ∋ pullback h S
      rem₃ ht = incl (λ _ → fst) (subst (J ∋_) (ap (pullback h) (sym rem₁))
        (local (pull h (inc R)) λ f rfh → max (T .closed ht (f ∘ id) , subst (_∈ R) (ap (h ∘_) (intror refl)) rfh)))
```
-->

```agda
    in Ω-ua (λ h∈S → cT h (rem₂' h∈S)) (λ h∈T → cS h (rem₃ h∈T))
```

Now we have to show that a family $S$ of compatible closed sieves over a
$J(U)$-covering sieve $R$ can be uniquely patched to a closed sieve on
$U$. This is the sieve which is defined to contain $g : V \to U$
whenever, for all $f : W \to V$ in $g^*(R)$, the part $S(gf)$ is the
maximal sieve.

```agda
  module _ {U : ⌞ C ⌟} (R : J ʻ U) (S : Patch (ΩJ .fst) ⟦ R ⟧) where
    S' : Sieve C U
    S' .arrows {V} g = elΩ $
      ∀ {W} (f : Hom W V) (hf : f ∈ pullback g ⟦ R ⟧) →
      ∀ {V'} (i : Hom V' W) → i ∈ S .part (g ∘ f) hf .fst

    S' .closed = elim! λ α h → inc λ {W} g hf →
      subst (λ e → ∀ (h : e ∈ R) {V'} (i : Hom V' W) → i ∈ S .part e h .fst)
        (assoc _ _ _) (α (h ∘ g)) hf
```

<!--
```agda
    module _ {V W W'} (f : Hom V U) (hf : f ∈ ⟦ R ⟧) (g : Hom W V) (hfg : f ∘ g ∈ ⟦ R ⟧) {h : Hom W' W} where
      lemma : h ∈ S .part (f ∘ g) hfg .fst ≡ (g ∘ h) ∈ S .part f hf .fst
      lemma = sym (ap (λ e → ⌞ e .fst .arrows h ⌟) (S .patch f hf g hfg))

      module lemma = Equiv (path→equiv lemma)
```
-->

The first thing we have to show is that this pulls back to $S$. This is,
as usual, a proof of biimplication, though in this case both directions
are painful --- and entirely mechanical --- calculations.

```agda
    restrict : ∀ {V} (f : Hom V U) (hf : f ∈ R) → pullback f S' ≡ S .part f hf .fst
    restrict f hf = ext λ {V} h → Ω-ua
      (rec! λ α →
        let
          step₁ : id ∈ S .part (f ∘ h ∘ id) (⟦ R ⟧ .closed hf (h ∘ id)) .fst
          step₁ = subst₂ (λ e e' → id ∈ S .part e e' .fst) (pullr refl) (to-pathp⁻ refl)
            (α id _ id)

          step₂ : ((h ∘ id) ∘ id) ∈ S .part f hf .fst
          step₂ = lemma.to f hf (h ∘ id) (⟦ R ⟧ .closed hf (h ∘ id)) {id} step₁

        in subst (λ e → ⌞ S .part f hf .fst .arrows e ⌟) (cancelr (idr _)) step₂)
      (λ hh → inc λ {W} g hg {V'} i → S .part ((f ∘ h) ∘ g) hg .snd i (max
        let
          s1 : i ∈ S .part (f ∘ h ∘ g) _ .fst
          s1 = lemma.from f hf (h ∘ g) _
            (subst (_∈ S .part f hf .fst) (assoc _ _ _)
              (S .part f hf .fst .closed hh (g ∘ i)))

          q : PathP (λ i → assoc f h g i ∈ R) _ hg
          q = to-pathp⁻ refl
        in transport (λ j → ⌞ S .part (assoc f h g j) (q j) .fst .arrows (idr i (~ j)) ⌟) s1))
```

Finally, we can use this to show that $S'$ is closed.

```agda
    abstract
      S'-closed : is-closed S'
      S'-closed {V} h hb = inc λ {W} f hf {V'} i → S .part (h ∘ f) hf .snd i $
        let
          p =
            pullback (f ∘ i) (pullback h S')     ≡˘⟨ pullback-∘ ⟩
            pullback (h ∘ f ∘ i) S'              ≡⟨ restrict (h ∘ f ∘ i) (subst (_∈ R) (sym (assoc h f i)) (⟦ R ⟧ .closed hf i)) ⟩
            S .part (h ∘ f ∘ i) _ .fst           ≡⟨ ap₂ (λ e e' → S .part e e' .fst) (assoc h f i) (to-pathp⁻ refl) ⟩
            S .part ((h ∘ f) ∘ i) _ .fst         ≡˘⟨ ap fst (S .patch (h ∘ f) hf i (⟦ R ⟧ .closed hf i)) ⟩
            pullback i (S .part (h ∘ f) hf .fst) ∎
        in subst (J ∋_) p (pull (f ∘ i) hb)
```

<!--
```agda
    mk : Section (ΩJ .fst) S
    mk .whole = S' , S'-closed
    mk .glues f hf = Σ-prop-path! (restrict f hf)

open _=>_

ΩJ=>Ω : ΩJ .fst => Sieves {C = C}
ΩJ=>Ω .η U              = fst
ΩJ=>Ω .is-natural x y f = refl
```
-->

## Closed subpresheaves

To show that $\Omega_J$ is the [[subobject classifier]] in $\Sh(\cC,
J)$, we'll start by showing that a subpresheaf $A' \mono A$ of a sheaf
$A$ is a sheaf precisely when the associated natural transformation
$\name{A} : A \to \Omega$ into the presheaf of sieves on $\cC$ is valued
in closed sieves.

First, suppose that the domain of $A' \mono A$ is indeed a sheaf, and
note that since the inclusion $\Sh(\cC, J) \mono \psh(\cC)$ is a [[right
adjoint]], any [[subobject]] $A' \mono A$ in $\Sh(\cC, J)$ is also a
subobject in $\psh(\cC)$. Since subobjects in $\psh(\cC)$ are
componentwise embeddings, the same is thus true of a subobject in
$\Sh(\cC, J)$.

```agda
sheaf-name : {A : Sheaf J _} (A' : Subobject (Sheaves J _) A) → A .fst => ΩJ .fst
sheaf-name {A} A' = nm module sheaf-name where
  sub' : Subobject (PSh ℓ C) (A .fst)
  sub' .domain = A' .domain .fst
  sub' .map    = A' .map
  sub' .monic  = right-adjoint→is-monic _
    (free-objects→left-adjoint (Small.make-free-sheaf J))
    {A' .domain} {A} (λ {C} → A' .monic {C})

  emb : ∀ {i} → is-embedding (A' .map .η i)
  emb = is-monic→is-embedding-at ℓ C (sub' .monic)

  nm' : A .fst => Sieves {C = C}
  nm' = psh-name sub'
```

We can then compute, in $\psh(\cC)$, the name of $A'$, resulting in a
natural transformation $\name{A'} : A \to \Omega$. It remains to show
that this transformation is actually valued in $\Omega_J$, i.e. that
each of the resulting sieves is closed. To this end, susppose we have
some $x : A(U)$ and that the sieve $h^*(\name{A'} x)$ is $J$-covering.
We must show that $\name{A'} x$ contains $h$.

By the definition of $\name{A'}$, it suffices to exhibit a fibre of $A'$
over $A(h)(x)$, and since $A'$ is a sheaf, we can construct this fibre
by gluing over the $J$-covering sieve $h^*(\name{A'} x)$. At each $f : W
\to V$, we are given *some* fibre of $A' \mono A$ over $A(hf)(x)$; but
since $A' \mono A$ is an embedding everywhere, we can extract an actual
element of $A'(W)$ from this mere fibre. By the usual functoriality
work, this extends to a patch over $h^*(\name{A'} x)$.

```agda
  name-is-closed : {U : ⌞ C ⌟} (x : A ʻ U) → is-closed (nm' .η U x)
  name-is-closed {U} x {V} h pb =
    let
      it = sat.split (A' .domain .snd) pb record
        { part  = λ {W} f hf → □-out (emb _) hf .fst
        ; patch = λ f hf g hgf → ap fst $ emb _
          (_ , (A' .map .η _ (A' .domain .fst ⟪ g ⟫ (□-out (emb _) hf .fst))  ≡⟨ A' .map .is-natural _ _ _ $ₚ _ ⟩
                (A .fst ⟪ g ⟫ (A' .map .η _ (□-out (emb _) hf .fst)))         ≡⟨ ap (A .fst .F₁ g) (□-out (emb _) hf .snd) ⟩
                (A .fst ⟪ g ⟫ (A .fst ⟪ h ∘ f ⟫ x))                           ≡⟨ sym (A .fst .F-∘ _ _ $ₚ _) ⟩
                (A .fst ⟪ (h ∘ f) ∘ g ⟫ x)                                    ∎))
          (_ , □-out (emb _) hgf .snd ∙ ap₂ (A .fst .F₁) (assoc _ _ _) refl)
        }
```

We must then show that this is indeed a fibre of $A' \mono A$ over
$A(h)(x)$. But since $A$, being a sheaf, is separated, it suffices to do
so locally along $h^*(\name{A'} x)$, at which point we know that this is
true by construction.

```agda
      prf = sat.separate (A .snd) pb λ f hf →
        A .fst ⟪ f ⟫ A' .map .η V (it .whole)          ≡˘⟨ A' .map .is-natural _ _ _ $ₚ _ ⟩
        A' .map .η _ (A' .domain .fst ⟪ f ⟫ it .whole) ≡⟨ ap (A' .map .η _) (it .glues f hf) ⟩
        A' .map .η _ (□-out (emb _) hf .fst)           ≡⟨ □-out (emb _) hf .snd ⟩
        A .fst ⟪ h ∘ f ⟫ x                             ≡⟨ A .fst .F-∘ _ _ $ₚ _ ⟩
        A .fst ⟪ f ⟫ (A .fst ⟪ h ⟫ x)                  ∎
    in inc (it .whole , prf)

  nm : A .fst => ΩJ .fst
  nm .η U x = record { fst = nm' .η U x ; snd = name-is-closed x }
  nm .is-natural x y f = funext λ a → Σ-prop-path! (happly (nm' .is-natural x y f) a)
```

This "if" direction turns out to be sufficient to prove that $\Omega_J$
is a subobject classifier. First, the maximal sieve is obviously closed,
because it contains *every* morphism:

```agda
tru' : Subobject (Sheaves J ℓ) ΩJ
tru' .domain                = Terminal.top (Sh[]-terminal J)
tru' .map .η _ _            = maximal' , (λ _ _ → tt)
tru' .map .is-natural x y f = trivial!
tru' .monic g h x           = trivial!
```

<details>
<summary>Now the universal property follows essentially by arguing in
$\psh(\cC)$. Since the proofs boil down to shuffling whether a given
square is a pullback in $\Sh(\cC, J)$ or in $\psh(\cC)$, we do not
comment on them further.
</summary>

```agda
ΩSheaf : is-generic-subobject (Sheaves J ℓ) tru'
ΩSheaf .name         = sheaf-name
ΩSheaf .classifies m = record { has-is-pb = pb' } where
  rem : is-pullback-along (PSh ℓ C) (m .map) (ΩJ=>Ω ∘nt sheaf-name m) (ΩJ=>Ω ∘nt tru' .map)
  rem = record { has-is-pb = subst-is-pullback refl trivial! refl trivial!
    (ΩPSh.classifies (sheaf-name.sub' m) .has-is-pb) }

  pb' : is-pullback (Sheaves J ℓ) (m .map) (sheaf-name m) (rem .top) (tru' .map)
  pb' .square       = ext λ i h {V} x → unext (rem .square) i h x
  pb' .universal α  = rem .universal (PSh.extendr α)
  pb' .p₁∘universal = rem .p₁∘universal
  pb' .p₂∘universal = rem .p₂∘universal
  pb' .unique       = rem .unique

ΩSheaf .unique {m = m} {nm} α = ext λ i x {V} h → unext path i x h where
  pb : is-pullback (PSh ℓ C) (m .map) nm (α .top) (tru' .map)
  pb = right-adjoint→is-pullback (free-objects→left-adjoint (Small.make-free-sheaf J)) (α .has-is-pb)

  pb' : is-pullback (PSh ℓ C) (m .map) (ΩJ=>Ω ∘nt nm) (α .top) (ΩPSh.true .map)
  pb' .square = ext λ i h {V} x → unext (pb .square) i h x
  pb' .universal {p₁' = p₁'} {p₂'} α = pb .universal {p₁' = p₁'} {p₂'} (ext λ i x {V} h → unext α i x h)
  pb' .p₁∘universal = pb .p₁∘universal
  pb' .p₂∘universal = pb .p₂∘universal
  pb' .unique       = pb .unique

  path = ΩPSh.unique {m = sheaf-name.sub' m} record { has-is-pb = pb' }
```

</details>

Finally, we can show the converse direction to the result we claimed in
the start of this section: a subpresheaf $A' \mono A$ with name
$\name{A'}$ valued in $J$-closed sieves is itself a sheaf. First, we
show that it is separated, because it embeds into a sheaf:

```agda
name-is-closed→is-sheaf
  : {A : Sheaf J _} (A' : Subobject (PSh ℓ C) (A .fst))
  → (∀ {U : ⌞ C ⌟} (x : A ʻ U) → is-closed (psh-name A' .η U x))
  → is-sheaf J (A' .domain)
name-is-closed→is-sheaf {A = A} A' cl = from-is-sheaf₁ λ {U} j p → from-is-separated₁ _ (sep j) (s j p) where
  emb : ∀ {i} → is-embedding (A' .map .η i)
  emb = is-monic→is-embedding-at ℓ C (A' .monic)

  sep : ∀ {U} (j : J .covers U) → is-separated₁ (A' .domain) (J .cover j)
  sep j {x} {y} h = ap fst $ emb _ (_ , refl) $ _ , A .snd .separate j λ f hf →
    A .fst ⟪ f ⟫ A' .map .η _ y         ≡˘⟨ A' .map .is-natural _ _ _ $ₚ _ ⟩
    A' .map .η _ ⌜ A' .domain ⟪ f ⟫ y ⌝ ≡⟨ ap! (sym (h f hf)) ⟩
    A' .map .η _ (A' .domain ⟪ f ⟫ x)   ≡⟨ A' .map .is-natural _ _ _ $ₚ _ ⟩
    A .fst ⟪ f ⟫ A' .map .η _ x         ∎
```

Now, given a $J$-covering sieve $R$ of some object $U$ and a patch $p$
along over $R$, we must put together a section in $A'(U)$. First, we
lift $p$ to a patch $p'$ of $A$, the sheaf, over the same $J$-covering
sieve; and this glues to a section $s' : A(U)$.

```agda
  module _ {U} (j : J .covers U) (p : Patch (A' .domain) (J .cover j)) where
    p' : Patch (A .fst) (J .cover j)
    p' = record
      { part  = λ {V} f hf → A' .map .η V (p .part f hf)
      ; patch = λ {V} {W} f hf g hgf → sym (A' .map .is-natural _ _ _ $ₚ _) ∙ ap (A' .map .η _) (p .patch f hf g hgf)
      }

    s' : Section (A .fst) p'
    s' = is-sheaf.split (A .snd) p'
```

We must show that $s'$ actually comes from a section $A'(U)$. This
follows from $A'$ having a closed name: by definition, this means that
if we can show that $\name{A'} s'$ is a $J$-covering sieve, then the
fibre of $A' \mono A$ over $A(\id)(s') = s'$ is contractible. To show
this, it suffices to show that $\name{A} s'$ pulls back to a
$J$-covering locally at every $f : V \to U$ in some other $J$-covering
sieve $R$ --- we choose the $R$ we were already working against. Then
we're left with a simple computation:

```agda
    abstract
      has : J ∋ pullback id (psh-name A' .η U (s' .whole))
      has = local (inc j) λ {V} f hf →
        let
          α : pullback f (pullback id (psh-name A' .η U (s' .whole))) ≡ psh-name A' .η V (p' .part f hf)
          α =
            pullback f ⌜ pullback id (psh-name A' .η U (s' .whole)) ⌝  ≡⟨ ap! pullback-id ⟩
            pullback f (psh-name A' .η U (s' .whole))                  ≡⟨ sym (psh-name A' .is-natural _ _ _ $ₚ _) ⟩
            psh-name A' .η V (A .fst ⟪ f ⟫ s' .whole)                  ≡⟨ ap (psh-name A' .η _) (s' .glues f hf) ⟩
            psh-name A' .η V (p' .part f hf)                           ∎
        in subst (J ∋_) (sym α) (max (inc (p .part f hf , sym (A .fst .F-id $ₚ _))))

    it : fibre (map A' .η U) (A .fst ⟪ id ⟫ s' .whole)
    it = □-out (emb _) (cl (s' .whole) id has)

    s : Section (A' .domain) p
    s = record
      { whole = it .fst
      ; glues = λ f hf → ap fst (emb (A .fst ⟪ f ⟫ s' .whole)
        (_ , A' .map .is-natural _ _ _ $ₚ _ ∙ ap (A .fst .F₁ f) (it .snd ∙ A .fst .F-id $ₚ _))
        (_ , sym (s' .glues f hf)))
      }
```
