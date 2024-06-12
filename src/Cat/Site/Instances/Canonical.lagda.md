<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Colimit.Base
open import Cat.Instances.Elements
open import Cat.Site.Constructions
open import Cat.Functor.Kan.Base
open import Cat.Diagram.Sieve
open import Cat.Site.Closure
open import Cat.Functor.Hom
open import Cat.Site.Base
open import Cat.Prelude

import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Site.Instances.Canonical {o ℓ} (C : Precategory o ℓ) where
```

# The canonical coverage

<!--
```agda
open Element-hom
open Element
open Cat C
open _=>_
```
-->

Every [[sieve]] $S$ on an object $U$ (in a category $\cC$) may be
regarded as a *diagram* in $\cC$, by first [[interpreting it as a
presheaf|sieves as presheaves]], then considering the projection functor

$$
\pi : \int S \to \cC
$$

with domain the [[category of elements]] of $S$; The objects of this
category consist of triples $i : \cC$, $f : i \to U$, and a
([[propositional|proposition]]) witness that $f \in S$. Thus, purely
formally, the object $U$ is the nadir of a [[cocone]] under
$S$-qua-diagram, since we can give the component of a natural
transformation $\pi \To U$ by projecting the arrow.

```agda
sieve→cocone : ∀ {U} (S : Sieve C U) → πₚ C (to-presheaf S) => Const U
sieve→cocone S .η (elem i (f , f∈S)) = f
sieve→cocone S .is-natural (elem _ (f , _)) (elem _ (g , _)) h =
  g ∘ h .hom ≡⟨ ap fst (h .commute) ⟩
  f          ≡⟨ introl refl ⟩
  id ∘ f     ∎
```

Thus, under this setup, a natural question to ask about *any* sieve is
whether it forms a [[colimit]] diagram. This is also a notion of
*covering*, which we can impose on any category, since *any* given
colimit diagram with nadir $U$ can be seen as a covering of $U$ by the
objects in $S$, which sit inside according to the *maps* in $S$.
Johnstone [-@Elephant, C2.2.8] refers to the sieves which *are*
colimiting cocones as "effective-epimorphic". We will instead follow
Lester [-@Lester:2019] and refer to them as **colim sieves**.

```agda
is-colim : ∀ {U} → Sieve C U → Type _
is-colim {U} S = is-colimit _ U (sieve→cocone S)
```

Natural though it is, unfortunately, being a colim sieve is *not* a
property we can ask of sieves to get a [[site]]. The reason is that, in
an arbitrary category, colimits may not be preserved by [[pullback]]; in
terms of sieves, even if $S$ is a colim sieve over $U$, we may not have
that $f^*(S)$ is a colim sieve over $V$ for $f : V \to U$. We can,
however, turn this into a site, by restricting the notion of colim sieve
so that it's stable under pullbacks: we say that $S$ is a **universal
colim sieve** if $f^*(S)$ is a colim sieve, for any appropriate $f$.

```agda
is-universal-colim : ∀ {U} → Sieve C U → Type _
is-universal-colim {U} S =
  ∀ {V} (f : Hom V U) → is-colim (pullback f S)
```

Since this is a pullback-stable property of sieves, we can get a site.
We refer to this as the **canonical coverage** on a category $\cC$.

```agda
abstract
  is-universal-colim-is-stable
    : ∀ {U V} (f : Hom V U) (S : Sieve C U)
    → is-universal-colim S
    → is-universal-colim (pullback f S)
  is-universal-colim-is-stable f S hS g = subst is-colim pullback-∘ (hS (f ∘ g))

  is-universal-colim→is-colim : ∀ {U} (S : Sieve C U) → is-universal-colim S → is-colim S
  is-universal-colim→is-colim S u = subst is-colim pullback-id (u id)

Canonical-coverage : Coverage C (o ⊔ ℓ)
Canonical-coverage = from-stable-property
  is-universal-colim
  is-universal-colim-is-stable
```

## Representables as sheaves

We will now investigate the matter of [[sheaves]] for the canonical
topology. First, let $S$ be an arbitrary sieve on $U : \cC$, and suppose
that we have a [[patch]] $p$ for $\cC(-, V)$ over $S$: this means that
we have a function $p(f) : W \to V$, for $f$ a map $W \to U$ belonging
to $S$. Since the components of a cocone under $S$ are indexed precisely
by these maps, we see that $p(-)$ is a transformation $S \To
\operatorname{Const} V$.

```agda
patch→cocone
  : ∀ {U V} (S : Sieve C U)
  → Patch (Hom-into C V) S
  → πₚ C (to-presheaf S) => const! V F∘ !F
patch→cocone S p .η (elem _ (f , hf)) = p .part f hf
```

It remains to show that this transformation is natural. We compute:

```agda
patch→cocone S p .is-natural (elem _ (f , hf)) (elem _ (g , hg)) h =
  p .part g hg ∘ h .hom  ≡⟨ p .patch g hg (h .hom) (S .closed hg (h .hom)) ⟩
  p .part (g ∘ h .hom) _ ≡⟨ app p (ap fst (h .commute)) ⟩
  p .part f _            ≡⟨ introl refl ⟩
  id ∘ p .part f _       ∎
```

Now suppose that $S$ is not just a sieve, but a colim sieve, as defined
above. Since any patch $p$ for $\cC(-,V)$ gives a cocone under $S$ with
nadir $V$, and $U$ is the colimit of $S$, we have a map $\pi : U \to V$
which satisfies $\pi \circ f = p(f)$, for any $f \in S$.

```agda
is-colim→よ-is-sheaf
  : ∀ {U V} (S : Sieve C U)
  → is-colim S
  → is-sheaf₁ (Hom-into C V) S
is-colim→よ-is-sheaf {U} {V} S colim p = uniq where
  module x = is-lan colim

  p' : πₚ C (to-presheaf S) => const! V F∘ !F
  p' = patch→cocone S p
```

Note now that $\pi$, with its "computation rule", is precisely a
[[section|patch]] for the patch $p$.

```agda
  π : Hom U V
  π = x.σ p' .η tt

  πβ : ∀ {W} (f : Hom W _) hf → π ∘ f ≡ p .part f hf
  πβ f hf = x.σ-comm {α = p'} ηₚ elem _ (f , hf) ∙ app p refl
```

But `π` is not just *a* map with this property; it is *the unique* map
with this property. Since sections of $p$ correspond precisely to this
data, we have that $\cC(-, V)$ is a sheaf for $S$, as soon as $S$ is a
colim sieve.

```agda
  uniq : is-contr (Section _ p)
  uniq .centre  = record { glues = πβ }
  uniq .paths x = ext $
    x.σ-uniq {σ' = const-nt _} (ext λ i → sym (x .glues _ _)) ηₚ tt
```

Generalising the proof above, we conclude that *any* representable
functor $\cC(-, U)$ is a sheaf for the canonical coverage.

```agda
よ-is-sheaf-canonical
  : ∀ {U} → is-sheaf Canonical-coverage (Hom-into C U)
よ-is-sheaf-canonical = from-is-sheaf₁ λ (S , hS) →
  is-colim→よ-is-sheaf S (is-universal-colim→is-colim S hS)
```

## Subcanonical coverages

:::{.definition #subcanonical-coverage}

We can now ask: is there a converse to this result, i.e., if every
$\cC(-, U)$ is a sheaf for a coverage $J$, must it be the canonical
coverage? The answer is *not quite*, since that is too strong. But we
*can* show that all the sieves in $J$ are universal colim sieves! We
will refer to any coverage $J$ which satisfies the following equivalent
conditions as a **subcanonical coverage**:

1. Every representable functor $\cC(-, U)$ is a sheaf for $J$;
2. Every covering sieve in $J$ is universally colimiting.

:::

```agda
is-subcanonical : ∀ {ℓc} → Coverage C ℓc → Type _
is-subcanonical J = ∀ {U} (S : J .covers U) → is-universal-colim (J .cover S)
```

<!--
```agda
make-is-colim : ∀ {U} (S : Sieve C U) → Type _
make-is-colim {U} S = make-is-colimit (πₚ C (to-presheaf S)) U

is-subcanonical→よ-is-sheaf
  : ∀ {ℓc} (J : Coverage C ℓc)
  → is-subcanonical J
  → ∀ {V} → is-sheaf J (Hom-into C V)
is-subcanonical→よ-is-sheaf J sub {V} = from-is-sheaf₁ λ c →
  is-colim→よ-is-sheaf _ (is-universal-colim→is-colim (J .cover c) (sub _))
```
-->

For concreteness, we formalise the statement "$J$ is a subcanonical
coverage" as property (2); We must then show that $J$ is subcanonical if
every representable is a $J$-sheaf.

```agda
よ-is-sheaf→is-subcanonical
  : ∀ {ℓc} (J : Coverage C ℓc)
  → (∀ {V} → is-sheaf J (Hom-into C V))
  → is-subcanonical J
よ-is-sheaf→is-subcanonical J shf {U} S {V} f = to-is-colimitp mk refl where
  open make-is-colimit
```

So, suppose we have such a $J$, a covering sieve $S : J(U)$, and a map
$f : V \to U$. We want to show that $V$ is the colimit of $f^*(S)$.
First, we get the cocone $\pi_S \To \operatorname{Const} U$ out of the
way: this is as, as we've seen repeatedly, projecting the arrow.

```agda
  mk : make-is-colim (pullback f (J .cover S))
  mk .ψ (elem V' (g , hg)) = g
  mk .commutes f = ap fst (f .commute)
```

Now for the interesting part, universality. Our inputs are an object
$W$, and a function $\eps$ which, given a map $g : X \to V$ in $f^*(S)$
(i.e., such that $fg \in S$), produces $\eps(g) : X \to W$. Moreover, if
we have some $h : Y \to X$ with $fgh \in S$, then $\eps$ satisfies
$\eps(g) \circ h = \eps(gh)$. What we want is, initially, a map $V \to
W$. But note that $\eps(-)$ is precisely the data of a [[patch]] for
$\cC(-, W)$ under $f^*(S)$!

```agda
  mk .universal {W} ε comm = [_] .centre .whole module univ where
    ε' : Patch (よ₀ C W) (pullback f (J .cover S))
    ε' .part  g hg       = ε (elem _ (_ , hg))
    ε' .patch g hg h hhg = comm (elem-hom h (Σ-prop-path! refl))
```

Since $\cC(-, W)$ was assumed to be a sheaf for $S$, it's also a sheaf
for any pullback of $S$, including $f^*(S)$; The patch induced by $\eps$
thus glues to a unique *section*, which we will write $[\eps]$. What
does this section consist of? Well, first, since $f^*(S)$ covers $V$, a
map $V \to W$, like we wanted; It also contains evidence that, for $g :
W \to V$ belonging to $f^*(S)$, we have $[\eps] \circ g = \eps(g)$.

```agda
    [_] : is-contr (Section (Hom-into C W) ε')
    [_] = is-sheaf-pullback shf S f ε'

  mk .factors {elem W (g , hg)} ε p = univ.[ ε ] p .centre .glues _ _
```

Finally, for $V$ to be a colimit, we must show uniqueness of the map
$[\eps] : V \to W$, in the sense that if we have $\sigma : V \to W$
which *also* satisfies $\sigma \circ f = \eps(f)$ for any $f \in S$,
then we must have $[\eps] = \sigma$. But note that this commutativity
condition is precisely what it means for $\sigma$ to underlie a section
for $\eps$-qua-patch; so since $\cC(-, W)$ is a sheaf, this $\sigma$
must be equal to the $[\eps]$ we obtained from *the* section for
$\eps$.

```agda
  mk .unique ε p σ q = sym $ ap whole $ univ.[ ε ] p .paths
    record { glues = λ f hf → q (elem _ (f , hf)) }
```
