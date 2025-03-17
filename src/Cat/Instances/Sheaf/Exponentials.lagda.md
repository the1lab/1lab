<!--
```agda
open import Cat.Instances.Presheaf.Exponentials
open import Cat.Diagram.Sieve
open import Cat.Functor.Base
open import Cat.Site.Closure
open import Cat.Site.Base
open import Cat.Prelude

import Cat.Functor.Reasoning.Presheaf as PSh
import Cat.Reasoning as Cat

open Functor
open _=>_
```
-->

```agda
module Cat.Instances.Sheaf.Exponentials where
```

# Exponentials of sheaves {defines="exponentials-of-sheaves"}

In this module we will show that the $J$-[[sheaves]], for a coverage
$J$, are an *exponential ideal* in $\psh(\cC)$. This means that, if $B$
is a $J$-sheaf, and $A$ is any presheaf at all, then the exponential
object $B^A$ is *also* a $J$-sheaf. The proof will rely crucially on the
[[closure properties of sites]]. For this proof, keep in that the
exponential $B^A$ is constructed[^yoneda] to have sections $$(B^A)(x) =
\hom(\cC(-, x) \times A, B)$$.

[^yoneda]:
    If you're worried about the dependence on the concrete construction,
    don't be: this always holds as a natural isomorphism, by the
    [[yoneda lemma]]:

    $$
    \begin{align*}
    (B^A)(x) &= \hom(\cC(-, x), B^A) \\
             &= \hom(\cC(-, x) \times A, B)\text{.}
    \end{align*}
    $$

```agda
is-sheaf-exponential
  : ∀ {ℓ ℓs} {C : Precategory ℓ ℓ} (J : Coverage C ℓs) (A B : Functor (C ^op) (Sets ℓ))
  → is-sheaf J B
  → is-sheaf J (PSh[_,_] C A B)
is-sheaf-exponential {C = C} J A B bshf = from-is-sheaf₁ λ c → done where
  open Cat C
  module bshf = sat bshf

  psh = PSh[_,_] C A B
```

The first thing we'll do is show that $B^A$ is $J$-separated. Let $R$ be
a $J$-covering sieve of $U$, and $x, y : (B^A)(U)$ be sections at $U$
which are $R$-locally equal, i.e. such that, for $g : V \to U \in R$, we
have, for all $W : \cC$, maps $h : W \to V$, and $e : A(W)$, we have
$x_W(gh, x) = y_W(gh, e)$. This condition is a bit of a mouthful, but
all we've done is unfold the definition of equality in $\cC(-,U) \times
A \To B$.

What we must *show*, however, is that $x(f,z) = y(f,z)$, for a totally
arbitrary $f : W \to V$ and $z : A(V)$. But, since this is an equality
in $B(W)$, and $B$ is a $J$-sheaf, it suffices to choose a $J$-covering
sieve $S$ of $W$, and to show this equality $S$-locally, i.e. to show
$$
B(g)(x(f, z)) = B(g)(y(f, z))
$$
for any $g \in S$. Note that, by naturality, these are equal to $x(fg,
z)$, resp. $y(fg, z)$. We can then choose $S = f^*(R)$, which lets us
apply our $R$-local equality (since $g \in f^*(R)$ means $fg \in R$)!
This concludes the proof that $B^A$ is $J$-separated.

```agda
  abstract
    sep : {U : ⌞ C ⌟} {c : J ʻ U} → is-separated₁ psh (J .cover c)
    sep {c = c} {x} {y} loc = ext λ V f z → bshf.separate (pull f (inc c)) λ g hg →
      B ⟪ g ⟫ x .η V (f , z)             ≡˘⟨ x .is-natural _ _ _ $ₚ _ ⟩
      x .η _ (f ∘ g , A ⟪ g ⟫ z)         ≡⟨ ap (x .η _) (Σ-pathp (intror refl) refl) ⟩
      x .η _ ((f ∘ g) ∘ id , A ⟪ g ⟫ z)  ≡⟨ loc (f ∘ g) hg ηₚ _ $ₚ _ ⟩
      y .η _ ((f ∘ g) ∘ id , A ⟪ g ⟫ z)  ≡˘⟨ ap (y .η _) (Σ-pathp (intror refl) refl) ⟩
      y .η _ (f ∘ g , A ⟪ g ⟫ z)         ≡⟨ y .is-natural _ _ _ $ₚ _ ⟩
      B ⟪ g ⟫ y .η V (f , z)             ∎
```

The proof of separatedness demonstrates the general schema for shuffling
between local equality of natural transformations and local equality of
their components, by passing to a pullback. The rest of the proof
essentially follows from similar calculations.

This will also be the strategy to show that $B^A$ admits sections!  To
put together a section for a [[patch]] $p$ for a $J$-covering sieve $R$,
it suffices to do so at each component; so we'll start by showing that
$p$ descends to a patch $p'$ for $B(U)$ on $f^*R$, for any $f : V \to
U$, as long as we're given $x : A(V)$. Each part of $p'$ is given by
evaluating the corresponding part of $p$:

```agda
  module _ {U} {c : J ʻ U} (p : Patch psh (J .cover c)) where
    p' : ∀ {V} (e : A ʻ V) (f : Hom V U) → Patch B (pullback f (J .cover c))
    p' e f .part g hg = p .part (f ∘ g) hg .η _ (id , A ⟪ g ⟫ e)
    p' e f .patch g hg h hh =
      B ⟪ h ⟫ p .part (f ∘ g) _ .η _ (id , A ⟪ g ⟫ e)          ≡˘⟨ p .part (f ∘ g) hg .is-natural _ _ _ $ₚ (id , A ⟪ g ⟫ e) ⟩
      p .part (f ∘ g) _ .η _ (id ∘ h , A ⟪ h ⟫ (A ⟪ g ⟫ e))    ≡⟨ ap (λ it → p .part (f ∘ g) hg .η _ (it , A ⟪ h ⟫ (A ⟪ g ⟫ e))) id-comm-sym ⟩
      p .part (f ∘ g) _ .η _ (h ∘ id , A ⟪ h ⟫ (A ⟪ g ⟫ e))    ≡⟨ p .patch (f ∘ g) hg h (subst (_∈ J .cover c) (assoc _ _ _) hh) ηₚ _ $ₚ (id , _) ⟩
      p .part ((f ∘ g) ∘ h) _ .η _ (id , A ⟪ h ⟫ (A ⟪ g ⟫ e))  ≡⟨ app p (sym (assoc f g h)) ηₚ _ $ₚ _ ⟩
      p .part (f ∘ g ∘ h) _ .η _ (id , A ⟪ h ⟫ (A ⟪ g ⟫ e))    ≡⟨ ap (λ e → p .part (f ∘ g ∘ h) hh .η _ (id , e)) (sym (A .F-∘ _ _ · _)) ⟩
      p .part (f ∘ g ∘ h) _ .η _ (id , A ⟪ g ∘ h ⟫ e)          ∎
```

Then, since $B$ is a $f^*(R)$-sheaf, for the component at $(f, x)$, we
can glue together the relevant $p'$. By the same strategy by which we
showed separatedness we can show naturality, and that the resulting
natural transformation really does glue $p$.

```agda
    s' : Section (PSh[_,_] C A B) p
    s' .whole .η x (f , e) = it .whole module s' where
      it : Section B (p' e f)
      it = bshf.split (pull f (inc c)) (p' e f)

    s' .whole .is-natural x y f = ext λ g e → bshf.separate (pull (g ∘ f) (inc c)) λ h hh →
      let clo = subst (_∈ J .cover c) (sym (assoc _ _ _)) hh in
      B ⟪ h ⟫ (s'.it y (g ∘ f) (A ⟪ f ⟫ e) .whole)            ≡⟨ s'.it y (g ∘ f) (A ⟪ f ⟫ e) .glues _ hh ⟩
      p .part ((g ∘ f) ∘ h) _ .η _ (id , A ⟪ h ⟫ (A ⟪ f ⟫ e)) ≡˘⟨ (λ i → p .part (assoc g f h i) (coe1→i (λ i → assoc g f h i ∈ J .cover c) i hh) .η _ (id , A .F-∘ h f i e)) ⟩
      p .part (g ∘ f ∘ h) _ .η _ (id , A ⟪ f ∘ h ⟫ e)         ≡˘⟨ sym (B .F-∘ _ _ · _) ∙ s'.it x g e .glues (f ∘ h) clo ⟩
      B ⟪ h ⟫ (B ⟪ f ⟫ (s'.it x g e .whole))                  ∎

    s' .glues f hf = ext λ x g e →
      let clo = J .cover c .closed (J .cover c .closed hf g) id in
      s'.it x (f ∘ g) e .whole                         ≡˘⟨ B .F-id · _ ⟩
      (B ⟪ id ⟫ s'.it x (f ∘ g) e .whole)              ≡⟨ s'.it x (f ∘ g) e .glues id clo ⟩
      p .part ((f ∘ g) ∘ id) _ .η x (id , A ⟪ id ⟫ e)  ≡⟨ ap₂ (λ i1 i2 → p .part i1 i2 .η x (id , A ⟪ id ⟫ e)) (idr (f ∘ g)) prop! ⟩
      p .part (f ∘ g) _ .η x (id , A ⟪ id ⟫ e)         ≡⟨ sym (p .patch f hf g (J .cover c .closed hf g) ηₚ _ $ₚ (id , A ⟪ id ⟫ e)) ⟩
      p .part f hf .η x (g ∘ id , A ⟪ id ⟫ e)          ≡⟨ ap (p .part f hf .η x) (Σ-pathp (idr g) (A .F-id · _)) ⟩
      p .part f hf .η x (g , e)                        ∎

    done = from-is-separated₁ psh sep s'
```
