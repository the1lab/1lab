<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Colimit.Base
open import Cat.Instances.Elements
open import Cat.Site.Constructions
open import Cat.Functor.Kan.Base
open import Cat.Diagram.Sieve
open import Cat.Functor.Hom
open import Cat.Site.Base hiding (whole ; glues ; separate)
open import Cat.Prelude

import Cat.Functor.Reasoning.Presheaf as Psh
import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Site.Closure where
```

# Closure properties of sites {defines="closure-properties-of-sites"}

<!--
```agda
module _ {o ℓ ℓs} {C : Precategory o ℓ} (A : Functor (C ^op) (Sets ℓs)) where
  open Cat C
  open Section
  open Patch
  open is-sheaf
  private module A = Psh A
```
-->

If $A$ is a [[sheaf]] on a [[site]] $(\cC, J)$, then there are quite a
few sieves for which $A$ is a sheaf but which are not required to be
present in $J$. Put another way, the collection of sieves for which a
given functor is a sheaf enjoys closure properties beyond the basic
pullback-stability which we have assumed in the definition of coverage.
Closing $J$ under these extra constructions does not change the theory
of "sheaves on $(\cC, J)$", and sometimes they're quite convenient!

In reality, the first few of these properties don't even *need* a site:
they work for a completely arbitrary functor $A$. We will fix a
completely arbitrary functor $A$ for the remainder of this section. The
first thing we note is that, if a sieve $S$ contains the identity, then
$A$ is a sheaf for $S$:

```agda
  is-sheaf-maximal : ∀ {U} {S : Sieve C U} → id ∈ S → is-sheaf₁ A S
  is-sheaf-maximal {S = S} id∈S p .centre .whole = p .part id id∈S
  is-sheaf-maximal {S = S} id∈S p .centre .glues f hf =
    A ⟪ f ⟫ p .part id id∈S ≡⟨ p .patch id id∈S f (subst (_∈ S) (sym (idl f)) hf) ⟩
    p .part (id ∘ f) _      ≡⟨ app p (idl f) ⟩
    p .part f hf            ∎
  is-sheaf-maximal {S = S} id∈S p .paths x = ext $
    p .part id id∈S   ≡˘⟨ x .glues id id∈S ⟩
    A ⟪ id ⟫ x .whole ≡⟨ A.F-id ⟩
    x .whole          ∎
```

Since sieves are closed under composition, this can be extended to any
$S$ which contains an isomorphism. Intuitively, this is because any
sieve on $U$ which contains the identity (or an isomorphism) says that
global data on $U$ can be constructed locally... on all of $U$! We can
thus just extract this not-actually-local data from a given patch.

```agda
  is-sheaf-iso : ∀ {V U} {S : Sieve C U} (f : V ≅ U) → f .to ∈ S → is-sheaf₁ A S
  is-sheaf-iso {S = S} f hf = is-sheaf-maximal $
    subst (_∈ S) (f .invl) (S .closed hf (f .from))
```

The second notion we investigate says that the notion of sheaf is,
*itself*, local: If $A$ is a sheaf for a sieve $R$, and we have some
other sieve $S$ which we want to show $A$ is a sheaf for, it (almost)
suffices to show that A is an $f^*(S)$-sheaf for every $f \in R$. If $R$
and $S$ are not part of a site, then this condition does not suffice: we
also require that $A$ be $f^*(R)$-separated, for every $f \in S$.

::: warning
In the Elephant, this lemma appears as C2.1.7. However, Johnstone's
version is **incorrect** as stated. It can be remedied by assuming that
$R$ belongs to a site for which $A$ is a sheaf, since a sheaf on a site
is automatically separated for any pullback of a covering sieve.
:::

```agda
  is-sheaf-transitive
    : ∀ {U} {R S : Sieve C U}
    → (∀ {V} (f : Hom V U) (hf : f ∈ S) → is-separated₁ A (pullback f R))
    → (∀ {V} (f : Hom V U) (hf : f ∈ R) → is-sheaf₁ A (pullback f S))
    → is-sheaf₁ A R
    → is-sheaf₁ A S
  is-sheaf-transitive {U} {R} {S} R*sep S*sheaf Rsheaf p = q where
```

The proof is slightly complicated. Note that a patch $p$ on $S$ can be
pulled back to give a patch $f^*(p)$ on $f^*(S)$, for any $f \in R$;
Since $A$ is an $f^*(S)$-sheaf, at each $f : V \to U$ in $R$, there is a
unique $p''(f) : A(V)$, and a short calculation shows that these $p''$
give a patch on $R$.

```agda
    p' : ∀ {V} (f : Hom V U) → Patch A (pullback f S)
    p' f = pullback-patch f p

    p'' : Patch A R
    p'' .part f hf = S*sheaf f hf (p' f) .centre .whole
    p'' .patch f hf g hgf = ext $ is-sheaf₁→is-separated₁ A _ (S*sheaf (f ∘ g) hgf) λ h hh →
      A ⟪ h ⟫ (A ⟪ g ⟫ (p'' .part f hf))  ≡⟨ A.collapse refl ⟩
      A ⟪ g ∘ h ⟫ (p'' .part f hf)        ≡⟨ S*sheaf f hf (p' f) .centre .glues (g ∘ h) (subst (_∈ S) (sym (assoc f g h)) hh) ⟩
      p .part (f ∘ g ∘ h) _               ≡⟨ app p (assoc _ _ _) ⟩
      p .part ((f ∘ g) ∘ h) _             ≡˘⟨ S*sheaf (f ∘ g) hgf (p' (f ∘ g)) .centre .glues h hh ⟩
      A.₁ h (p'' .part (f ∘ g) hgf)       ∎

    s : Section A p''
    s = Rsheaf p'' .centre
```

By assumption, $A$ is an $R$-sheaf, so our patch $p''$ on $R$ glues to
give an element $s : A(U)$ --- a section of $p''$, even. We must now
show that $A(f)(s) = p(f)$, for $f \in S$. Since $s$ only agrees with
$p''$ $R$-locally, this might be a problem: that's where the assumption
that $A$ is $f^*(R)$-local comes in (for $f \in S$): we can reduce this
to showing $A(gf)(s) = A(g)(p(f))$, with $fg \in R$. We would almost be
in trouble again, since $p''(fg)$ is only characterised $S$-locally, but
we can appeal to separatedness *again*, this time at $(fg)^*(S)$.  This
*finally* allows the calculation to go through:

```agda
    q : is-contr (Section A p)
    q .centre .whole = s .whole
    q .centre .glues f hf = R*sep f hf λ g hg → is-sheaf₁→is-separated₁ A _ (S*sheaf (f ∘ g) hg) λ h hh →
      A ⟪ h ⟫ (A ⟪ g ⟫ (A ⟪ f ⟫ s .whole)) ≡⟨ A.ap (A.collapse refl ∙ Rsheaf p'' .centre .glues (f ∘ g) hg) ⟩
      A ⟪ h ⟫ p'' .part (f ∘ g) hg        ≡⟨ S*sheaf (f ∘ g) hg (p' (f ∘ g)) .centre .glues h hh ⟩
      p .part ((f ∘ g) ∘ h) hh            ≡˘⟨ app p (assoc f g h) ⟩
      p .part (f ∘ g ∘ h) _               ≡˘⟨ p .patch f hf (g ∘ h) (subst (_∈ S) (sym (assoc f g h)) hh) ⟩
      A ⟪ g ∘ h ⟫ (p .part f hf)          ≡⟨ A.expand refl ⟩
      A ⟪ h ⟫ (A ⟪ g ⟫ p .part f hf)      ∎
    q .paths x = ext $ ap whole $ Rsheaf p'' .paths
      record { glues = λ f hf → sym $ ap whole (S*sheaf f hf (p' f) .paths
        record { glues = λ g hg → A.collapse refl ∙ x .glues (f ∘ g) hg }) }
```

<!--
```agda
module
  _ {o ℓ ℓs ℓc} {C : Precategory o ℓ} {J : Coverage C ℓc}
    {A : Functor (C ^op) (Sets ℓs)} (shf : is-sheaf J A)
  where

  open Precategory C
  open is-sheaf
  open Section
  open Patch

  private
    module A = Psh A
    module shf = is-sheaf shf
```
-->

## On a site

Now specialising to a site $(\cC, J)$ and a functor $A$ which is a
$J$-sheaf, we can show a few more pedestrian closure properties. First,
$A$ is a sheaf for any sieve that contains a $J$-covering sieve (call it
$R$):

```agda
  is-sheaf-factor
    : ∀ {U} (s : Sieve C U) (c : J · U)
    → (∀ {V} (f : Hom V U) → f ∈ J .cover c → f ∈ s)
    → is-sheaf₁ A s
  is-sheaf-factor s c c⊆s ps = done where
    sec' = shf.split (subset→patch c⊆s ps)
```

If $p$ is a patch on $S$ and $S$ contains $R$, we can restrict $p$ to a
patch $p'$ on $R$. Gluing $p'$, we obtain a section $s$ for $p$! Showing
this requires using the pullback-stability of $J$, though: We must show
that $A(f)(s) = p(f)$, for $f : V \to U \in S$, but $p$ is only
characterised for $f \in R$!

```agda
    sec : Section A ps
    sec .whole = sec' .whole
```

However, by passing to the pullback sieve $f^*(R)$, we're allowed to
show this assuming that we have some $g : W \to V$, with $fg \in R$. The
calculation goes through without problems:

```agda
    sec .glues f hf = ∥-∥-out! do
      (c' , sub) ← J .stable c f
      pure $ shf.separate c' λ g hg →
        A ⟪ g ⟫ (A ⟪ f ⟫ sec' .whole) ≡⟨ A.collapse refl ⟩
        A ⟪ f ∘ g ⟫ sec' .whole       ≡⟨ sec' .glues (f ∘ g) (sub _ hg) ⟩
        ps .part (f ∘ g) _           ≡˘⟨ ps .patch f hf g (c⊆s (f ∘ g) (sub g hg)) ⟩
        A ⟪ g ⟫ ps .part f hf        ∎

    done : is-contr (Section A ps)
    done .centre = sec
    done .paths x = ext $ shf.separate c λ f hf →
      A ⟪ f ⟫ sec' .whole ≡⟨ sec' .glues f hf ⟩
      ps .part f _        ≡˘⟨ x .glues f (c⊆s f hf) ⟩
      A ⟪ f ⟫ x .whole    ∎
```

As a specialisation of the lemma above, we can show that $A$ is a sheaf
for the pullback of any $J$-covering sieve. This is sharper than the
pullback-stability property, but they differ exactly by the theorem
above!

```agda
  is-sheaf-pullback
    : ∀ {V U} (c : J · U) (f : Hom V U) → is-sheaf₁ A (pullback f (J .cover c))
  is-sheaf-pullback c f p = ∥-∥-out! do
    (c' , sub) ← J .stable c f
    pure (is-sheaf-factor (pullback f (J .cover c)) c' sub p)
```

## Saturating sites

<!--
```agda
module _ {o ℓ ℓs} {C : Precategory o ℓ} where
  open Precategory C using (Hom ; id ; _∘_)
```
-->

Putting the two previous batches of lemmas together, given a site $J$,
we can define by induction a new site $\widehat{J}$ which definitionally
enjoys these extra closure properties, but which has exactly the same
sheaves as $J$; in the code, we refer to this as the `Saturation`{.Agda}
of $J$. This is actually a pretty simple process:

```agda
  data _∋_ (J : Coverage C ℓs) : {U : ⌞ C ⌟} → Sieve C U → Type (o ⊔ ℓ ⊔ ℓs) where
    inc : {U : ⌞ C ⌟} (c : J ʻ U) → J ∋ J .cover c

    max : ∀ {U} {R : Sieve C U} → id ∈ R → J ∋ R

    local
      : ∀ {U R} (hr : J ∋ R) {S : Sieve C U}
      → (∀ {V} (f : Hom V U) (hf : f ∈ R) → J ∋ pullback f S)
      → J ∋ S

    pull : ∀ {U V} (h : Hom V U) {R : Sieve C U} (hr : J ∋ R) → J ∋ pullback h R

    squash : ∀ {U} {R : Sieve C U} → is-prop (J ∋ R)
```

In addition to the constructor which ensures that a $J$-covering sieve
is $\widehat{J}$-covering, each of the constructors corresponds exactly
to one of the lemmas above:

- `max`{.Agda} corresponds to `is-sheaf-maximal`{.Agda};
- `local`{.Agda} corresponds to `is-sheaf-transitive`{.Agda};
- `pull`{.Agda} corresponds to `is-sheaf-pullback`{.Agda}.

Note that `is-sheaf-factor`{.Agda} can be derived, instead of being a
constructor, as shown below. We also truncate this type to ensure that a
sieve belongs to the saturation in at most one way.

```agda
  abstract
    incl
      : ∀ {J : Coverage C ℓs} {U} {R S : Sieve C U}
      → S ⊆ R → J ∋ S → J ∋ R
    incl {J = J} {S = S} sr us = local us λ f hf → subst (J ∋_) refl $
      max $ sr (f ∘ id) (S .closed hf id)
```

<!--
```agda
    ∋-intersect
      : ∀ {J : Coverage C ℓs} {U} {R S : Sieve C U}
      → J ∋ R → J ∋ S → J ∋ (R ∩S S)
    ∋-intersect {J = J} {R = R} {S = S} α β = local β
      (λ {V} f hf → subst (J ∋_) (ext λ h → Ω-ua (λ fhR → fhR , S .closed hf _) fst) (pull f α))
```
-->

```agda
  Saturation : Coverage C ℓs → Coverage C (o ⊔ ℓ ⊔ ℓs)
  Saturation J = from-stable-property (J ∋_) λ f R s → pull f s
```

<!--
```agda
  instance
    H-Level-∋ : ∀ {J : Coverage C ℓs} {U} {S : Sieve C U} {n} → H-Level (J ∋ S) (suc n)
    H-Level-∋ = prop-instance squash

module _ {o ℓ ℓs ℓp} {C : Precategory o ℓ} {J : Coverage C ℓs} {A : Functor (C ^op) (Sets ℓp)}  where
  open Cat C
```
-->

Proving that a $J$-sheaf is also a $\widehat{J}$-sheaf can be done very
straightforwardly, by induction. However, there is a gotcha: to get the
induction hypotheses we need for `local`{.Agda} without running afoul of
the termination checker, we must strengthen the motive of induction from
"$A$ is a sheaf for any $\widehat{J}$-covering sieve" to "$A$ is a sheaf
for any *pullback of* a $\widehat{J}$-covering sieve".

```agda
  is-sheaf-sat
    : is-sheaf J A
    → ∀ {V U R} (c : J ∋ R) (h : Hom V U)
    → is-sheaf₁ A (pullback h R)
```

To compensate for this extra strength, we must use
`is-sheaf-pullback`{.Agda} at the "leaves" `inc`{.Agda}. Other than
that, it's a very straightforward recursive computation:

```agda
  is-sheaf-sat shf (inc x) h = is-sheaf-pullback shf x h

  is-sheaf-sat _ (max {R = R} p) h = is-sheaf-maximal A $
    subst (_∈ R) id-comm-sym (R .closed p h)

  is-sheaf-sat shf {V} (local {U} {R} hR {S} x) h =
    let
      rem₁ : ∀ {W} (f : Hom W V) → h ∘ f ∈ S
           → is-separated₁ A (pullback f (pullback h R))
      rem₁ f hhf = is-sheaf₁→is-separated₁ A _ $
        subst-is-sheaf₁ A pullback-∘ (is-sheaf-sat shf hR (h ∘ f))

      rem₂ : ∀ {W} (f : Hom W V) → h ∘ f ∈ R
           → is-sheaf₁ A (pullback f (pullback h S))
      rem₂ f hf = subst-is-sheaf₁ A (pullback-id ∙ pullback-∘) $
        is-sheaf-sat shf (x (h ∘ f) hf) id
    in is-sheaf-transitive A rem₁ rem₂ (is-sheaf-sat shf hR h)

  is-sheaf-sat shf (pull h {R} hR) g = subst-is-sheaf₁ A pullback-∘ $
    is-sheaf-sat shf hR (h ∘ g)

  is-sheaf-sat shf (squash {R} x y i) h p = is-contr-is-prop
    (is-sheaf-sat shf x h p)
    (is-sheaf-sat shf y h p) i
```

Showing that a $\widehat{J}$-sheaf is also a $J$-sheaf is immediate.

```agda
  is-sheaf-saturation : is-sheaf J A ≃ is-sheaf (Saturation J) A
  is-sheaf-saturation .fst sheaf = from-is-sheaf₁ λ (R , hR) → subst-is-sheaf₁ A pullback-id $ is-sheaf-sat sheaf hR id
  is-sheaf-saturation .snd = biimp-is-equiv! _ λ shf → from-is-sheaf₁ λ c →
    to-is-sheaf₁ shf (J .cover c , inc c)

  module is-sheaf-saturation = Equiv is-sheaf-saturation
```

<!--
```agda
module sat {o ℓ ℓs ℓc} {C : Precategory o ℓ} {J : Coverage C ℓc} {A : Functor (C ^op) (Sets ℓs)} (shf : is-sheaf J A) where
  private module shf = is-sheaf (is-sheaf-saturation.to shf)

  whole : ∀ {U S} (w : J ∋ S) (p : Patch A S) → A ʻ U
  whole w = shf.whole (_ , w)

  abstract
    glues : ∀ {U} {S : Sieve C U} (w : J ∋ S) (p : Patch A S) → is-section A (whole w p) p
    glues w = shf.glues (_ , w)

    separate : ∀ {U} {S : Sieve C U} (w : J ∋ S) → is-separated₁ A S
    separate w = shf.separate (_ , w)

  split : ∀ {U} {S : Sieve C U} (w : J ∋ S) (p : Patch A S) → Section A p
  split w p .Section.whole = whole w p
  split w p .Section.glues = glues w p
```
-->
