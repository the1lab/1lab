<!--
```agda
{-# OPTIONS --lossy-unification #-}
open import Cat.Functor.Equivalence
open import Cat.Functor.Properties
open import Cat.Instances.Functor
open import Cat.Functor.Compose
open import Cat.Univalent
open import Cat.Prelude

import Cat.Functor.Reasoning.FullyFaithful as FfR
import Cat.Functor.Reasoning as FR
import Cat.Reasoning

open Functor
open _=>_
```
-->

```agda
module Cat.Univalent.Rezk.Universal where
```

<!--
```agda
private variable
  o ℓ : Level
  A B C C⁺ : Precategory o ℓ

private module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C using (_≅_)
  open _≅_ public

-- Using ∙/∙∙ over equational reasoning saves ~5k conversion checks
```
-->

# Universal property of the Rezk completion

With the [Rezk completion], we defined, for any precategory $\cC$, a
univalent category $\cC^+$, together with a _weak equivalence_
functor $R : \cC \to \cC^+$. We also stated, but did not in that
module _prove_, the universal property of the Rezk completion: The
functor $R$ is the universal map from $\cC$ to categories. This
module actually proves it, but be warned: the proof is _very_ technical,
and is mostly a calculation.

[Rezk completion]: Cat.Univalent.Rezk.html

In generic terms, universality of the Rezk completion follows from
univalent categories being the class of _local objects_ for the weak
equivalences^[a _weak equivalence_ is a fully faithful, essentially
surjective functor]: A category $\cC$ is univalent _precisely_ if any
weak equivalence $H : \cA \to \cB$ induces^[by [precomposition]]
a proper equivalence of categories $- \circ H : [\cB,\cC] \to [\cA,\cC]$.

[precomposition]: Cat.Functor.Compose.html

The high-level overview of the proof is as follows:

- For any [[eso functor]] $H : \cA \to \cB$, and for any $\cC$, all
precategories, the functor $- \circ H : [\cA,\cB] \to [\cB,\cC]$ is
faithful. This is the least technical part of the proof, so we do it
first.

- If $H$ is additionally full, then $- \circ H$ is [[fully
faithful|fully faithful functor]].

- If $H$ is a weak equivalence, and $\cC$ is [[univalent|univalent
category]], then $- \circ H$ is essentially surjective. By the principle
of unique choice, it is an equivalence, and thus^[since both its domain
and codomain are univalent] an isomorphism.

Luckily, we `already know`{.Agda ident=is-eso→precompose-is-faithful} that precomposition
with an eso functor extends to a faithful functor. Unfortunately, the
remaining two steps are both _quite_ technical: that's because we're given
some _mere_^[truncated] data, from the assumption that $H$ is a weak
equivalence, so to use it as proper data, we need to show that whatever
we want lives in a contractible space, after which we are free to
project only the data we are interested in, and forget about the coherences.

It will turn out, however, that the coherence data necessary to make
these types contractible is exactly the coherence data we need to show
that we are indeed building functors, natural transformations, etc. So,
not only do we need it to use unique choice, we also need it to show
we're doing category theory.

## Full-faithfulness

Let $A$, $B$, $C$ and $H$ be as before, except now assume that $H$ is
full (in addition to eso).

```agda
eso-full→pre-ff
  : (H : Functor A B)
  → is-eso H → is-full H
  → is-fully-faithful {C = Cat[ B , C ]} (precompose H)
eso-full→pre-ff {A = A} {B = B} {C = C} H H-eso H-full = res where
```

We will show that, for every natural transformation $\gamma : FH \to
GH$, and each $b : \cB$, there is a contractible type of "component
data" over $b$. These data consist of morphisms $g : Fb \to Gb$,
each equipped with a witness that $g$ acts naturally when faced with
isomorphisms $Ha \cong b$.

<!--
```agda
  module A = Cat.Reasoning A
  module B = Cat.Reasoning B
  module C = Cat.Reasoning C
  module H = FR H

  module _ (F G : Functor B C) (γ : F F∘ H => G F∘ H) where
    module F = FR F
    module FH = FR (F F∘ H)
    module G = FR G
    module GH = FR (G F∘ H)
    module γ = _=>_ γ
```
-->

In more detail, if we're given an [[essential fibre]] $(a,f)$ of $H$ over
$b$, we can use $f$ to "match up" our component $g$ with the components
of the natural transformation $\gamma$: since $\gamma_a : FH(a) \to
FG(a)$, we've claimed to have a $Fb \to Gb$, and someone has just handed
us a $H(a) \cong b$, then it darn well better be the case that $\gamma$ is

$$
FH(a) \xto{Ff} Fb \xto{g} Gb \xto{Gf\inv} FG(a)
$$.

```agda
    T : B.Ob → Type _
    T b = Σ (C.Hom (F.₀ b) (G.₀ b)) λ g →
      (a : A.Ob) (f : H.₀ a B.≅ b) →
      γ.η a ≡ G.₁ (f .from) C.∘ g C.∘ F.₁ (f .to)
```

We'll first show that components exist at all. Assume that we have some
$b : \cB$ and an essential fibre $(a_0, h_0)$ of $H$ over it^[Don't
worry about actually getting your hands on an $(a_0, h_0)$.]. In this
situation, guided by the compatibility condition (and isomorphisms being
just the best), we can actually _define_ the component to be "whatever
satisfies compatibility at $(a_0,h_0)$", and a short calculation
establishes that defining

<!--
```agda
    module Mk (b : B.Ob) (a₀ : A.Ob) (h : H.₀ a₀ B.≅ b) where
      private module h = B._≅_ h
```
-->

```agda
      g = G.₁ h.to C.∘ γ.η a₀ C.∘ F.₁ h.from
```

is indeed a possible choice. We present the formalisation below, but do
not comment on the calculation, leaving it to the curious reader to load
this file in Agda and poke around the proof.

```agda
      lemma : (a : A.Ob) (f : H.₀ a B.≅ b)
            → γ.η a ≡ G.₁ (f .from) C.∘ g C.∘ F.₁ (f .to)
      lemma a f = ∥-∥-out (C.Hom-set _ _ _ _) do
        (k , p)   ← H-full (h.from B.∘ B.to f)
        (k⁻¹ , q) ← H-full (B.from f B.∘ h.to)
        ∥_∥.inc $
             C.intror (F.annihilate
               (ap₂ B._∘_ q p ∙∙ B.cancel-inner h.invl ∙∙ f .invr))
          ∙∙ C.extendl (γ.is-natural _ _ _)
          ∙∙ ap₂ (λ e e' → G.₁ e C.∘ γ.η a₀ C.∘ F.₁ e') q p
          ∙∙ ap₂ (λ e e' → e C.∘ γ.η a₀ C.∘ e') (G.F-∘ _ _) (F.F-∘ _ _)
          ∙∙ C.pullr (ap (G.₁ h.to C.∘_) (C.pulll refl) ∙ C.pulll refl)
```

Anyway, because of how we've phrased the coherence condition, if $g$,
$g'$ both satisfy it, then we have $\gamma$ equal to both
$G(h)gF(h\inv)$ and $G(h)g'F(h\inv)$.^[I've implicitly used that $H$
is eso to cough up an $(a,h)$ over $b$, since we're proving a
proposition] Since isomorphisms are both monic and epic, we can cancel
$G(h)$ and $F(h\inv)$ from these equations to conclude $g = g'$.  Since
the coherence condition is a proposition, the type of component data
over $b$ is a proposition.

```agda
    T-prop : ∀ b → is-prop (T b)
    T-prop b (g , coh) (g' , coh') = Σ-prop-path! $ ∥-∥-out! do
      (a₀ , h) ← H-eso b
      pure $ C.iso→epic (F-map-iso F h) _ _
        (C.iso→monic (F-map-iso G (h B.Iso⁻¹)) _ _
          (sym (coh a₀ h) ∙ coh' a₀ h))
```

Given any $b$, $H$ being eso means that we [[merely]] have an essential
fibre $(a,h)$ of $H$ over $b$. But since the type of components over $b$
is a proposition, if we're going to use it to construct a component over
$b$, then we are granted the honour of actually getting hold of an
$(a,h)$ pair.

```agda
    mkT' : ∀ b → ∥ Essential-fibre H b ∥ → ∥ T b ∥
    mkT' b he = do
      (a₀ , h) ← he
      ∥_∥.inc (Mk.g b a₀ h , Mk.lemma b a₀ h)

    mkT : ∀ b → T b
    mkT b = ∥-∥-out (T-prop b) (mkT' b (H-eso b))
```

Another calculation shows that, since $H$ is full, given any pair of
essential fibres $(a, h)$ over $b$ and $(a', h')$ over $b'$, with a
mediating map $f : b \to b'$, we can choose a map $k : Ha \to Ha'$
satisfying $Hk = h'fh$, and since both the components at $b$ and $b$
"come from $\gamma$" (which is natural), we get a naturality result for
the transformation we're defining, too.

<details>
<summary>That computation is a bit weirder, so it's hidden in this
`<details>`{.html} tag.</summary>

```agda
    module
      _ {b b'} (f : B.Hom b b') (a a' : A.Ob)
        (h : H.₀ a B.≅ b) (h' : H.₀ a' B.≅ b')
      where
      private
        module h' = B._≅_ h'
        module h = B._≅_ h

      naturality : _
      naturality = ∥-∥-out (C.Hom-set _ _ _ _) do
        (k , p) ← H-full (h'.from B.∘ f B.∘ h.to)
        pure $ C.pullr (C.pullr (F.weave (sym
                  (B.pushl p ∙ ap₂ B._∘_ refl (B.cancelr h.invl)))))
            ∙∙ ap₂ C._∘_ refl (C.extendl (γ.is-natural _ _ _))
            ∙∙ C.extendl (G.weave (B.lswizzle p h'.invl))
```

</details>

Because of this naturality result, all the components we've chosen piece
together into a natural transformation. And since we defined $\delta$
parametrically over the choice of essential fibre, if we're looking at
some $Hb$, then we can choose the _identity_ isomorphism, from which it
falls out that $\delta H = \gamma$. Since we had already established that
$- \circ H$ is faithful, and now we've shown it is full, it is fully faithful.

```agda
    δ : F => G
    δ .η b = mkT b .fst
    δ .is-natural b b' f = ∥-∥-elim₂
      {P = λ α β → ∥-∥-out (T-prop b') (mkT' b' α) .fst C.∘ F.₁ f
                 ≡ G.₁ f C.∘ ∥-∥-out (T-prop b) (mkT' b β) .fst}
      (λ _ _ → C.Hom-set _ _ _ _)
      (λ (a' , h') (a , h) → naturality f a a' h h') (H-eso b') (H-eso b)

  full : is-full (precompose H)
  full {x = x} {y = y} γ = pure (δ _ _ γ , ext p) where
    p : ∀ b → δ _ _ γ .η (H.₀ b) ≡ γ .η b
    p b = subst
      (λ e → ∥-∥-out (T-prop _ _ γ (H.₀ b)) (mkT' _ _ γ (H.₀ b) e) .fst
           ≡ γ .η b)
      (squash (inc (b , B.id-iso)) (H-eso (H.₀ b)))
      (C.eliml (y .F-id) ∙ C.elimr (x .F-id))

  res : is-fully-faithful (precompose H)
  res =
    full+faithful→ff (precompose H)
      full
      (is-eso→precompose-is-faithful H H-eso)
```

## Essential surjectivity

The rest of the proof proceeds in this same way: Define a type which
characterises, up to a compatible space of choices, first the action on
morphisms of a functor which inverts $- \circ H$, and in terms of this type,
the action on morphisms. It's mostly the same trick as above, but a
_lot_ wilder. We do not comment on it too extensively: the curious
reader, again, can load this file in Agda and play around.

<!--
```agda
module
  _ {ao aℓ bo bℓ co cℓ}
    {A : Precategory ao aℓ} {B : Precategory bo bℓ} {C : Precategory co cℓ}
    (H : Functor A B) (H-eso : is-eso H) (H-ff : is-fully-faithful H)
    (c-cat : is-category C)
  where

  private
    module A = Cat.Reasoning A
    module B = Cat.Reasoning B
    module C = Cat.Reasoning C
    module H = FfR H H-ff
```
-->

The type of object-candidates `Obs`{.Agda} is indexed by a $b : \cB$,
and any object candidate $c$ must come with a family of isomorphisms
$k_h$ giving, for every way of expressing $b$ as coming from $Ha$, a way
of $c$ coming from $Fa$. To show this type is a proposition, we
additionally require a naturality condition for these isomorphisms.

```agda
  private module _ (F : Functor A C) where
    private module F = FR F

    Obs : B.Ob → Type _
    Obs b =
      Σ C.Ob λ c →
      Σ ((a : A.Ob) (h : H.₀ a B.≅ b) → F.₀ a C.≅ c) λ k →
      ((a , h) (a' , h') : Essential-fibre H b) (f : A.Hom a a') →
      h' .to B.∘ H.₁ f ≡ h .to →
      k a' h' .to C.∘ F.₁ f ≡ k a h .to
```

Note that we can _derive_ an object candidate over $b$ from a fibre
$(a,h)$ of $H$ over $b$. Moreover, this choice is a center of
contraction, so we can once more apply unique choice and the assumption
that $H$ is eso to conclude that every $b : \cB$ has an object
candidate over it.

```agda
    obj' : ∀ {b} → Essential-fibre H b → Obs b
    obj' (a₀ , h₀) .fst = F.₀ a₀
    obj' (a₀ , h₀) .snd .fst a h = F-map-iso F (H.iso.from (h₀ B.Iso⁻¹ B.∘Iso h))
    obj' (a₀ , h₀) .snd .snd (a , h) (a' , h') f p = F.collapse (H.ipushr p)

    Obs-is-prop : ∀ {b} (f : Essential-fibre H b) (c : Obs b) → obj' f ≡ c
    Obs-is-prop (a₀ , h₀) (c' , k' , β) =
      Σ-pathp (Univalent.iso→path c-cat c≅c') $
      Σ-prop-pathp! $
        funextP λ a → funextP λ h → C.≅-pathp _ _ $
          Univalent.Hom-pathp-reflr-iso c-cat {q = c≅c'}
            ( C.pullr (F.eliml (H.from-id (h₀ .invr)))
            ∙ β _ _ _ (H.ε-lswizzle (h₀ .invl)))
      where
        ckα = obj' (a₀ , h₀)
        c = ckα .fst
        k = ckα .snd .fst
        α = ckα .snd .snd
        c≅c' = k' a₀ h₀ C.∘Iso k a₀ h₀ C.Iso⁻¹
```

<!--
```agda
    summon : ∀ {b} → ∥ Essential-fibre H b ∥ → is-contr (Obs b)
    summon f = ∥-∥-out is-contr-is-prop do
      f ← f
      pure $ contr (obj' f) (Obs-is-prop f)

    G₀ : B.Ob → C.Ob
    G₀ b = summon {b = b} (H-eso b) .centre .fst

    k : ∀ {b} a (h : H.₀ a B.≅ b) → F.₀ a C.≅ G₀ b
    k {b = b} a h = summon {b = b} (H-eso b) .centre .snd .fst a h

    kcomm
      : ∀ {b} ((a , h) (a' , h') : Essential-fibre H b) (f : A.Hom a a')
      → h' .to B.∘ H.₁ f ≡ h .to → k a' h' .to C.∘ F.₁ f ≡ k a h .to
    kcomm {b} f1 f2 f w = summon {b = b} (H-eso b) .centre .snd .snd f1 f2 f w
```
-->

We will write `G₀`{.Agda} for the canonical choice of object candidate,
and `k`{.Agda} for the associated family of isomorphisms. The type of
morphism candidates over $f : b \to b'$ consists of maps $G_0(b) \to
G_0(b')$ which are compatible with the reindexing isomorphisms $k$ for
any essential fibre $(a,h)$ over $b$, $(a',h')$ over $b'$, and map $l : a
\to a'$ satisfying $h'H(l) = fh$.

```agda
    compat : ∀ {b b'} (f : B.Hom b b') → C.Hom (G₀ b) (G₀ b') → Type _
    compat {b} {b'} f g =
      ∀ a (h : H.₀ a B.≅ b) a' (h' : H.₀ a' B.≅ b') (l : A.Hom a a')
      → h' .to B.∘ H.₁ l ≡ f B.∘ h .to
      → k a' h' .to C.∘ F.₁ l ≡ g C.∘ k a h .to

    Homs : ∀ {b b'} (f : B.Hom b b') → Type _
    Homs {b = b} {b'} f = Σ (C.Hom (G₀ b) (G₀ b')) (compat f)
```

<details>
<summary>It will again turn out that any initial choice of fibre over
$b$ and $b'$ gives a morphism candidate over $f : b \to b'$, and the
compatibility data is exactly what we need to show the type of morphism
candidates is a proposition.</summary>

This proof _really_ isn't commented. I'm sorry.

```agda
    module _ {b b'} (f : B.Hom b b')
             a₀ (h₀ : H.₀ a₀ B.≅ b)
             a₀' (h₀' : H.₀ a₀' B.≅ b') where
      l₀ : A.Hom a₀ a₀'
      l₀ = H.from (h₀' .from B.∘ f B.∘ h₀ .to)

      p : h₀' .to B.∘ H.₁ l₀ ≡ (f B.∘ h₀ .to)
      p = H.ε-lswizzle (h₀' .invl)

      g₀ : C.Hom (G₀ b) (G₀ b')
      g₀ = k a₀' h₀' .to C.∘ F.₁ l₀ C.∘ k a₀ h₀ .from

      module _ a (h : H.₀ a B.≅ b) a' (h' : H.₀ a' B.≅ b')
                (l : A.Hom a a') (w : h' .to B.∘ H.₁ l ≡ f B.∘ h .to) where
        m : a₀ A.≅ a
        m = H.iso.from (h B.Iso⁻¹ B.∘Iso h₀)

        m' : a₀' A.≅ a'
        m' = H.iso.from (h' B.Iso⁻¹ B.∘Iso h₀')

        α : k a₀ h₀ .from ≡ F.₁ (m .from) C.∘ k a h .from
        α = C.inverse-unique₀ (k a₀ h₀) (k a h C.∘Iso F-map-iso F m) $
          sym (kcomm _ _ _ (H.ε-lswizzle (h .invl)))

        γ : H.₁ (m' .to) B.∘ H.₁ l₀ ≡ H.₁ l B.∘ H.₁ (m .to)
        γ =  B.pushl (H.ε _)
          ∙∙ ap₂ B._∘_ refl (p ∙
              B.pushl (B.insertr (h .invl) ∙ ap₂ B._∘_ (sym w) refl))
          ∙∙ B.deletel (h' .invr)
          ∙ ap₂ B._∘_ refl (sym (H.ε _))

        γ' : l₀ A.∘ m .from ≡ m' .from A.∘ l
        γ' = A.iso→monic m' _ _ $ A.extendl (H.injective (H.swap γ))
                               ∙∙ A.elimr (m .invl)
                               ∙∙ A.insertl (m' .invl)

        δ : g₀ C.∘ k a h .to ≡ k a' h' .to C.∘ F.₁ l
        δ = C.pullr ( C.pullr refl ∙∙ ap₂ C._∘_ refl (C.pushl α)
                   ∙∙ C.pulll refl ∙ C.elimr (k a h .invr))
          ∙∙ ap₂ C._∘_ refl (F.weave γ')
          ∙∙ C.pulll (C.pushl (sym (kcomm _ _ _ (H.ε-lswizzle (h' .invl))))
              ∙ C.elimr (F.annihilate (m' .invl)))

      Homs-pt : Homs f
      Homs-pt = g₀ , λ a h a' h' l w → sym (δ a h a' h' l w)

      Homs-prop' : (h' : Homs f) → h' .fst ≡ g₀
      Homs-prop' (g₁ , w) = C.iso→epic (k a₀ h₀) _ _
        (sym (δ a₀ h₀ a₀' h₀' l₀ p ∙ w a₀ h₀ a₀' h₀' l₀ p))

    Homs-contr' : ∀ {b b'} (f : B.Hom b b') → ∥ is-contr (Homs f) ∥
    Homs-contr' {b = b} {b'} f = do
      (a₀ , h)   ← H-eso b
      (a₀' , h') ← H-eso b'
      inc (contr (Homs-pt f a₀ h a₀' h') λ h' → Σ-prop-path!
        (sym (Homs-prop' f _ _ _ _ h')))

    Homs-contr : ∀ {b b'} (f : B.Hom b b') → is-contr (Homs f)
    Homs-contr f = ∥-∥-out! (Homs-contr' f)

    G₁ : ∀ {b b'} → B.Hom b b' → C.Hom (G₀ b) (G₀ b')
    G₁ f = Homs-contr f .centre .fst
```

</details>


<details>
<summary>Using the compatibility condition, and choices of $(a, h)$, we can show
that the assignment of morphism candidates _does_ assemble into a
functor.</summary>

```agda
    module G∘ {x y z} (f : B.Hom y z) (g : B.Hom x y)
              {ax ay az} (hx : H.₀ ax B.≅ x) (hy : H.₀ ay B.≅ y)
              (hz : H.₀ az B.≅ z) where

      af : A.Hom ay az
      af = H.from (hz .from B.∘ f B.∘ hy .to)

      ag : A.Hom ax ay
      ag = H.from (hy .from B.∘ g B.∘ hx .to)

      h' : H.₁ (af A.∘ ag) ≡ hz .from B.∘ f B.∘ g B.∘ hx .to
      h' = H.ε-expand refl ∙ B.pullr (B.cancel-inner (hy .invl))

      commutes : G₁ (f B.∘ g) ≡ G₁ f C.∘ G₁ g
      commutes = C.iso→epic (k ax hx) _ _ $
          sym (Homs-contr (f B.∘ g) .centre .snd ax hx az hz (af A.∘ ag)
                (ap₂ B._∘_ refl h' ∙∙ B.cancell (hz .invl) ∙∙ B.pulll refl))
        ∙ sym ( C.pullr (sym (Homs-contr g .centre .snd ax hx ay hy ag
                  (H.ε-lswizzle (hy .invl))))
              ∙ C.pulll (sym (Homs-contr f .centre .snd ay hy az hz af
                  (H.ε-lswizzle (hz .invl))))
              ∙ F.pullr refl)
```

</details>

In this manner, the assignment of object candidates and morphism
candidates fits together into a functor $G : \cB \to \cC$. After
finishing this, we have to show that $GH = F$. But the compatibility
data which we have used to uniquely characterise $G$... uniquely
characterises $G$, after all, and it does so as _composing with $H$ to
give $F$_.

```agda
    G : Functor B C
    G .F₀ b = G₀ b
    G .F₁ f = G₁ f

    G .F-id = ap fst $ Homs-contr B.id .paths $ C.id , λ a h a' h' l w →
      sym (C.idl _ ∙ sym (kcomm (a , h) (a' , h') l (w ∙ B.idl _)))
```

Note that we proved^[in the second `<details>`{.Agda} tag above] that
$G_1$ is functorial given _choices_ of essential fibres of all three
objects involved in the composition. Since we're showing an equality in
a set --- a proposition --- these choices don't matter, so we can use
essential surjectivity of $H$.

```agda
    G .F-∘ {x} {y} {z} f g = ∥-∥-out! do
      (ax , hx) ← H-eso x
      (ay , hy) ← H-eso y
      (az , hz) ← H-eso z
      inc (G∘.commutes f g hx hy hz)
```

To use the unique charactersation of $G$ as "the functor satisfying $GH
= F$", observe: for any $x : \cA$, the object $F(x)$ can be made into
an object candidate over $H(x)$, and since the type of object candidates
is a proposition, our candidate $F(x)$ is identical to the value of
$GH(x)$.  That's half of $GH = F$ established right off the bat!

```agda
    module _ (x : A.Ob) where
      hf-obs : Obs (H.₀ x)
      hf-obs .fst = F.F₀ x
      hf-obs .snd .fst a h = F-map-iso F (H.iso.from h)
      hf-obs .snd .snd (a , h) (a' , h') f α = F.collapse (H.inv∘l α)

      abstract
        objp : G₀ (H.₀ x) ≡ F.₀ x
        objp = ap fst $ summon {H.₀ x} (H-eso _) .paths hf-obs
```

<!--
```agda
        kp : (a : A.Ob) (h : H.₀ a B.≅ H.₀ x)
           → PathP (λ i → F.₀ a C.≅ objp i) (k a h) (hf-obs .snd .fst a h)
        kp a h = ap (λ e → e .snd .fst a h)
          (summon {H.₀ x} (H-eso (H.₀ x)) .paths hf-obs)
```
-->

_Over that identification_, we can show that, for any $f : x \to y$ in
$\cA$, the value $F(f)$ is also a candidate for the morphism $GH(f)$,
so these are also identical. This proof is a bit hairier, because $F(f)$
only has the right type if we adjust it by the proof that $GH(x) =
F(x)$: we have to transport $F(f)$, and then as punishment for our
hubris, invoke a lot of technical lemmas about the characterisation of
`PathP`{.Agda} in the morphism spaces of (pre)categories.

```agda
    module _ {x y} (f : A.Hom x y) where
      hom' : Homs (H.₁ f)
      hom' .fst = transport (λ i → C.Hom (objp x (~ i)) (objp y (~ i))) (F.₁ f)
      hom' .snd a h a' h' l w = sym $
        C.pushl (Hom-transport C (sym (objp x)) (sym (objp y)) (F.₁ f))
        ∙∙ ap₂ C._∘_ refl
          ( C.pullr (from-pathp-from C (objp x) (λ i → kp x a h i .to))
          ∙ F.weave (H.ε-twist (sym w)))
        ∙∙ C.pulll (from-pathp-to C (sym (objp y)) λ i → kp y a' h' (~ i) .to)

      homp : transport (λ i → C.Hom (objp x (~ i)) (objp y (~ i))) (F.₁ f)
           ≡ Homs-contr (H.₁ f) .centre .fst
      homp = ap fst $ sym $ Homs-contr (H.₁ f) .paths hom'

    correct : G F∘ H ≡ F
    correct = Functor-path objp λ {x} {y} f → symP
      {A = λ i → C.Hom (objp x (~ i)) (objp y (~ i))} $
      to-pathp (homp f)
```

Since we've shown that $GH = F$, so in particular $GH \cong F$, we've
now put together proofs that $- \circ H$ is fully faithful and, since the
construction above works for any $F$, essentially surjective. Even
better, since we've actually _constructed_ a functor $G$, we've shown
that $- \circ H$ is **split** essentially surjective! Since $[-,\cC]$ is
univalent whenever $\cC$ is, the splitting would be automatic, but
this is a nice strengthening.

```agda
  weak-equiv→pre-equiv : is-equivalence {C = Cat[ B , C ]} (precompose H)
  weak-equiv→pre-equiv = ff+split-eso→is-equivalence {F = precompose H}
    (eso-full→pre-ff H H-eso λ g → inc (H.from g , H.ε g))
    λ F → G F , path→iso (correct F)
```

And since a functor is an equivalence of categories iff. it is an
isomorphism of categories, we also have that the rule sending $F$ to its
$G$ is an equivalence of types.

```agda
  weak-equiv→pre-iso : is-precat-iso {C = Cat[ B , C ]} (precompose H)
  weak-equiv→pre-iso = is-equivalence→is-precat-iso (precompose H) weak-equiv→pre-equiv
    (Functor-is-category c-cat)
    (Functor-is-category c-cat)
```

Restating the result that $- \circ H$ acts on objects as an equivalence of
types, we have the following result: If $R : \cC \to \cC^+$ is a
weak equivalence (a fully faithful and essentially surjective functor),
then for any category $\cD$ and functor $G : \cC \to \cD$,
there is a contractible space(!) of extensions $H : \cC^+ \to \cD$
which factor $G$ through $F$.

```agda
weak-equiv→reflection
  : (F : Functor C C⁺) → is-eso F → is-fully-faithful F
  → {D : Precategory o ℓ} → is-category D
  → (G : Functor C D)
  → is-contr (Σ (Functor C⁺ D) λ H → H F∘ F ≡ G)
weak-equiv→reflection F F-eso F-ff D-cat G =
  weak-equiv→pre-iso F F-eso F-ff D-cat
    .is-precat-iso.has-is-iso .is-eqv G
```

Note that this is only _half_ of the point of the Rezk completion: we
would also like for $\cC^+$ to be univalent, but that is not
necessary for $D$ to think that precomposition with $F$ is an
isomorphism.
