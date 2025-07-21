<!--
```agda
open import 1Lab.Path.Reasoning
open import 1Lab.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Group.Concrete
open import Algebra.Group.Homotopy
open import Algebra.Group

open import Data.Set.Truncation

open import Homotopy.Space.Suspension
open import Homotopy.Connectedness
open import Homotopy.Conjugation
open import Homotopy.Truncation
open import Homotopy.Loopspace
open import Homotopy.HSpace
open import Homotopy.Wedge
open import Homotopy.Base
open import Homotopy.Join

open ConcreteGroup
```
-->

```agda
module Homotopy.Space.Suspension.Pi2 {ℓ} (grp : ConcreteGroup ℓ) (hg : HSpace (grp .B)) where
```

# π₂ of a suspension

<!--
```agda
open ConcreteGroup grp renaming (B to BG ; pt to G₀) using ()
open HSpace {ℓ = ℓ} {A* = BG} hg

private
  G : Type ℓ
  G = ⌞ grp ⌟

  ΣG : Type ℓ
  ΣG = Susp G

  ∥_∥₁ : Type ℓ → Type ℓ
  ∥ X ∥₁ = n-Tr X 3

  μr : ∀ a → ⌞ G ⌟ ≃ ⌞ G ⌟
  μr a = _ , μ-invr a
```
-->

We will prove that the second [[homotopy group]] $\pi_2(\Susp G)$ of the
[[suspension]] of a [[pointed]] [[connected]] [[groupoid]] $G$ with an
[[H-space]] structure (hence an [[abelian|concrete abelian group]]
[[concrete group]]) is $\Loop G$.

We start by defining a type family `Hopf`{.Agda} over $\Susp G$ which is
$G$ on both poles and sends the $x$th `merid`{.Agda}ian to the H-space
multiplication $\mu(-,x)$ on the right, which is an equivalence by
assumption. We will show, by an encode-decode argument, that the
groupoid [[truncation]] $\| \rm{north} \is x \|_1$ is equivalent to the
fibre of `Hopf`{.Agda} over $x$.

As the name implies, the `Hopf`{.Agda} type family is the synthetic
equivalent of the classic Hopf fibration, though here we have evidently
generalised it beyond a map $S^3 \to S^1$. [Below] we prove that the
total space of the `Hopf`{.Agda} is the [[join|join of types]] $G * G$.

[Below]: #the-hopf-fibration

```agda
Hopf : ΣG → Type _
Hopf north       = G
Hopf south       = G
Hopf (merid x i) = ua (μr x) i
```

To encode, we use truncation recursion, since `Hopf`{.Agda} is a family
of groupoids by construction, and since we have $G_0 :
\operatorname{Hopf}(\rm{north})$ we can transport it along a
$\rm{north} \is x$ to get a point in an arbitrary fibre.

```agda
encode' : ∀ x → ∥ north ≡ x ∥₁ → Hopf x
encode' x = n-Tr-rec (tr x) λ p → subst Hopf p G₀ where
  tr : ∀ x → is-groupoid (Hopf x)
  tr = Susp-elim-prop (λ s → hlevel 1) (grp .has-is-groupoid) (grp .has-is-groupoid)
```

To decode an element of `Hopf`{.Agda} we use suspension recursion. On
the north pole we can use the suspension map $\sigma : A \to_*
\Loop \Susp A$; on the south pole this is just a meridian; and on the
meridians we must prove that these agree. Through a short calculation we
can reduce this to a coherence lemma relating the composition of
meridians and the H-space multiplication.

```agda
decode' : ∀ x → Hopf x → ∥ north ≡ x ∥₁
decode' = Susp-elim _ (n-Tr.inc ∘ suspend BG) (n-Tr.inc ∘ merid) λ x → ua→ λ a → to-pathp $
  inc (subst (north ≡_) (merid x) (suspend BG a)) ≡⟨ ap n-Tr.inc (subst-path-right (suspend BG a) (merid x)) ⟩
  inc ((merid a ∙ sym (merid G₀)) ∙ merid x)      ≡˘⟨ ap n-Tr.inc (∙-assoc _ _ _) ⟩
  inc (merid a ∙ sym (merid G₀) ∙ merid x)        ≡⟨ merid-μ a x ⟩
  inc (merid (μ a x))                             ∎
  where
```

To show this coherence, we can use the [[wedge connectivity]] lemma. It
will suffice to do so, in turn, when $b = G_0$, when $a = G_0$, and then
to show that these agree. In either case we must show something like
$$
\merid{a}\cdot (\merid{G_0})\inv \cdot \merid{G_0} = \merid{\mu(a,G_0)}
$$,
which is easy to do with the pre-existing coherence lemmas
`∙∙-introl`{.Agda} and `∙∙-intror`{.Agda}, and the H-space unit laws.

```agda
  merid-μ : ∀ a b → inc (merid a ∙ sym (merid G₀) ∙ merid b) ≡ inc (merid (μ a b))
  merid-μ =
    let
      α = merid G₀

      P : (a b : ⌞ G ⌟) → Type ℓ
      P a b = Path ∥ north ≡ south ∥₁ (inc (merid a ∙ sym α ∙ merid b)) (inc (merid (μ a b)))

      p1 : ∀ a → P a G₀
      p1 a = ap n-Tr.inc $
           sym (double-composite _ _ _)
        ∙∙ sym (∙∙-intror (merid a) (sym α))
        ∙∙ ap merid (sym (idr a))

      p2 : ∀ b → P G₀ b
      p2 b = ap n-Tr.inc $
           sym (double-composite _ _ _)
        ∙∙ sym (∙∙-introl (merid b) α)
        ∙∙ ap merid (sym (idl b))
```

Moreover, it is easy to show that these agree: by construction we're
left with showing that `∙∙-introl` and `∙∙-intror` agree when all three
paths are the same, and by path induction we may assume that this one
path is refl; In that case, they agree definitionally.

```agda
      coh : p1 G₀ ≡ p2 G₀
      coh = ap (ap n-Tr.inc) $ ap₂ (_∙∙_∙∙_ (sym (double-composite α (sym α) α)))
        (ap sym (J (λ y p → ∙∙-intror p (sym p) ≡ ∙∙-introl p p) refl α))
        (ap (ap merid ∘ sym) (sym id-coh))

      c = is-connected∙→is-connected (grp .has-is-connected)
    in Wedge.elim {A∙ = BG} {BG} 0 0 c c (λ _ _ → hlevel 2) p1 p2 coh
```

<details>
<summary>
We have thus constructed maps between $\operatorname{Hopf}(x)$ and the
truncation of the based path space $\| \rm{north} \is x \|_1$. We must
then show that these are inverses, which, in both directions, are simple
calculations.

```agda
opaque
  ΩΣG≃G : ∥ north {A = fst BG} ≡ north ∥₁ ≃ G
  ΩΣG≃G .fst = encode' north
```

</summary>

```agda
  ΩΣG≃G .snd = is-iso→is-equiv (iso (decode' north) invl (invr north)) where abstract
    invl : ∀ a → encode' north (decode' north a) ≡ a
    invl a = Regularity.fast! (
      Equiv.from (flip μ G₀ , μ-invr G₀) (μ G₀ a) ≡⟨ ap (λ e → Equiv.from e (μ G₀ a)) {x = _ , μ-invr G₀} {y = id≃} (ext idr) ⟩
      μ G₀ a                                      ≡⟨ idl a ⟩
      a                                           ∎)
```

To show that decoding inverts encoding, we use the extra generality
afforded by the $x$ parameter to apply path induction.

```agda
    invr : (x : ΣG) (p : ∥ north ≡ x ∥₁) → decode' x (encode' x p) ≡ p
    invr x = n-Tr-elim! _ $ J
      (λ x p → decode' x (encode' x (inc p)) ≡ inc p)
      (ap n-Tr.inc
        ( ap₂ _∙_ (ap merid (transport-refl _)) refl
        ∙ ∙-invr (merid G₀)))
```
</details>

This equivalence is pointed, almost by definition.

```agda
  ΩΣG≃∙G : n-Tr∙ (Ω¹ (Σ¹ BG)) 3 ≃∙ BG
  ΩΣG≃∙G = ΩΣG≃G , transport-refl _
```

Furthermore, note that, by construction, the inverse pointed map
$G \to_* \| \Loop \Susp G \|_1$ of this equivalence is none other than
`suspend∙`{.Agda} followed by the inclusion into the groupoid truncation.

```agda
  ΩΣG≃∙G-inv : Equiv∙.from∙ ΩΣG≃∙G ≡ inc∙ ∘∙ suspend∙ BG
  ΩΣG≃∙G-inv = homogeneous-funext∙ λ _ → refl
```

Finally, we can apply $\Loop$ to the equivalence above and use some
pre-existing lemmas to show that the [[set truncation]] of the double
[[loop space]] $\Loop^2 \Susp G$ is equivalent to $\Loop G$.
A couple more short calculations which we omit show that this equivalence
preserves path composition, i.e. is an isomorphism of homotopy groups
$\pi_2(\Susp G) \cong \pi_1(G)$, and that the inverse map is the
expected suspension map $\Loop \sigma$ up to truncation.

```agda
Ω²ΣG≃ΩG : ∥ ⌞ Ωⁿ 2 (Σ¹ BG) ⌟ ∥₀ ≃ ⌞ Ω¹ BG ⌟
Ω²ΣG≃ΩG =
  ⌞ πₙ₊₁ 1 (Σ¹ BG) ⌟            ≃⟨ n-Tr-set ⟩
  ⌞ n-Tr∙ (Ωⁿ 2 (Σ¹ BG)) 2 ⌟    ≃⟨ n-Tr-Ω¹ (Ω¹ (Σ¹ BG)) 1 .fst ⟩
  ⌞ Ω¹ (n-Tr∙ (Ω¹ (Σ¹ BG)) 3) ⌟ ≃⟨ Ω¹-ap ΩΣG≃∙G .fst ⟩
  ⌞ Ω¹ BG ⌟                     ≃∎

opaque
  unfolding Ω¹-ap

  Ω²ΣG≃ΩG-pres : is-group-hom
    (πₙ₊₁ 1 (Σ¹ BG) .snd)
    (π₁Groupoid.π₁ BG (grp .has-is-groupoid) .snd)
    (Ω²ΣG≃ΩG .fst)

  Ω²ΣG≃ΩG-inv
    : ∀ (l : ⌞ Ω¹ BG ⌟)
    → Equiv.from Ω²ΣG≃ΩG l ≡ inc (Ω¹-map (suspend∙ BG) .fst l)
```

<!--
```agda
  Ω²ΣG≃ΩG-pres = record { pres-⋆ = elim! λ p q → trace p q .snd } where
    open Σ Ω²ΣG≃ΩG renaming (fst to f0) using ()
    instance
      _ : ∀ {n} → H-Level ⌞ G ⌟ (3 + n)
      _ = basic-instance 3 (grp .has-is-groupoid)

    trace : (p q : refl ≡ refl) → (∥ ⌞ Ωⁿ 2 (Σ¹ BG) ⌟ ∥₀ , inc (p ∙ q)) ≃∙ (⌞ Ω¹ BG ⌟ , f0 (inc p) ∙ f0 (inc q))
    trace p q =
      ⌞ πₙ₊₁ 1 (Σ¹ BG) ⌟ , inc (p ∙ q)         ≃∙⟨ n-Tr-set , refl ⟩
      ⌞ n-Tr∙ (Ωⁿ 2 (Σ¹ BG)) 2 ⌟ , inc (p ∙ q) ≃∙⟨ n-Tr-Ω¹ _ 1 .fst , n-Tr-Ω¹-∙ _ 1 p q ⟩
      ⌞ Ω¹ (n-Tr∙ (Ω¹ (Σ¹ BG)) 3) ⌟ , _        ≃∙⟨ Ω¹-ap ΩΣG≃∙G .fst , Ω¹-map-∙ (Equiv∙.to∙ ΩΣG≃∙G) (n-Tr-Ω¹ _ 1 · inc p) (n-Tr-Ω¹ _ 1 · inc q) ⟩
      ⌞ Ω¹ BG ⌟ , f0 (inc p) ∙ f0 (inc q)      ≃∙∎

  Ω²ΣG≃ΩG-inv l = trace .snd where
    trace : (⌞ Ω¹ BG ⌟ , l) ≃∙ (⌞ πₙ₊₁ 1 (Σ¹ BG) ⌟ , inc (Ω¹-map (suspend∙ BG) · l))
    trace =
      ⌞ Ω¹ BG ⌟                     , l                                ≃∙⟨ Ω¹-ap ΩΣG≃∙G .fst e⁻¹ , (Ω¹-ap-inv ΩΣG≃∙G ·ₚ l) ∙ ap (λ x → Ω¹-map x · l) ΩΣG≃∙G-inv ⟩
      ⌞ Ω¹ (n-Tr∙ (Ω¹ (Σ¹ BG)) 3) ⌟ , Ω¹-map (inc∙ ∘∙ suspend∙ BG) · l ≃∙˘⟨ n-Tr-Ω¹ _ 1 .fst , (n-Tr-Ω¹-inc _ 1 ·ₚ _) ∙ (Ω¹-map-∘ inc∙ (suspend∙ BG) ·ₚ l) ⟩
      ⌞ n-Tr∙ (Ωⁿ 2 (Σ¹ BG)) 2 ⌟    , inc (Ω¹-map (suspend∙ BG) · l)   ≃∙˘⟨ n-Tr-set , refl ⟩
      ⌞ πₙ₊₁ 1 (Σ¹ BG) ⌟            , inc (Ω¹-map (suspend∙ BG) · l)   ≃∙∎
```
-->

```agda
π₂ΣG≅ΩG : πₙ₊₁ 1 (Σ¹ BG) Groups.≅ π₁Groupoid.π₁ BG (grp .has-is-groupoid)
π₂ΣG≅ΩG = total-iso Ω²ΣG≃ΩG Ω²ΣG≃ΩG-pres
```

## The Hopf fibration

We can now prove that the total space of the Hopf fibration defined
above is the [[join]] of $G$ with itself.

```agda
join→hopf : (G ∗ G) → Σ _ Hopf
join→hopf (inl x) = north , x
join→hopf (inr x) = south , x
join→hopf (join a b i) = record
  { fst = merid (a \\ b) i
  ; snd = attach (∂ i) (λ { (i = i0) → a ; (i = i1) → b })
    (inS (μ-\\-l a b i))
  }
```

```agda
join→hopf-split : ∀ x p → fibre join→hopf (x , p)
join→hopf-split = Susp-elim _
  (λ p → inl p , refl)
  (λ p → inr p , refl)
  (λ x i → filler x i i1)

  module surj where module _ (x : fst BG) where
    coh : ∀ a → PathP
      (λ i → fibre join→hopf (merid x i , ua-inc (μr x) a i))
      (inl a , refl) (inr (μ a x) , refl)
    coh a i .fst = join a (μ a x) i
    coh a i .snd j .fst = merid (μ-\\-r a x j) i
    coh a i .snd j .snd = attach (∂ i)
      (λ { (i = i0) → a ; (i = i1) → μ a x })
      (inS (∨-square (μ-zig a x) j i))

    open ua→ {e = μr x} {B = λ i z → fibre join→hopf (merid x i , z)} {f₀ = λ p → inl p , refl} {f₁ = λ p → inr p , refl} coh public

hopf→join : (Σ _ Hopf) → G ∗ G
hopf→join a = uncurry join→hopf-split a .fst

hopf→join→hopf : is-right-inverse hopf→join join→hopf
hopf→join→hopf a = uncurry join→hopf-split a .snd

join→hopf→join : is-left-inverse hopf→join join→hopf
join→hopf→join (inl x) = refl
join→hopf→join (inr x) = refl
join→hopf→join (join a b i) =
  let it = attach (∂ i) (λ { (i = i0) → a ; (i = i1) → b }) (inS (μ-\\-l a b i)) in
  comp (λ l → surj.filler (a \\ b) i l it .fst ≡ join a b i) (∂ i) λ where
    j (j = i0) → λ k → join a (μ-\\-l a b (i ∨ k)) (~ k ∨ i)
    j (i = i0) → λ k → join a (μ-\\-l a b k) (~ j ∧ ~ k)
    j (i = i1) → λ k → inr b

∫Hopf≃join : Σ _ Hopf ≃ (⌞ G ⌟ ∗ ⌞ G ⌟)
∫Hopf≃join .fst = hopf→join
∫Hopf≃join .snd = is-iso→is-equiv (iso join→hopf join→hopf→join hopf→join→hopf)
```
