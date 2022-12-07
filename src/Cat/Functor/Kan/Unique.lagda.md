```agda
open import Cat.Instances.Functor.Compose
open import Cat.Instances.Functor
open import Cat.Functor.Base
open import Cat.Functor.Kan
open import Cat.Prelude

import Cat.Reasoning

module Cat.Functor.Kan.Unique

```

<!--
```agda
  {o ℓ o′ ℓ′ o′′ ℓ′′}
  {C : Precategory o ℓ} {C′ : Precategory o′ ℓ′} {D : Precategory o′′ ℓ′′}
  (dcat : is-category D)
  (p : Functor C C′) (F : Functor C D)
  where
```
-->

# Uniqueness of Kan extensions

Since [(left) Kan extensions] are defined by a universal property (they
are partial values of a specific [adjunction]), they are unique: When
$\ca{D}$ is a category, then the type $\Lan_p(F)$ of left Kan extensions
of $F$ along $p$ is a proposition.

[(left) Kan extensions]: Cat.Functor.Kan.html
[adjunction]: Cat.Functor.Kan.Global.html

```agda
Lan-is-prop : is-prop (Lan p F)
Lan-is-prop L₁ L₂ = Lan-unique module Lan-unique where
```

We diagram the situation generically as follows: $p$ and $F$ are fixed,
with $G$ and $G'$ being both left extensions of $F$ along $p$. The
functor $G$ (resp. $G'$) is equipped with a natural transformation $\eta
: F \to Gp$ (resp. $\eta' : F \to G'p$), and if $M$ is equipped with
$\theta : F \to Mp$, then $G$ can cough up a _unique_ natural
transformation $\sigma_\theta : G \to M$ (resp. $\sigma'_\theta : G' \to
M$) making everything in sight commute.

~~~{.quiver .tall-2}
\[\begin{tikzcd}
  C \\
  &&& D \\
  \\
  & {C'}
  \arrow["p"', from=1-1, to=4-2]
  \arrow["F", from=1-1, to=2-4]
  \arrow[""{name=0, anchor=center, inner sep=0}, "M"{description, pos=0.2}, dashed, from=4-2, to=2-4]
  \arrow[""{name=1, anchor=center, inner sep=0}, "G"{description}, curve={height=-24pt}, from=4-2, to=2-4]
  \arrow[""{name=2, anchor=center, inner sep=0}, "{G'}"{description}, curve={height=24pt}, from=4-2, to=2-4]
  \arrow["{\sigma'}"', shorten <=3pt, shorten >=3pt, Rightarrow, from=2, to=0]
  \arrow["\sigma"', shorten <=4pt, shorten >=4pt, Rightarrow, from=1, to=0]
\end{tikzcd}\]
~~~

<!--
```agda
  private
    module C  = Cat.Reasoning C
    module C′ = Cat.Reasoning C′
    module D  = Cat.Reasoning D
    module [C′,D] = Cat.Reasoning Cat[ C′ , D ]
    module [C,D] = Precategory Cat[ C , D ]
    module L₁ = Lan L₁
    module L₂ = Lan L₂
    cd-cat : is-category Cat[ C′ , D ]
    cd-cat = Functor-is-category dcat

  open _=>_
```
-->

The isomorphism $G \cong G'$ is constructed as follows: Since $G'$ is
equipped with $\eta'$, $G$ can produce $\sigma_{\eta'} : G \to G'$;
Since $G$ is equipped with $\eta$, $G'$ can produce $\sigma'_\eta : G'
\to G$. To show $\sigma_{\eta'}\sigma'_\eta : G' \to G'$ is the
identity, note that both make "everything in sight commute", so they
inhabit a contractible space since $G'$ is an extension. The argument
for $\sigma'_\eta\sigma_{\eta'}$ is analogous.

```agda
  Ext-unique : [C′,D].Isomorphism L₁.Ext L₂.Ext
  Ext-unique = [C′,D].make-iso (L₁.σ L₂.eta) (L₂.σ L₁.eta)
    ( sym (L₂.σ-uniq {α = L₂.eta}
        (Nat-path λ _ → sym ( D.pullr (ap (λ e → e .η _) L₂.σ-comm)
                            ∙ ap (λ e → e .η _) L₁.σ-comm)))
    ∙ L₂.σ-uniq (Nat-path λ _ → D.introl refl))
    ( sym (L₁.σ-uniq {α = L₁.eta}
        (Nat-path λ _ → sym ( D.pullr (ap (λ e → e .η _) L₁.σ-comm)
                            ∙ ap (λ e → e .η _) L₂.σ-comm)))
    ∙ L₁.σ-uniq (Nat-path λ _ → D.introl refl))

  Ext-uniqueₚ : L₁.Ext ≡ L₂.Ext
  Ext-uniqueₚ = cd-cat .to-path Ext-unique
```

The functor is not the only data associated with a left extension,
though: we must also verify that, under the identification $G \equiv G'$
we just produced, the natural transformations $\eta$ and $\eta'$ are
also identified. This boils down to verifying, in components, that
$\sigma_{\eta'}\eta = \eta'$, but that is immediate by the specification
for $\sigma$.

```agda
  eta-uniqueₚ : PathP (λ i → F => Ext-uniqueₚ i F∘ p) L₁.eta L₂.eta
  eta-uniqueₚ = Nat-pathp refl _ λ _ →
    Univalent.Hom-pathp-reflr-iso dcat (ap (λ e → e .η _) L₁.σ-comm)
```

<details>
<summary>A similar argument shows that $\sigma_j$ and $\sigma'_j$ are
also identified.</summary>
```agda
  σ-uniqueₚ : ∀ {M} (f : F => M F∘ p)
            → PathP (λ i → Ext-uniqueₚ i => M) (L₁.σ f) (L₂.σ f)
  σ-uniqueₚ {M = M} f = Nat-pathp _ _ λ _ →
    Univalent.Hom-pathp-refll-iso dcat lemma
    where
      σ′ : L₂.Ext => M
      σ′ .η x = L₁.σ f .η x D.∘ L₂.σ L₁.eta .η x
      σ′ .is-natural x y f = D.pullr (L₂.σ _ .is-natural _ _ _)
                          ∙ D.extendl (L₁.σ _ .is-natural _ _ _)

      lemma : ∀ {x} → L₁.σ f .η x D.∘ L₂.σ (L₁.eta) .η x ≡ L₂.σ f .η x
      lemma {x = x} = sym $ ap (λ e → e .η x) {y = σ′} $
        L₂.σ-uniq $ Nat-path λ _ →
          sym (D.pullr (ap (λ e → e .η _) L₂.σ-comm) ∙ ap (λ e → e .η _) L₁.σ-comm)
```
</details>

Now $(G, \eta, \sigma)$ _is_ all the data of a left extension: The other
two fields are propositions, and so they are automatically identified
--- regardless of the specific isomorphism we would have exhibited.

```agda
  open Lan

  Lan-unique : L₁ ≡ L₂
  Lan-unique i .Ext = cd-cat .to-path Ext-unique i
  Lan-unique i .eta = eta-uniqueₚ i
  Lan-unique i .σ f = σ-uniqueₚ f i
  Lan-unique i .σ-comm {α = α} =
    is-prop→pathp
      (λ i → [C,D].Hom-set _ _ ((σ-uniqueₚ α i ◂ p) ∘nt eta-uniqueₚ i) α)
      L₁.σ-comm L₂.σ-comm i
  Lan-unique i .σ-uniq {M = M} {α = α} {σ′ = σ′} =
    is-prop→pathp
      (λ i → Π-is-hlevel² {A = cd-cat .to-path Ext-unique i => M}
                          {B = λ σ′ → α ≡ (σ′ ◂ p) ∘nt eta-uniqueₚ i} 1
              λ σ′ x → [C′,D].Hom-set _ _ (σ-uniqueₚ α i) σ′)
      (λ σ′ → L₁.σ-uniq {σ′ = σ′})
      (λ σ′ → L₂.σ-uniq {σ′ = σ′})
      i σ′
```
