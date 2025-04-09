<!--
```agda
open import 1Lab.Counterexamples.IsIso renaming (contra to ¬is-iso-is-prop)
open import 1Lab.Equiv.Biinv
open import 1Lab.Prelude
```
-->

```agda
module 1Lab.Counterexamples.Isovalence where
```

# The failure of "isovalence" {defines="isovalence"}

In HoTT, the [[univalence]] principle can be equivalently stated as
saying that the [[equivalences]] form an [[identity system]] on the
universe; in cubical type theory, this principle is a theorem. But in
most cases, we do *not* construct equivalences directly by hand, instead
factoring the construction through exhibiting a [[quasi-inverse]] to the
function at hand. Seeing this pattern everywhere, one must wonder: could
we not have that the *isomorphisms* are an identity system on the
universe?

This alternative principle is sometimes referred to as **isovalence**
for short, and this file will show that it is inconsistent. First, let's
make things clear: there is a natural choice of isomorphism $A \cong A$
for any type, given by the identity function, *where both homotopies are
the identity*.


```agda
id-iso : ∀ {ℓ} {A : Type ℓ} → Iso A A
id-iso = id , iso id (λ x → refl) (λ x → refl)
```

Quantifying over $A$, this is our only choice. But if we're looking at a
*specific* type $A$, like the [[circle]], there are [multiple ways] to
show that the identity map $\id : S^1 \to S^1$ is an isomorphism. This
fact will be crucial in the proof below.

[multiple ways]: 1Lab.Counterexamples.IsIso.html

We say that **isovalence holds** if the isomorphisms, equipped with the
natural choice of identity, form an identity system on every universe
$\type_j$.

```agda
Isovalence : Typeω
Isovalence = ∀ {ℓ} → is-identity-system {A = Type ℓ} Iso (λ a → id-iso)
```


```agda
module _ (isovalent : Isovalence) where
```

Assuming that isovalence *does* hold, we can equip the type of
isomorphisms with a [[path induction]]-like principle: Fixing a type
$A$, if we have a type family $P$ over $B$ and $f : A \cong B$, then we
can construct a section $P(B,f)$ by showing only $P(A,\id)$.

```agda
  IsoJ
    : ∀ {ℓ ℓ'} {A : Type ℓ} (P : (B : Type ℓ) (f : Iso A B) → Type ℓ')
    → P A id-iso
    → ∀ {B} (f : Iso A B) → P B f
  IsoJ = IdsJ isovalent
```

Keep in mind that the family $P$, being parametrised by an isomorphism
$f : A \cong B$, can make statements not only about the underlying map
$f : A \to B$, but *also* about the two-sided inverse with which $f$ was
equipped. In particular, we can formulate the statement "$\isiso(f)$ is
a *retract* of $\operatorname{is-biinv}(f)$", and conclude this about
*any* $f$ by showing it at the identity equivalence:

```agda
  is-iso-is-preserved
    : ∀ {ℓ} {A B : Type ℓ}
    → (f : A → B)
    → (p : is-iso f)
    → is-biinv→is-iso (is-iso→is-biinv p) ≡ p
  is-iso-is-preserved {A = A} f f-iso = IsoJ P at-id (f , f-iso) where
    P : (B : Type _) (f : Iso A B) → Type _
    P B (f , wit) = is-biinv→is-iso (is-iso→is-biinv wit) ≡ wit
```

Showing this at the identity isomorphism is simple, because Agda will
automatically chase it around the computation and tell us what we have
to show: for the precise implementation here, it boils down to showing
that four copies of the identity path are identical to a single copy:

```agda
    at-id : P A id-iso
    at-id = ap (iso id (λ x → refl)) $ funext λ x →
      refl ∙ refl ∙ refl ∙ refl ≡⟨ (∙-idl _ ∙∙ ∙-idl _ ∙∙ ∙-idl _) ⟩
      refl                      ∎
```

Finally, because $\operatorname{is-biinv}(f)$ is a proposition, under
the assumption of isovalence, we can show that $\isiso$ is a
proposition; since we already know this is false, we conclude that
isovalence *also* fails. This provides the motivation for seeking a more
coherent formulation of equivalence.

```agda
  is-iso-is-prop : ∀ {ℓ} {A B : Type ℓ} (f : A → B) → is-prop (is-iso f)
  is-iso-is-prop f = retract→is-prop
    is-biinv→is-iso is-iso→is-biinv (is-iso-is-preserved f) is-biinv-is-prop

  ¬isovalence : ⊥
  ¬isovalence = ¬is-iso-is-prop (is-iso-is-prop _)
```
