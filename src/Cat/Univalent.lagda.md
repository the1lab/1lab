<!--
```
open import 1Lab.Prelude hiding (_∘_ ; id)

open import Cat.Morphism.Instances
open import Cat.Base

import Cat.Reasoning

open Cat.Reasoning using (Isomorphism ; id-iso)
open Precategory using (Ob)
```
-->

```agda
module Cat.Univalent where
```

# (Univalent) categories {defines="univalent-categories univalent-category"}

In much the same way that a [[partial order]] is a preorder where $x \le
y \land y \le x \to x = y$, a **category** is a precategory where
isomorphic objects are identified. This is a generalisation of the
[[univalence axiom]] to arbitrary categories, and, indeed, it's phrased
in the same way: asking for a canonically defined map to be an
equivalence.

We define a precategory to be univalent when it can be equipped when its
family of isomorphisms is an [[identity system]].

```agda
is-category : ∀ {o h} (C : Precategory o h) → Type (o ⊔ h)
is-category C = is-identity-system (Isomorphism C) (λ a → id-iso C)
```

This notion of univalent category corresponds to the usual notion ---
which is having the canonical map from paths to isomorphisms be an
equivalence --- by the following argument: Since the types `(Σ[ B ∈ _ ]
C [ A ≅ B ])` and `Σ[ B ∈ _ ] A ≣ B`, the action of `path→iso`{.Agda}
on total spaces is an equivalence; Hence `path→iso` is an equivalence.

```agda
path→iso
  : ∀ {o h} {C : Precategory o h} {A B}
  → A ≡ B → Isomorphism C A B
path→iso {C = C} {A} p = transport (λ i → Isomorphism C A (p i)) (id-iso C)

module Univalent' {o h} {C : Precategory o h} (r : is-category C) where
  module path→iso = Ids r
    renaming ( to            to iso→path
             ; J             to J-iso
             ; to-refl       to iso→path-id
             ; η             to iso→path→iso
             ; ε             to path→iso→path
             )

  open Cat.Reasoning C hiding (id-iso) public

  open path→iso
    using ( iso→path ; J-iso ; iso→path-id ; iso→path→iso ; path→iso→path )
    public
```

Furthermore, since the h-level of the relation behind an identity system
determines the h-level of the type it applies to, we have that the space
of objects in any univalent category is a groupoid:

```agda
  Ob-is-groupoid : is-groupoid ⌞ C ⌟
  Ob-is-groupoid = path→iso.hlevel 2 λ _ _ → hlevel 2
```

:::{.definition #transport-in-hom}
We can characterise transport in the Hom-sets of categories using the
`path→iso`{.Agda} equivalence. Transporting in $\hom(p\ i, q\ i)$ is
equivalent to turning the paths into isomorphisms and
pre/post-composing:
:::

```agda
module _ {o h} (C : Precategory o h) where
  open Cat.Reasoning C hiding (id-iso ; Isomorphism)
  Hom-transport : ∀ {A B C D} (p : A ≡ C) (q : B ≡ D) (h : Hom A B)
                → transport (λ i → Hom (p i) (q i)) h
                ≡ path→iso q .to ∘ h ∘ path→iso p .from
  Hom-transport {A = A} {B} {D = D} p q h i =
    comp (λ j → Hom (p (i ∨ j)) (q (i ∨ j))) (∂ i) λ where
      j (i = i0) → coe0→i (λ k → Hom (p (j ∧ k)) (q (j ∧ k))) j h
      j (i = i1) → path→iso q .to ∘ h ∘ path→iso p .from
      j (j = i0) → hcomp (∂ i) λ where
        j (i = i0) → idl (idr h j) j
        j (i = i1) → q' i1 ∘ h ∘ p' i1
        j (j = i0) → q' i ∘ h ∘ p' i
    where
      p' : PathP _ id (path→iso p .from)
      p' i = coe0→i (λ j → Hom (p (i ∧ j)) A) i id

      q' : PathP _ id (path→iso q .to)
      q' i = coe0→i (λ j → Hom B (q (i ∧ j))) i id
```

This lets us quickly turn paths between compositions into dependent
paths in `Hom`{.Agda}-sets.

```agda
  Hom-pathp : ∀ {A B C D} {p : A ≡ C} {q : B ≡ D} {h : Hom A B} {h' : Hom C D}
            → path→iso q .to ∘ h ∘ path→iso p .from ≡ h'
            → PathP (λ i → Hom (p i) (q i)) h h'
  Hom-pathp {p = p} {q} {h} {h'} prf =
    to-pathp (subst (_≡ h') (sym (Hom-transport p q h)) prf)
```

<!--
```agda
  Hom-transport-id
    : ∀ {A C D} (p : A ≡ C) (q : A ≡ D)
    → transport (λ i → Hom (p i) (q i)) id ≡ path→iso q .to ∘ path→iso p .from
  Hom-transport-id p q = Hom-transport p q _ ∙ ap (path→iso q .to ∘_) (idl _)

  Hom-transport-refll-id
    : ∀ {A B} (q : A ≡ B)
    → transport (λ i → Hom A (q i)) id ≡ path→iso q .to
  Hom-transport-refll-id p = Hom-transport-id refl p ∙ elimr (transport-refl _)

  Hom-transport-reflr-id
    : ∀ {A B} (q : A ≡ B)
    → transport (λ i → Hom (q i) A) id ≡ path→iso q .from
  Hom-transport-reflr-id p = Hom-transport-id p refl ∙ eliml (transport-refl _)

  Hom-pathp-refll :
    ∀ {A B C} {p : A ≡ C} {h : Hom A B} {h' : Hom C B}
    → h ∘ path→iso p .from ≡ h'
    → PathP (λ i → Hom (p i) B) h h'
  Hom-pathp-refll prf =
    Hom-pathp (ap₂ _∘_ (transport-refl id) refl ·· idl _ ·· prf)

  Hom-pathp-reflr
    : ∀ {A B D} {q : B ≡ D} {h : Hom A B} {h' : Hom A D}
    → path→iso q .to ∘ h ≡ h'
    → PathP (λ i → Hom A (q i)) h h'
  Hom-pathp-reflr {q = q} prf =
    Hom-pathp (ap (path→iso q .to ∘_) (ap₂ _∘_ refl (transport-refl _))
            ·· ap₂ _∘_ refl (idr _)
            ·· prf)

  Hom-pathp-id
    : ∀ {A B C} {p : B ≡ A} {q : B ≡ C} {h' : Hom A C}
    → PathP (λ i → Hom (p i) (q i)) (id {B}) h'
    → path→iso q .to ∘ path→iso p .from ≡ h'
  Hom-pathp-id {p = p} {q} {h} prf =
    J' (λ B A p → ∀ {C} (q : B ≡ C) {h' : Hom A C}
                → PathP (λ i → Hom (p i) (q i)) (id {B}) h'
                → path→iso q .to ∘ path→iso p .from ≡ h')
      (λ x q prf → ap₂ _∘_ refl (transport-refl _) ·· idr _ ·· from-pathp prf)
      p q prf

  path→to-∙
    : ∀ {A B C} (p : A ≡ B) (q : B ≡ C)
    → path→iso (p ∙ q) .to ≡ path→iso q .to ∘ path→iso p .to
  path→to-∙ {A = A} p q =
    J (λ B p → ∀ {C} (q : B ≡ C) → path→iso (p ∙ q) .to ≡ path→iso q .to ∘ path→iso p .to)
      (λ q → subst-∙ (λ e → Hom A e) refl q _
          ∙ ap (subst (λ e → Hom A e) q) (transport-refl id)
          ∙ sym (idr _) ∙ ap₂ _∘_ refl (sym (transport-refl id))
      )
      p q

  path→from-∙
    : ∀ {A B C} (p : A ≡ B) (q : B ≡ C)
    → path→iso (p ∙ q) .from ≡ path→iso p .from ∘ path→iso q .from
  path→from-∙ {A = A} p q =
    J (λ B p → ∀ {C} (q : B ≡ C) → path→iso (p ∙ q) .from ≡ path→iso p .from ∘ path→iso q .from)
      (λ q → subst-∙ (λ e → Hom e _) refl q _
          ·· ap (subst (λ e → Hom e _) q) (transport-refl id)
          ·· sym (idl _) ∙ ap₂ _∘_ (sym (transport-refl id)) refl
      )
      p q

  path→iso-∙
    : ∀ {A B C} (p : A ≡ B) (q : B ≡ C)
    → path→iso (p ∙ q) ≡ path→iso p ∘Iso path→iso q
  path→iso-∙ p q = ext (path→to-∙ p q)

  path→to-sym : ∀ {A B} (p : A ≡ B) → path→iso p .from ≡ path→iso (sym p) .to
  path→to-sym = J (λ B p → path→iso p .from ≡ path→iso (sym p) .to) refl

  from-pathp-to
    : ∀ {A B C} (p : A ≡ B) {f g}
    → PathP (λ i → Hom C (p i)) f g
    → path→iso p .to ∘ f ≡ g
  from-pathp-to {C = C} p q =
    J (λ B p → ∀ {f g} → PathP (λ i → Hom C (p i)) f g
             → path→iso p .to ∘ f ≡ g)
      (λ q → eliml (transport-refl _) ∙ q) p q

  from-pathp-from
    : ∀ {A B C} (p : A ≡ B) {f g}
    → PathP (λ i → Hom C (p i)) f g
    → path→iso (sym p) .from ∘ f ≡ g
  from-pathp-from {C = C} p q = ap₂ _∘_ (path→to-sym (sym p)) refl
                              ∙ from-pathp-to p q

module Univalent {o h} {C : Precategory o h} (r : is-category C) where
  open Univalent' r public

  Hom-pathp-refll-iso :
    ∀ {A B C} {p : A ≅ C} {h : Hom A B} {h' : Hom C B}
    → h ∘ p .from ≡ h'
    → PathP (λ i → Hom (iso→path p i) B) h h'
  Hom-pathp-refll-iso prf =
    Hom-pathp-refll C (ap₂ _∘_ refl (ap from (iso→path→iso _)) ∙ prf)

  Hom-pathp-reflr-iso
    : ∀ {A B D} {q : B ≅ D} {h : Hom A B} {h' : Hom A D}
    → q .to ∘ h ≡ h'
    → PathP (λ i → Hom A (iso→path q i)) h h'
  Hom-pathp-reflr-iso prf =
    Hom-pathp-reflr C (ap₂ _∘_ (ap to (iso→path→iso _)) refl ∙ prf)

  Hom-pathp-iso
    : ∀ {A B C D} {p : A ≅ C} {q : B ≅ D} {h : Hom A B} {h' : Hom C D}
    → q .to ∘ h ∘ p .from ≡ h'
    → PathP (λ i → Hom (iso→path p i) (iso→path q i)) h h'
  Hom-pathp-iso {p = p} {q} {h} {h'} prf =
    Hom-pathp C (ap₂ _∘_ (ap to (iso→path→iso _))
                  (ap₂ _∘_ refl (ap from (iso→path→iso _)))
              ∙ prf)
```
-->
