```
open import 1Lab.Prelude hiding (_∘_ ; id)

open import Cat.Solver
open import Cat.Base

module Cat.Univalent {o h} (C : Precategory o h) where

open import Cat.Morphism C
```

# (Univalent) Categories

In much the same way that a partial order is a preorder where $x \le y
\land y \le x \to x = y$, a **category** is a precategory where
isomorphic objects are identified. This is a generalisation of the
univalence axiom to arbitrary categories, and, indeed, it's phrased in
the same way: asking for a canonically defined map to be an equivalence.

A precategory is a category precisely when the type `(Σ[ B ∈ _ ] C [ A ≅
B ])` is contractible. This implies that the type `A ≡ B` is equivalent
to the type `C [ A ≃ B ]`, for any pair of objects `A`, `B` in the
category. This is because `Σ[ B ∈ _ ] (A ≡ _)` is also contractible.
Further, the type `C [ A ≃ B ]` satisfies J, by the same argument used
to construct `EquivJ`{.Agda}.

```agda
is-category : Type _
is-category = ∀ A → is-contr (Σ[ B ∈ _ ] A ≅ B)
```

This notion of univalent category corresponds to the usual notion ---
which is having the canonical map from paths to isomorphisms be an
equivalence --- by the following argument: Since the types `(Σ[ B ∈ _ ]
C [ A ≅ B ])` and `Σ[ B ∈ _ ] A ≣ B`, the action of `path→iso`{.Agda}
on total spaces is an equivalence; Hence `path→iso` is an equivalence.

```agda
path→iso : ∀ {A B} → A ≡ B → A ≅ B
path→iso {A = A} p = transport (λ i → A ≅ p i) id-iso
```

First we define, exactly as in the book, the canonical map `path→iso`{.Agda}.

```agda
path→iso-is-equiv : is-category → ∀ {A B} → is-equiv (path→iso {A = A} {B = B})
path→iso-is-equiv iscat {A} {B} = total→equiv is-equiv-total where
  P Q : Precategory.Ob C → Type _
  P B = A ≡ B
  Q B = A ≅ B
```

We consider the map `path→iso`{.Agda} as a [fibrewise equivalence]
between the two families `A ≡ -` and `C [ A ≅ - ]`. This lets us reduce
the problem of proving that `path→iso`{.Agda} is an equivalence to the
problem of proving that it induces an equivalence of total spaces.

[fibrewise equivalence]: agda://1Lab.Equiv.Fibrewise

```agda
  is-equiv-total : is-equiv (total {P = P} {Q = Q} (λ A p → path→iso p))
  is-equiv-total =
    is-contr→is-equiv (contr (A , λ i → A) Singleton-is-contr)
                      (iscat _)
```

Since the total spaces are contractible (`Σ P` by `path induction`{.Agda
ident=J}, `Σ Q` by the assumption that C is a category) [any map between
them is an equivalence](agda://1Lab.Equiv#is-contr→is-equiv). This implies
that we can turn categorical isomorphisms into paths of objects:

```agda
iso→path : is-category
          → ∀ {A B}
          → A ≅ B
          → A ≡ B
iso→path cat =
  is-equiv→is-iso (path→iso-is-equiv cat) .is-iso.inv
```

<!--
```agda
J-iso : ∀ {ℓ} → is-category
      → ∀ {A} (P : ∀ B → A ≅ B → Type ℓ)
      → P A id-iso
      → ∀ {B} (p : A ≅ B) → P B p
J-iso isc {A} P pid {B} p = 
  transport (λ i → P (q (B , p) i .fst) (q (B , p) i .snd)) pid
  where q = is-contr→is-prop (isc A) (A , id-iso)

iso→path-id : ∀ (isc : is-category) {A} → iso→path isc (id-iso {A}) ≡ refl
iso→path-id isc = 
  iso→path isc id-iso          ≡˘⟨ ap (iso→path isc) (≅-pathp refl refl (transport-refl _) (transport-refl _)) ⟩
  iso→path isc (path→iso refl) ≡⟨ equiv→retraction (path→iso-is-equiv isc) _ ⟩
  refl                         ∎
```
-->

Furthermore, we have that this function is an equivalence, and so the
type of objects in a univalent category is at most a [groupoid]. We use
the fact that [h-levels are closed under equivalences] and that
[dependent sums preserve h-levels].

[h-levels are closed under equivalences]: agda://1Lab.HLevel.Retracts#equiv→is-hlevel
[dependent sums preserve h-levels]: agda://1Lab.HLevel.Retracts#Σ-is-hlevel
[groupoid]: agda://1Lab.HLevel#is-groupoid

```agda
Ob-is-groupoid : is-category → is-groupoid (C .Precategory.Ob)
Ob-is-groupoid iscat x y =
  equiv→is-hlevel 2
    (iso→path iscat)
    (((_ , path→iso-is-equiv iscat) e⁻¹) .snd)
    ≅-is-set
```

We can characterise transport in the Hom-sets of categories using the
`path→iso`{.Agda} equivalence. Transporting in $\hom(p\ i, q\ i)$ is
equivalent to turning the paths into isomorphisms and
pre/post-composing:

```agda
Hom-transport : ∀ {A B C D} (p : A ≡ C) (q : B ≡ D) (h : Hom A B)
              → transport (λ i → Hom (p i) (q i)) h
              ≡ path→iso q .to ∘ h ∘ path→iso p .from
Hom-transport {A = A} {B} {D = D} =
  J (λ _ p → (q : B ≡ D) (h : Hom A B) →  transport (λ i → Hom (p i) (q i)) h
           ≡ path→iso q .to ∘ h ∘ path→iso p .from)
    (J (λ _ q → (h : Hom A B) → transport (λ i → Hom _ (q i)) h
              ≡ path→iso q .to ∘ h ∘ path→iso refl .from)
      λ h →
        transport refl h                          ≡⟨ transport-refl _ ⟩
        h                                         ≡⟨ solve C ⟩
        id ∘ h ∘ id                               ≡⟨ (λ i → transport-refl id (~ i) ∘ h ∘ transport-refl id (~ i)) ⟩
        transport refl id ∘ h ∘ transport refl id ∎)
```

This lets us quickly turn paths between compositions into dependent
paths in `Hom`{.Agda}-sets.

```agda
Hom-pathp : ∀ {A B C D} {p : A ≡ C} {q : B ≡ D} {h : Hom A B} {h' : Hom C D}
          → path→iso q .to ∘ h ∘ path→iso p .from ≡ h'
          → PathP (λ i → Hom (p i) (q i)) h h'
Hom-pathp {p = p} {q} {h} {h'} prf =
  to-pathp _ _ _ (subst (_≡ h') (sym (Hom-transport p q h)) prf)
```

<--
```agda
Hom-pathp-reflˡ : 
  ∀ {A B C} {p : A ≡ C} {h : Hom A B} {h' : Hom C B}
  → h ∘ path→iso p .from ≡ h'
  → PathP (λ i → Hom (p i) B) h h'
Hom-pathp-reflˡ prf = 
  Hom-pathp (ap₂ _∘_ (transport-refl id) refl ·· idl _ ·· prf)

Hom-pathp-reflˡ-iso : 
  ∀ {A B C} {p : A ≅ C} {h : Hom A B} {h' : Hom C B}
  → (isc : is-category)
  → h ∘ p .from ≡ h'
  → PathP (λ i → Hom (iso→path isc p i) B) h h'
Hom-pathp-reflˡ-iso isc prf = 
  Hom-pathp-reflˡ ( 
    ap₂ _∘_ refl (ap from (equiv→section (path→iso-is-equiv isc) _)) 
    ∙ prf)

Hom-pathp-reflʳ 
  : ∀ {A B D} {q : B ≡ D} {h : Hom A B} {h' : Hom A D}
  → path→iso q .to ∘ h ≡ h'
  → PathP (λ i → Hom A (q i)) h h'
Hom-pathp-reflʳ {q = q} prf = 
  Hom-pathp (ap (path→iso q .to ∘_) (ap₂ _∘_ refl (transport-refl _)) 
          ·· ap₂ _∘_ refl (idr _) 
          ·· prf)

Hom-pathp-reflʳ-iso
  : ∀ {A B D} {q : B ≅ D} {h : Hom A B} {h' : Hom A D}
  → (isc : is-category)
  → q .to ∘ h ≡ h'
  → PathP (λ i → Hom A (iso→path isc q i)) h h'
Hom-pathp-reflʳ-iso isc prf = 
  Hom-pathp-reflʳ (
    ap₂ _∘_ (ap to (equiv→section (path→iso-is-equiv isc) _)) refl 
    ∙ prf)
```
-->