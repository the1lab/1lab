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
isCategory : Type _
isCategory = ∀ A → isContr (Σ[ B ∈ _ ] A ≅ B)
```

This notion of univalent category corresponds to the usual notion ---
which is having the canonical map from paths to isomorphisms be an
equivalence --- by the following argument: Since the types `(Σ[ B ∈ _ ]
C [ A ≅ B ])` and `Σ[ B ∈ _ ] A ≣ B`, the action of `pathToIso`{.Agda}
on total spaces is an equivalence; Hence `pathToIso` is an equivalence.

```agda
pathToIso : ∀ {A B} → A ≡ B → A ≅ B
pathToIso {A = A} p = transport (λ i → A ≅ p i) idIso
```

First we define, exactly as in the book, the canonical map `pathToIso`{.Agda}.

```agda
isEquiv-pathToIso : isCategory → ∀ {A B} → isEquiv (pathToIso {A = A} {B = B})
isEquiv-pathToIso iscat {A} {B} = total→equiv isEquiv-total where
  P Q : Precategory.Ob C → Type _
  P B = A ≡ B
  Q B = A ≅ B
```

We consider the map `pathToIso`{.Agda} as a [fibrewise equivalence]
between the two families `A ≡ -` and `C [ A ≅ - ]`. This lets us reduce
the problem of proving that `pathToIso`{.Agda} is an equivalence to the
problem of proving that it induces an equivalence of total spaces.

[fibrewise equivalence]: agda://1Lab.Equiv.Fibrewise

```agda
  isEquiv-total : isEquiv (total {P = P} {Q = Q} (λ A p → pathToIso p))
  isEquiv-total =
    isContr→isEquiv (contr (A , λ i → A) isContr-Singleton)
                    (iscat _)
```

Since the total spaces are contractible (`Σ P` by `path induction`{.Agda
ident=J}, `Σ Q` by the assumption that C is a category) [any map between
them is an equivalence](agda://1Lab.Equiv#isContr→isEquiv). This implies
that we can turn categorical isomorphisms into paths of objects:

```agda
isoToPath : isCategory
          → ∀ {A B}
          → A ≅ B
          → A ≡ B
isoToPath cat =
  isEquiv→isIso (isEquiv-pathToIso cat) .isIso.inv
```

Furthermore, we have that this function is an equivalence, and so the
type of objects in a univalent category is at most a [groupoid]. We use
the fact that [h-levels are closed under equivalences] and that
[dependent sums preserve h-levels].

[h-levels are closed under equivalences]: agda://1Lab.HLevel.Retracts#isHLevel-equiv
[dependent sums preserve h-levels]: agda://1Lab.HLevel.Retracts#isHLevelΣ
[groupoid]: agda://1Lab.HLevel#isGroupoid

```agda
isGroupoid-Ob : isCategory → isGroupoid (C .Precategory.Ob)
isGroupoid-Ob iscat x y =
  isHLevel-equiv 2
    (isoToPath iscat)
    (((_ , isEquiv-pathToIso iscat) e⁻¹) .snd)
    isSet-≅
```

We can characterise transport in the Hom-sets of categories using the
`pathToIso`{.Agda} equivalence. Transporting in $\hom(p\ i, q\ i)$ is
equivalent to turning the paths into isomorphisms and
pre/post-composing:

```agda
Hom-transport : ∀ {A B C D} (p : A ≡ C) (q : B ≡ D) (h : Hom A B)
              → transport (λ i → Hom (p i) (q i)) h
              ≡ pathToIso q .to ∘ h ∘ pathToIso p .from
Hom-transport {A = A} {B} {D = D} =
  J (λ _ p → (q : B ≡ D) (h : Hom A B) →  transport (λ i → Hom (p i) (q i)) h
           ≡ pathToIso q .to ∘ h ∘ pathToIso p .from)
    (J (λ _ q → (h : Hom A B) → transport (λ i → Hom _ (q i)) h
              ≡ pathToIso q .to ∘ h ∘ pathToIso refl .from)
      λ h →
        transport refl h                          ≡⟨ transport-refl _ ⟩
        h                                         ≡⟨ solve C ⟩
        id ∘ h ∘ id                               ≡⟨ (λ i → transport-refl id (~ i) ∘ h ∘ transport-refl id (~ i)) ⟩
        transport refl id ∘ h ∘ transport refl id ∎)
```

This lets us quickly turn paths between compositions into dependent
paths in `Hom`{.Agda}-sets.

```agda
toHomPathP : ∀ {A B C D} {p : A ≡ C} {q : B ≡ D} {h : Hom A B} {h' : Hom C D}
           → pathToIso q .to ∘ h ∘ pathToIso p .from ≡ h'
           → PathP (λ i → Hom (p i) (q i)) h h'
toHomPathP {p = p} {q} {h} {h'} prf =
  toPathP _ _ _ (subst (_≡ h') (sym (Hom-transport p q h)) prf)
```
