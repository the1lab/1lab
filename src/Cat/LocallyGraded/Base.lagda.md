---
description: |
  Locally graded categories.
---
<!--
```agda
open import Cat.Bi.Base
open import Cat.Prelude
```
-->
```agda
module Cat.LocallyGraded.Base where
```

<!--
```agda
private variable
  ob ℓb₁ ℓb₂ : Level
```
-->

# Locally graded categories {defines=locally-graded-category}

<!-- [TODO: Reed M, 08/08/2025] Define enriched categories/actegories -->

There is a striking similarity between [[displayed categories]], enriched categories,
and actegories. All three of these concepts take the basic algebra of a category and
replace the hom *sets* with some other notion of morphism graded by some base category
$B$, and then equip those morphisms with an action of $B$.

For a displayed category $\cE \liesover \cB$, our $\cB$-graded morphisms
are the displayed hom sets $\cE_{u}(X', Y')$ over indexed over a $u : \cB(X,Y)$.
The action of $\cB$ is a bit hard to see initially, but becomes painfully
clear once you've gotten your hands dirty: it is given by transport of hom families.

For an enriched category $\cC$, our $\cV$-graded morphisms are generalized
elements $\cV(\Gamma, \cC(X,Y))$ for $\Gamma : \cV$. Moreover, $\cV$ acts on
graded morphisms $\cV(\Gamma, \cC(X,Y))$ via precomposition with a morphism
$\cV(\Delta, \Gamma)$.

Finally, for an actegory $\cC$ equipped with an action $\oslash : \cV \times \cC \to \cC$,
the appropriate notion of $V$-graded morphism is a sort of sort of "$\cV$-generalized morphism"
$\cC(\Gamma \oslash X, Y)$ where $\Gamma : \cV$. The action of $\cV$ on these morphisms is given
by functoriality of $\oslash$ and precomposition.

**Locally graded categories** simultaneously generalize these three related notions
by combining the indexing of a displayed category with a sort of "directed transport"
operation that lets us move between indices. Explicitly, a locally graded category $\cE$
over a [[prebicategory]] $\cB$ consists of:

- A family of objects $\cC_0 : \cB_0 \to \ty$ indexed by the objects of $\cB$.
- A family of morphisms $\cC_1 : \cB_1(X,Y) \to \cC_0(X) \to \cC_0(Y) \to \set$ indexed
  by the 1-cells of $\cB$.
- Identity and composite morphisms indexed over the identity 1-cell and composites of 1-cells.
- An action $[-] : \cB_2(u,v) \to \cC_1(v,X',Y') \to \cC_1(u,X',Y')$ of 2-cells of $\cB$
  on morphisms of $\cC$.

```agda
module _ (B : Prebicategory ob ℓb₁ ℓb₂) where
  private module B = Prebicategory B

  record Locally-graded-precategory
    (oe ℓe : Level)
    : Type (ob ⊔ ℓb₁ ⊔ ℓb₂ ⊔ lsuc oe ⊔ lsuc ℓe) where
    no-eta-equality
    field
      Ob[_] : B.Ob → Type oe
      Hom[_] : ∀ {a b} → a B.↦ b → Ob[ a ] → Ob[ b ] → Type ℓe
      Hom[_]-set
        : ∀ {a b} (u : a B.↦ b) (a' : Ob[ a ]) (b' : Ob[ b ])
        → is-set (Hom[ u ] a' b')

      id' : ∀ {x x'} → Hom[ B.id {x} ] x' x'
      _∘'_
        : ∀ {x y z x' y' z'}
        → {u : y B.↦ z} {v : x B.↦ y}
        → Hom[ u ] y' z' → Hom[ v ] x' y'
        → Hom[ u B.⊗ v ] x' z'

      _[_]
        : ∀ {x y x' y'} {u v : x B.↦ y}
        → Hom[ v ] x' y' → u B.⇒ v → Hom[ u ] x' y'

    infixr 30 _∘'_
    infix 35 _[_]
```

We also require that composition is associative and unital once
suitably adjusted by an associator or unitor.

```agda
    field
      idl→
        : ∀ {x y x' y'} {u : x B.↦ y}
        → (f : Hom[ u ] x' y')
        → (id' ∘' f) [ B.λ→ u ] ≡ f
      idr→
        : ∀ {x y x' y'} {u : x B.↦ y}
        → (f : Hom[ u ] x' y')
        → (f ∘' id') [ B.ρ→ u ] ≡ f
      assoc←
        : ∀ {a b c d a' b' c' d'}
        → {u : c B.↦ d} {v : b B.↦ c} {w : a B.↦ b}
        → (f : Hom[ u ] c' d') (g : Hom[ v ] b' c') (h : Hom[ w ] a' b')
        → (f ∘' (g ∘' h)) [ B.α→ u v w ] ≡ (f ∘' g) ∘' h
```

Finally, we require that the action of 2-cells is functorial, and that
identities and composites are sufficiently natural.

```agda
      []-id
        : ∀ {x y x' y'} {u : x B.↦ y}
        → (f : Hom[ u ] x' y')
        →  f [ B.Hom.id ] ≡ f
      []-∘
        : ∀ {x y x' y'} {u v w : x B.↦ y}
        → (α : v B.⇒ w) (β : u B.⇒ v)
        → (f : Hom[ w ] x' y')
        → f [ α B.∘ β ] ≡ f [ α ] [ β ]
      []-id'
        : ∀ {x x'}
        → (α : B.id B.⇒ B.id)
        → id' {x} {x'} [ α ] ≡ id' {x} {x'}
      []-∘'
        : ∀ {x y z x' y' z'} {t u : y B.↦ z} {v w : x B.↦ y}
        → (α : t B.⇒ u) (β : v B.⇒ w)
        → (f : Hom[ u ] y' z') (g : Hom[ w ] x' y')
        → (f ∘' g) [ α B.◆ β ] ≡ f [ α ] ∘' g [ β ]
```
