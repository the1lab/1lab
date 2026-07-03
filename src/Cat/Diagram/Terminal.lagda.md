<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.Adjoint.Hom
open import Cat.Functor.Adjoint
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Terminal where
```

<!--
```agda
module _ {o h} (C : Precategory o h) where
  open Cat.Reasoning C
```
-->

# Terminal objects {defines="terminal-object terminal"}

An object $\top$ of a category $\mathcal{C}$ is said to be **terminal**
if it admits a _unique_ map from any other object:

```agda
  record is-terminal (t : Ob) : Type (o ⊔ h) where
    no-eta-equality
    field
      ! : ∀ {x} → Hom x t
      !-unique : ∀ {x} (h : Hom x t) → h ≡ !

    !-unique₂ : ∀ {x} (f g : Hom x t) → f ≡ g
    !-unique₂ f g = !-unique f ∙ sym (!-unique g)

  record Terminal : Type (o ⊔ h) where
    no-eta-equality
    field
      top : Ob
      has-is-term : is-terminal top

    open is-terminal has-is-term public
```

<!--
```agda
  {-# INLINE is-terminal.constructor #-}
  {-# INLINE Terminal.constructor #-}


module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C

  is-terminal-is-prop : ∀ {t} → is-prop (is-terminal C t)
  is-terminal-is-prop {t} t-term t-term' = path where
    open is-terminal

    !-path : ∀ {x} → t-term .! {x} ≡ t-term' .! {x}
    !-path = t-term' .!-unique (t-term .!)

    path : t-term ≡ t-term'
    path i .! = !-path i
    path i .!-unique h =
      is-prop→pathp (λ i → Hom-set _ _ h (!-path i))
        (t-term .!-unique h)
        (t-term' .!-unique h) i

  instance
    H-Level-is-terminal : ∀ {n} {t} → H-Level (is-terminal C t) (suc n)
    H-Level-is-terminal = prop-instance is-terminal-is-prop

  private unquoteDecl terminal-Σ-iso = declare-record-iso terminal-Σ-iso (quote Terminal)

  Terminal≃is-terminal
    : Terminal C ≃ (Σ[ apex ∈ Ob ] is-terminal C apex)
  Terminal≃is-terminal = Iso→Equiv terminal-Σ-iso

  -- Flattened record to make constructing terminal objects using
  -- 'record where' and 'record { Module }' easier.
  record make-terminal : Type (o ⊔ ℓ) where
    field
      top : Ob
      ! : ∀ {x} → Hom x top
      !-unique : ∀ {x} (h : Hom x top) → h ≡ !

  to-terminal : make-terminal → Terminal C
  {-# INLINE to-terminal #-}
  to-terminal mk = record
    { top = top
    ; has-is-term = record
      { ! = !
      ; !-unique = !-unique
      }
    }
    where open make-terminal mk

unquoteDecl Terminal-path = declare-record-path Terminal-path (quote Terminal)
```
-->

## Universal property

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C
  open Terminal
```
-->

If the type of morphisms into an object $t : \cC$ is [[contractible]],
then $t$ must be a terminal object.

```agda
  hom-contr→is-terminal
    : ∀ {t}
    → (∀ x → is-contr (Hom x t))
    → is-terminal C t
  {-# INLINE hom-contr→is-terminal #-}
  hom-contr→is-terminal hom-contr = record
    { ! = λ {x} → hom-contr x .centre
    ; !-unique = λ {x} h → sym (hom-contr x .paths h)
    }
```

We can further strengthen this implication to an if-and-only-if.

```agda
  is-terminal→hom-contr
    : ∀ {t}
    → is-terminal C t
    → (∀ x → is-contr (Hom x t))

  is-terminal-univ
    : ∀ {t}
    → is-terminal C t ≃ (∀ x → is-contr (Hom x t))
```

<details>
<summary>This holds essentially by definition, so we elide the details.
</summary>
```agda
  is-terminal→hom-contr term x = contr t.! λ h → sym (t.!-unique h) where
    module t = is-terminal term

  is-terminal-univ {t = t} = prop-ext! is-terminal→hom-contr hom-contr→is-terminal
```
</details>

We can also state this universal property in terms of [[equivalences]]:
an object $t$ is terminal if and only if the constant map $\cC(x, t) \to \top$
is an equivalence for every $x : \cC$.

```agda
  is-terminal≃comparison-equiv
    : ∀ {t}
    → is-terminal C t ≃ (∀ x → is-equiv λ (h : Hom x t) → tt)
  is-terminal≃comparison-equiv {t = t} =
    is-terminal C t                            ≃⟨ is-terminal-univ ⟩
    (∀ x → is-contr (Hom x t))                 ≃˘⟨ Π-ap-cod (λ x → Π-contr-eqv ⊤-is-contr ∙e is-hlevel-ap 0 (const-fibre-prop≃ (hlevel 1) tt tt)) ⟩
    (∀ x → ⊤ → is-contr (Hom x t × tt ≡ tt))   ≃˘⟨ Π-ap-cod (λ x → is-equiv≃fibre-is-contr) ⟩
    (∀ x → is-equiv (λ h → tt))                ≃∎
```

## Uniqueness

If a category has two terminal objects $t_1$ and $t_2$, then there is a
unique isomorphism $t_1 \cong t_2$. We first establish the isomorphism:
Since $t_1$ (resp. $t_2$) is terminal, there is a _unique_ map $!_1 : t_1 \to
t_2$ (resp. $!_2 : t_2 \to t_1$). To show these maps are inverses, we
must show that $!_1 \circ !_2$ is $\id$; But these morphisms
inhabit a contractible space, namely the space of maps into $t_2$, so
they are equal.

```agda
  module _ {t} (t-term : is-terminal C t) where
    private
      module t = is-terminal t-term

    !-invertible→is-terminal
      : ∀ {x} → is-invertible (t.! {x})
      → is-terminal C x
    {-# INLINE !-invertible→is-terminal #-}
    !-invertible→is-terminal !-inv = record
      { ! = λ {x} → !.inv ∘ t.!
      ; !-unique = λ h → post-invl.from !-inv (t.!-unique (t.! ∘ h))
      }
      where module ! = is-invertible (!-inv)

  !-invertible : (t1 t2 : Terminal C) → is-invertible (t1 .! {top t2})
  !-invertible t1 t2 = make-invertible (t2 .!) (!-unique₂ t1 _ _) (!-unique₂ t2 _ _)

  ⊤-unique : (t1 t2 : Terminal C) → top t1 ≅ top t2
  ⊤-unique t1 t2 = invertible→iso (t2 .!) (!-invertible t2 t1)
```

Hence, if $C$ is additionally a category, it has a propositional space of
terminal objects:

```agda
  ⊤-is-prop : is-category C → is-prop (Terminal C)
  ⊤-is-prop ccat x1 x2 = Terminal-path (ccat .to-path (⊤-unique x1 x2))

  is-terminal-iso : ∀ {A B} → A ≅ B → is-terminal C A → is-terminal C B
  is-terminal-iso {B = B} isom A-term = B-term where
    module isom = _≅_ isom
    module A = is-terminal A-term
    open is-terminal

    B-term : is-terminal C B
    B-term .! = isom.to ∘ A.!
    B-term .!-unique h = pre-invl.to (iso→invertible isom) (A.!-unique (isom.from ∘ h))
```

## In terms of right adjoints

We prove that the inclusion functor of an object $x$ of $\cC$ is right adjoint
to the unique functor $\cC \to \top$ if and only if $x$ is terminal.

```agda
  is-terminal→inclusion-is-right-adjoint
    : ∀ (x : Ob) → is-terminal C x
    → !F ⊣ !Const {C = C} x
  is-terminal→inclusion-is-right-adjoint x term =
    hom-iso→adjoints (e _ .fst) (e _ .snd)
      λ _ _ _ → is-terminal.!-unique₂ term _ _
    where
      e : ∀ y → ⊤ ≃ Hom y x
      e y = is-contr→≃ (hlevel 0) (is-terminal→hom-contr term y)

  inclusion-is-right-adjoint→is-terminal
    : ∀ (x : Ob) (adj : !F ⊣ !Const {C = C} x)
    → is-terminal C x
  {-# INLINE inclusion-is-right-adjoint→is-terminal #-}
  inclusion-is-right-adjoint→is-terminal x adj =
    hom-contr→is-terminal λ y →
    Equiv→is-hlevel 0
      (Σ-contr-snd (λ _ → hlevel 0) e⁻¹)
      (R-adjunct-is-equiv adj .is-eqv _)
```

<!--
```agda
module _ {o h} {C : Precategory o h} where
  open Cat.Reasoning C
  private unquoteDecl eqv = declare-record-iso eqv (quote Terminal)

  instance
    Extensional-Terminal
      : ∀ {ℓr}
      → ⦃ sa : Extensional Ob ℓr ⦄
      → Extensional (Terminal C) ℓr
    Extensional-Terminal ⦃ sa ⦄ =
      embedding→extensional
        (Iso→Embedding eqv ∙emb (fst , Subset-proj-embedding (λ _ → hlevel 1)))
        sa
```
-->
