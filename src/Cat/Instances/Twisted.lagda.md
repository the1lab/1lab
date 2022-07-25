```agda
open import Cat.Instances.Product
open import Cat.Prelude

module Cat.Instances.Twisted where
```

# Twisted arrow categories

The category of arrows of $\ca{C}$ is the category $\id{Arr}(\ca{C})$
which has objects given by morphisms $a_0 \xto{a} a_1 : \ca{C}$^[We will
metonymically refer to the triple $(a_0,a_1,a)$ using simply $a$.], and
morphisms $f : a \to b$ given by pairs $f_0, f_1$ as indicated making
the diagram below commute.

~~~{.quiver}
\[\begin{tikzcd}
  {a_0} && {b_0} \\
  \\
  {a_1} && {b_1}
  \arrow["a"', from=1-1, to=3-1]
  \arrow["b", from=1-3, to=3-3]
  \arrow["{f_0}", from=1-1, to=1-3]
  \arrow["{f_1}"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

Now, add a twist. Literally! Invert the direction of the morphism $f_0$
in the definition above. The resulting category is the **twisted arrow
category** of $\ca{C}$, written $\id{Tw}(\ca{C})$. You can think of a
morphism $f \to g$ in $\id{Tw}(\ca{C})$ as a factorisation of $g$
through $f$.

```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Precategory C
  record Twist {a₀ a₁ b₀ b₁} (f : Hom a₀ a₁) (g : Hom b₀ b₁) : Type ℓ where
    no-eta-equality
    field
      before : Hom b₀ a₀
      after  : Hom a₁ b₁
      commutes : after ∘ f ∘ before ≡ g
```

<!--
```agda
  Twist-path
    : ∀ {a₀ a₁ b₀ b₁} {f : Hom a₀ a₁} {g : Hom b₀ b₁} {h1 h2 : Twist f g}
    → Twist.before h1 ≡ Twist.before h2
    → Twist.after h1 ≡ Twist.after h2
    → h1 ≡ h2
  Twist-path {h1 = h1} {h2} p q i .Twist.before = p i
  Twist-path {h1 = h1} {h2} p q i .Twist.after = q i
  Twist-path {h1 = h1} {h2} p q i .Twist.commutes =
    is-prop→pathp (λ i → Hom-set _ _ (q i ∘ _ ∘ p i) _)
      (h1 .Twist.commutes) (h2 .Twist.commutes) i

  open Functor

  private unquoteDecl eqv = declare-record-iso eqv (quote Twist)
```
-->

```agda
  Twisted : Precategory (o ⊔ ℓ) ℓ
  Twisted .Precategory.Ob = Σ[ (a , b) ∈ Ob × Ob ] Hom a b
  Twisted .Precategory.Hom (_ , f) (_ , g) = Twist f g
  Twisted .Precategory.Hom-set (_ , f) (_ , g) =
    is-hlevel≃ 2 (Iso→Equiv eqv e⁻¹) (hlevel 2)
  Twisted .Precategory.id = record
    { before   = id ; after    = id ; commutes = idl _ ∙ idr _ }
  Twisted .Precategory._∘_ t1 t2 .Twist.before = t2 .Twist.before ∘ t1 .Twist.before
  Twisted .Precategory._∘_ t1 t2 .Twist.after   = t1 .Twist.after ∘ t2 .Twist.after
```

<!--
```agda
  Twisted .Precategory._∘_ {_ , f} {_ , g} {_ , h} t1 t2 .Twist.commutes =
    (t1.a ∘ t2.a) ∘ f ∘ t2.b ∘ t1.b ≡⟨ solve! C ⟩
    t1.a ∘ (t2.a ∘ f ∘ t2.b) ∘ t1.b ≡⟨ (λ i → t1.a ∘ t2.commutes i ∘ t1.b) ⟩
    t1.a ∘ g ∘ t1.b                 ≡⟨ t1.commutes ⟩
    h                               ∎
    where
      module t1 = Twist t1 renaming (after to a ; before to b)
      module t2 = Twist t2 renaming (after to a ; before to b)
  Twisted .Precategory.idr f = Twist-path (idl _) (idr _)
  Twisted .Precategory.idl f = Twist-path (idr _) (idl _)
  Twisted .Precategory.assoc f g h = Twist-path (sym (assoc _ _ _)) (assoc _ _ _)
```
-->

The twisted arrow category admits a forgetful functor $\id{Tw}(\ca{C})
\to \ca{C}\op \times \ca{C}$, which sends each arrow $a \xto{f} b$ to
the pair $(a, b)$, and forgets the commutativity datum for the diagram.
Since commutativity of diagrams is a property (rather than structure),
this inclusion functor is faithful, though it is not full.

```agda
  πₜ : Functor Twisted (C ^op ×ᶜ C)
  πₜ .F₀ = fst
  πₜ .F₁ f = Twist.before f , Twist.after f
  πₜ .F-id = refl
  πₜ .F-∘ f g = refl

module _ {o ℓ o′ ℓ′} {C : Precategory o ℓ} {D : Precategory o′ ℓ′} where
  twistᵒᵖ : Functor (C ^op ×ᶜ C) D → Functor (Twisted {C = C ^op} ^op) D
  twistᵒᵖ F .Functor.F₀ ((a , b) , _) = F .Functor.F₀ (a , b)
  twistᵒᵖ F .Functor.F₁ arr = F .Functor.F₁ (Twist.before arr , Twist.after arr)
  twistᵒᵖ F .Functor.F-id = F .Functor.F-id
  twistᵒᵖ F .Functor.F-∘ f g = F .Functor.F-∘ _ _
```
