```agda
open import Cat.Instances.StrictCat
open import Cat.Instances.Discrete hiding (Disc)
open import Cat.Instances.Functor
open import Cat.Functor.Adjoint
open import Cat.Univalent
open import Cat.Prelude

module Cat.Instances.StrictCat.Cohesive where
```

<!--
```agda
private variable
  ℓ o h : Level

open Precategory
open Functor
open _=>_
open _⊣_
```
-->

# StrictCat is "cohesive"

We prove that the category $\cat_{\mathrm{strict}}$ admits an adjoint
quadruple

$$
\Pi_0 \dashv \mathrm{Disc} \dashv \Gamma \dashv \mathrm{Codisc} 
$$

where the "central" adjoint $\Gamma$ is the functor which sends a strict
category to its underlying set of objects. This lets us treat categories
as giving a kind of "spatial" structure over $\mathrm{Sets}$.  The left-
and right- adjoints to $\mathrm{Ob}$ equip sets with the "discrete" and
"codiscrete" spatial structures, where nothing is stuck together, or
everything is stuck together.

The extra right adjoint to $\mathrm{Ob}$ assigns a category to its set
of connected components, which can be thought of as the "pieces" of the
category. Two objects land in the same connected component if there is a
path of morphisms connecting them, hence the name.

**Note**: Generally, the term "cohesive" is applied to Grothendieck
topoi, which `StrictCat`{.Agda} is _very far_ from being. We're using it
here by analogy: There's an adjoint quadruple, where the functor
$\Gamma$ sends each category to its set of points: see [the last
section]. Strictly speaking, the left adjoint to $\Gamma$ isn't defined
by tensoring with `Sets`{.Agda}, but it _does_ have the effect of
sending $S$ to the coproduct of $S$-many copies of the point category.

[the last section]: #object-set-vs-global-sections

# Disc ⊣ Γ

We begin by defining the object set functor.

```agda
Γ : Functor (StrictCat o h) (Sets o)
Γ .F₀ (C , obset) = Ob C , obset
Γ .F₁ = F₀
Γ .F-id = refl
Γ .F-∘ _ _ = refl
```

We must then prove that the assignment `Disc′`{.Agda} extends to a
functor from `Sets`{.Agda}, and prove that it's left adjoint to the
functor `Γ`{.Agda} we defined above. Then we define the adjunction
`Disc⊣Γ`{.Agda}.

```agda
Disc : Functor (Sets ℓ) (StrictCat ℓ ℓ)
Disc .F₀ S = Disc′ S , S .snd
Disc .F₁ = liftDisc
Disc .F-id = Functor≡ (λ x → refl) λ f → refl
Disc .F-∘ _ _ = Functor≡ (λ x → refl) λ f → refl

Disc⊣Γ : Disc {ℓ} ⊣ Γ
Disc⊣Γ = adj where
```

<!--
```agda
  abstract
    lemma : ∀ {A : StrictCat ℓ ℓ .Precategory.Ob} 
              {x y z : A .fst .Precategory.Ob} (f : y ≡ z) (g : x ≡ y)
          → subst (A .fst .Precategory.Hom _) (g ∙ f) (A .fst .Precategory.id)
          ≡ A .fst .Precategory._∘_ 
            (subst (A .fst .Precategory.Hom _) f (A .fst .Precategory.id))
            (subst (A .fst .Precategory.Hom _) g (A .fst .Precategory.id))
    lemma {A = A} {x = x} = 
      J′ (λ y z f → (g : x ≡ y) → subst (X.Hom _) (g ∙ f) X.id 
                  ≡ subst (X.Hom _) f X.id X.∘ subst (X.Hom _) g X.id) 
        λ x g → (subst-∙ (X.Hom _) g refl _ ·· transport-refl _ ·· sym (X.idl _))
              ∙ ap₂ X._∘_ (sym (transport-refl _)) refl
      where module X = Precategory (A .fst)
```
-->

For the adjunction `unit`{.Agda}, we're asked to provide a natural
transformation from the identity functor to $\Gamma \circ
\mathrm{Disc}$; Since the object set of $\mathrm{Disc}(X)$ is simply
$X$, the identity map suffices:

```agda
  adj : _ ⊣ _
  adj .unit   = NT (λ _ x → x) λ x y f i o → f o
```

The adjunction counit is slightly more complicated, as we have to give a
functor $\mathrm{Disc}(\Gamma(X)) \to X$, naturally in $X$. Since
morphisms in discrete categories are paths, for a map $x \equiv y$ (in
`{- 1 -}`{.Agda}), it suffices to assume $y$ really is $x$, and so the
identity map suffices.

```agda
  adj .counit = NT (λ x → F x) nat where
    F : (x : Precategory.Ob (StrictCat ℓ ℓ)) 
      → Functor (Disc′ (x .fst .Precategory.Ob , x .snd)) _
    F X .F₀ x = x
    F X .F₁ p = subst (X .fst .Hom _) p (X .fst .id) {- 1 -}
    F X .F-id = transport-refl _
    F X .F-∘ = lemma {A = X}
```

<!--
```agda
    abstract
      nat : (x y : Precategory.Ob (StrictCat ℓ ℓ)) 
            (f : Precategory.Hom (StrictCat ℓ ℓ) x y)
          → (F y F∘ F₁ (Disc F∘ Γ) f) ≡ (f F∘ F x)
      nat x y f = 
        Functor≡ (λ x → refl) 
           (J′ (λ x y p → subst (Y.Hom _) (ap (F₀ f) p) Y.id 
                        ≡ F₁ f (subst (X.Hom _) p X.id)) 
               λ _ → transport-refl _ 
                  ·· sym (F-id f) 
                  ·· ap (F₁ f) (sym (transport-refl _)))
         where
           module X = Precategory (x .fst)
           module Y = Precategory (y .fst)
```
-->

Fortunately the triangle identities are straightforwardly checked.

```agda
  adj .zig {x} = Functor≡ (λ x i → x) λ f → x .snd _ _ _ _
  adj .zag = refl
```

# Γ ⊣ Codisc

The _codiscrete_ category on a set $X$ is the strict category with
object space $X$, and _all_ hom-spaces contractible. The assignment of
codiscrete categories extends to a functor $\sets \to
\cat_{\mathrm{strict}}$, where we lift functions to act on object parts
and the action on morphisms is trivial.

```agda
Codisc : Functor (Sets ℓ) (StrictCat ℓ ℓ)
Codisc .F₀ (S , sset) = Codisc′ S , sset

Codisc .F₁ f .F₀ = f
Codisc .F₁ f .F₁ = λ _ → lift tt
Codisc .F₁ f .F-id = refl
Codisc .F₁ f .F-∘ = λ _ _ → refl

Codisc .F-id    = Functor≡ (λ x → refl) λ f → refl
Codisc .F-∘ _ _ = Functor≡ (λ x → refl) λ f → refl
```

The codiscrete category functor is right adjoint to the object set
functor $\Gamma$. The construction of the adjunction is now simple in
both directions:

```agda
Γ⊣Codisc : Γ ⊣ Codisc {ℓ}
Γ⊣Codisc = adj where
  adj : _ ⊣ _
  adj .unit = 
    NT (λ x → record { F₀ = λ x → x ; F₁ = λ _ → lift tt 
                     ; F-id = refl ; F-∘ = λ _ _ → refl }) 
       λ x y f → Functor≡ (λ _ → refl) λ _ → refl
  adj .counit = NT (λ _ x → x) λ x y f i o → f o
  adj .zig = refl
  adj .zag = Functor≡ (λ _ → refl) λ _ → refl
```

## Object set vs global sections

Above, we defined the functor $\Gamma$ by directly projecting the
underlying set of each category. Normally in the definition of a
cohesion structure, we use the _global sections_ functor which maps
$x \mapsto \hom(*,x)$ (where $*$ is the terminal object). Here we prove
that these functors are naturally isomorphic, so our abbreviation above
is harmless.

Below, we represent the terminal category $*$ as the codiscrete category
on the terminal set. Using the codiscrete category here is equivalent to
using the discrete category, but it is more convenient since the
$\hom$-sets are definitionally contractible.

```agda
module _ {ℓ} where
  import Cat.Morphism Cat[ StrictCat ℓ ℓ , Sets ℓ ] as Nt

  GlobalSections : Functor (StrictCat ℓ ℓ) (Sets ℓ)
  GlobalSections .F₀ C = 
    Functor (Codisc′ (Lift _ ⊤)) (C .fst) , isSet-Functor (C .snd)
  GlobalSections .F₁ G F = G F∘ F
  GlobalSections .F-id = funext λ _ → Functor≡ (λ _ → refl) λ _ → refl
  GlobalSections .F-∘ f g = funext λ _ → Functor≡ (λ _ → refl) λ _ → refl
```

Since `GlobalSections`{.Agda} is a section of the $\hom$ functor, it
acts on maps by composition. The functor identities hold definitionally.

```agda
  GlobalSections≅Γ : Γ {ℓ} Nt.≅ GlobalSections
  GlobalSections≅Γ = Nt.makeIso f g f∘g g∘f where
    open Precategory
```

We define a natural isomorphism from `Γ`{.Agda} to the
`GlobalSections`{.Agda} functor by sending each object to the constant
functor on that object. This assignment is natural because it is
essentially independent of the coordinate.

```agda
    f : Γ => GlobalSections
    f .η x ob = 
      record { F₀ = λ _ → ob ; F₁ = λ _ → x .fst .id 
             ; F-id = refl ; F-∘ = λ _ _ → sym (x .fst .idl _) 
             }
    f .is-natural x y f = funext λ _ → Functor≡ (λ _ → refl) λ _ → sym (F-id f)
```

In the opposite direction, the natural transformation is defined by
evaluating at the point. These natural transformations compose to the
identity almost definitionally, but Agda does need some convincing,
using our path helpers: `Nat-path`{.Agda}, `funext`{.Agda}, and
`Functor≡`{.Agda}.

```agda
    g : GlobalSections => Γ
    g .η x f = F₀ f (lift tt)
    g .is-natural x y f = refl

    f∘g : f ∘nt g ≡ idnt
    f∘g = Nat-path λ c → funext λ x → Functor≡ (λ x → refl) λ f → sym (F-id x)

    g∘f : g ∘nt f ≡ idnt
    g∘f = Nat-path λ _ i x → x
```
